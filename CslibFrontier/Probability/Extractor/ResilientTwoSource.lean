/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Extractor.TwoSource
public import CslibFrontier.Probability.Resilience.NOBF
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Foundations.BooleanAnalysis.Fourier
import CslibFrontier.Foundations.Data.BitString.Sign
import CslibFrontier.Probability.Conditioning
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.Product
import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Probability.StatisticalDistance.Event

/-!
# The Chattopadhyay–Zuckerman reduction from resilient functions to two-source extractors

Combining a strong seeded condenser `cond : Y → Fin D → Seed₂` (having at most `q_bad` bad seeds
outside which the condensed distribution has min-entropy deficiency at most `Δ`), an advice
`t`-non-malleable extractor `nmExt : X → Seed₂ → Fin D → Bool`, and a `(t + 1)`-independent
`(q_bad, ε_res)`-resilient Boolean function `f : BitString D → Bool` with `(t + 1)`-independent
bias at most `ε_bias` yields a two-source extractor `fun x y => f fun i => nmExt x (cond y i) i`
[Chattopadhyay–Zuckerman][ChattopadhyayZuckerman2019].

This is the conditional reduction endpoint of the Chattopadhyay–Zuckerman framework: instantiating
it unconditionally for polylogarithmic min-entropy requires explicit non-malleable extractors and
optimal depth-`4` resilient functions, which are not constructed here. Both condenser-based and
strong-extractor specializations are included below.

## Main definitions

* `Cslib.Probability.IsAdviceNonMalleableExtractor`: `t`-non-malleable extractors with advice.

## Main results

* `Cslib.Probability.isAdviceNonMalleableExtractor_zero_iff`: at `t = 0`, advice non-malleable
  extractors coincide with families of strong seeded extractors.
* `Cslib.Probability.exists_badSet_isSource_of_isStrongExtractor`: Markov bound extracting a
  small bad seed set outside which a strong extractor produces near-uniform outputs on a source.
* `Cslib.Probability.isKWiseSmallBias_map_restrict_of_condenser`: conditioned on the good seeds,
  the induced bit string `(nmExt x (cond y i) i)_i` is `(t + 1)`-wise
  `(2 * γ + 2 ^ (Δ + 1) * ε_nm)`-biased.
* `Cslib.Probability.isTwoSourceExtractor_of_resilient_condenser`,
  `Cslib.Probability.isTwoSourceExtractor_of_resilient_strongExtractor`: the Chattopadhyay–Zuckerman
  two-source extractor reductions.

## References

* [E. Chattopadhyay, D. Zuckerman, *Explicit two-source extractors and resilient
  functions*][ChattopadhyayZuckerman2019]
-/

public section

namespace Cslib.Probability

open Finset Cslib.Probability.PMF Cslib.BitString
open scoped BigOperators NNReal

/-! ### Advice `t`-non-malleable extractors -/

/-- A **`(t, k, ε)`-non-malleable extractor with advice**: for every source of min-entropy at
least `k`, every target advice `a₀`, and at most `t` deterministic tampering functions
`f j : Seed → Seed × Adv` never equal to `(r, a₀)`, the output `nmExt x r a₀` stays `ε`-close to
uniform even given `r` and all tampered outputs `nmExt x (f j r).1 (f j r).2`. -/
def IsAdviceNonMalleableExtractor {X Seed Adv : Type*} [Fintype Seed] [Nonempty Seed]
    (nmExt : X → Seed → Adv → Bool) (t : ℕ) (k ε : ℝ) : Prop :=
  ∀ source : PMF X, k ≤ minEntropy source →
    ∀ (a₀ : Adv) (m : ℕ), m ≤ t →
      ∀ f : Fin m → Seed → Seed × Adv, (∀ j r, f j r ≠ (r, a₀)) →
        dist
          (source.bind fun x => (PMF.uniformOfFintype Seed).map fun r =>
            (r, nmExt x r a₀, fun j => nmExt x (f j r).1 (f j r).2))
          (source.bind fun x => (PMF.uniformOfFintype Seed).bind fun r =>
            (PMF.uniformOfFintype Bool).map fun b =>
              (r, b, fun j => nmExt x (f j r).1 (f j r).2)) ≤ ε

/-- Advice non-malleable extractors remain valid for smaller `t`, larger min-entropy `k`, and
larger error `ε`. -/
theorem IsAdviceNonMalleableExtractor.mono {X Seed Adv : Type*} [Fintype Seed] [Nonempty Seed]
    {nmExt : X → Seed → Adv → Bool} {t t' : ℕ} {k k' ε ε' : ℝ}
    (h : IsAdviceNonMalleableExtractor nmExt t k ε) (ht : t' ≤ t) (hk : k ≤ k') (hε : ε ≤ ε') :
    IsAdviceNonMalleableExtractor nmExt t' k' ε' :=
  fun source hsource a₀ m hm f hf =>
    (h source (hk.trans hsource) a₀ m (hm.trans ht) f hf).trans hε

/-- At `t = 0`, an advice non-malleable extractor is equivalently a strong seeded extractor for
every fixed advice `a₀`. -/
theorem isAdviceNonMalleableExtractor_zero_iff {X Seed Adv : Type*} [Fintype Seed] [Nonempty Seed]
    (nmExt : X → Seed → Adv → Bool) (k ε : ℝ) :
    IsAdviceNonMalleableExtractor nmExt 0 k ε ↔
      ∀ a₀ : Adv, IsStrongExtractor (fun x r => nmExt x r a₀) k ε := by
  let e : (Seed × Bool) ≃ (Seed × Bool × (Fin 0 → Bool)) :=
    { toFun := fun rb => (rb.1, rb.2, Fin.elim0)
      invFun := fun rbv => (rbv.1, rbv.2.1)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨r, b, v⟩ => Prod.ext rfl (Prod.ext rfl (funext fun j => Fin.elim0 j)) }
  have he (source : PMF X) (a₀ : Adv) (f : Fin 0 → Seed → Seed × Adv) :
      dist
        (source.bind fun x => (PMF.uniformOfFintype Seed).map fun r =>
          (r, nmExt x r a₀, fun j => nmExt x (f j r).1 (f j r).2))
        (source.bind fun x => (PMF.uniformOfFintype Seed).bind fun r =>
          (PMF.uniformOfFintype Bool).map fun b =>
            (r, b, fun j => nmExt x (f j r).1 (f j r).2)) =
      dist
        (source.bind fun x => (PMF.uniformOfFintype Seed).map fun r => (r, nmExt x r a₀))
        (PMF.uniformOfFintype (Seed × Bool)) := by
    have hv (x : X) (r : Seed) : (r, nmExt x r a₀, fun j => nmExt x (f j r).1 (f j r).2) =
        e (r, nmExt x r a₀) := Prod.ext rfl (Prod.ext rfl (funext fun j => j.elim0))
    have hL :
        (source.bind fun x => (PMF.uniformOfFintype Seed).map fun r =>
          (r, nmExt x r a₀, fun j => nmExt x (f j r).1 (f j r).2)) =
        (source.bind fun x => (PMF.uniformOfFintype Seed).map fun r =>
          (r, nmExt x r a₀)).map e := by
      simp only [hv, PMF.map_bind, PMF.map_comp, Function.comp_def]
    have hR :
        (source.bind fun x => (PMF.uniformOfFintype Seed).bind fun r =>
          (PMF.uniformOfFintype Bool).map fun b =>
            (r, b, fun j => nmExt x (f j r).1 (f j r).2)) =
        (PMF.uniformOfFintype (Seed × Bool)).map e := by
      have hb (x : X) (r : Seed) (b : Bool) :
          (r, b, fun j => nmExt x (f j r).1 (f j r).2) = e (r, b) :=
        Prod.ext rfl (Prod.ext rfl (funext fun j => j.elim0))
      simp only [hb, ← uniformOfFintype_prod, PMF.map_bind, PMF.map_comp, Function.comp_def,
        PMF.bind_const]
    rw [hL, hR, dist_map_of_injective _ _ e.injective]
  constructor
  · intro hnm a₀ source hsource
    rw [← he source a₀ (fun j => Fin.elim0 j)]
    exact hnm source hsource a₀ 0 le_rfl (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
  · intro hs source hsource a₀ m hm f _
    obtain rfl : m = 0 := Nat.le_zero.mp hm
    rw [he source a₀ f]
    exact hs a₀ source hsource

/-! ### Seeded correlation and strong-extractor Markov bounds -/

/-- An expectation of a score bounded by `C` on the support has absolute value at most `C`. -/
private theorem abs_sum_toReal_mul_le {α : Type*} [Fintype α] (ν : PMF α) {F : α → ℝ} {C : ℝ}
    (hF : ∀ a ∈ ν.support, |F a| ≤ C) : |∑ a, (ν a).toReal * F a| ≤ C := by
  calc |∑ a, (ν a).toReal * F a| ≤ ∑ a, (ν a).toReal * |F a| := by
        simpa only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg] using
          abs_sum_le_sum_abs (fun a => (ν a).toReal * F a) univ
    _ ≤ ∑ a, (ν a).toReal * C := sum_toReal_mul_mono_support ν hF
    _ = C := by rw [← sum_mul, sum_toReal, one_mul]

private theorem sum_abs_signVal_mul_prod_le {X Seed Adv : Type*} [Fintype X] [Fintype Seed]
    [Nonempty Seed] {nmExt : X → Seed → Adv → Bool} {t : ℕ} {k ε : ℝ}
    (hnm : IsAdviceNonMalleableExtractor nmExt t k ε) {p : PMF X} (hp : k ≤ minEntropy p)
    (a₀ : Adv) {m : ℕ} (hm : m ≤ t) (f : Fin m → Seed → Seed × Adv)
    (hf : ∀ j r, f j r ≠ (r, a₀)) :
    ∑ r : Seed,
      |∑ x : X, (p x).toReal *
        (BitString.signVal (nmExt x r a₀) *
          ∏ j : Fin m, BitString.signVal (nmExt x (f j r).1 (f j r).2))| ≤
      2 * (Fintype.card Seed : ℝ) * ε := by
  classical
  let inner (r : Seed) : ℝ := ∑ x : X, (p x).toReal *
    (BitString.signVal (nmExt x r a₀) *
      ∏ j : Fin m, BitString.signVal (nmExt x (f j r).1 (f j r).2))
  change ∑ r, |inner r| ≤ _
  let s (r : Seed) : ℝ := if 0 ≤ inner r then 1 else -1
  have hs (r : Seed) : |inner r| = s r * inner r := by
    by_cases h : 0 ≤ inner r
    · simp [s, h, abs_of_nonneg h]
    · simp [s, h, abs_of_neg (not_le.mp h)]
  -- Test the two distributions against `s r * signVal b * χ v`, which averages to `0` under the
  -- uniform bit and to `(∑ r, |inner r|) / |Seed|` under the extractor output.
  let φ (z : Seed × Bool × (Fin m → Bool)) : ℝ :=
    s z.1 * (BitString.signVal z.2.1 * ∏ j, BitString.signVal (z.2.2 j))
  have hφ (z : Seed × Bool × (Fin m → Bool)) : |φ z| ≤ 1 := by
    have : |s z.1| = 1 := by by_cases h : 0 ≤ inner z.1 <;> simp [s, h]
    simp [φ, abs_mul, this, Finset.abs_prod]
  have h := (abs_sum_mul_sub_le _ _ φ hφ).trans
    (mul_le_mul_of_nonneg_left (hnm p hp a₀ m hm f hf) (by norm_num))
  simp only [sum_bind_mul, sum_map_mul, Fintype.sum_bool, φ, BitString.signVal_true,
    BitString.signVal_false, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast] at h
  simp only [neg_one_mul, one_mul, mul_neg, neg_add_cancel, mul_zero, sum_const_zero, sub_zero,
    mul_left_comm (p _).toReal (Fintype.card Seed : ℝ)⁻¹, ← mul_sum, abs_mul, abs_inv,
    Nat.abs_cast] at h
  rw [inv_mul_le_iff₀ (by positivity)] at h
  convert (le_abs_self _).trans h using 1
  · simp_rw [hs, inner, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun x _ => sum_congr rfl fun r _ => by ring
  · ring

/-- **Markov lemma for strong extractors**: if `cond : Y → Fin D → Seed₂` is a strong
`(k₂, ε_ext)`-extractor, then for every `k₂`-source `q` on `Y` and every `δ > 0`, there is a
bad set `B` of at most `⌊ε_ext * D / δ⌋` seeds outside which `q.map (fun y => cond y i)` is a
`(log₂ |Seed₂|, δ)`-source. -/
theorem exists_badSet_isSource_of_isStrongExtractor {Y Seed₂ : Type*} {D : ℕ} [NeZero D]
    [Fintype Seed₂] [Nonempty Seed₂] {cond : Y → Fin D → Seed₂} {k₂ ε_ext : ℝ}
    (hcond : IsStrongExtractor cond k₂ ε_ext) {q : PMF Y} (hq : k₂ ≤ minEntropy q)
    {δ : ℝ≥0} (hδ : 0 < δ) :
    ∃ B : Finset (Fin D), #B ≤ Nat.floor (ε_ext * D / δ) ∧
      ∀ i ∉ B, IsSource (q.map fun y => cond y i) (Real.logb 2 (Fintype.card Seed₂)) δ := by
  classical
  have hstrong := hcond q hq
  have hpairL : (q.bind fun y => (PMF.uniformOfFintype (Fin D)).map fun i => (i, cond y i)) =
      (PMF.uniformOfFintype (Fin D)).bind fun i => (q.map fun y => cond y i).map (i, ·) := by
    simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
    exact PMF.bind_comm _ _ _
  rw [hpairL, ← uniformOfFintype_prod, dist_bind_pair] at hstrong
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Fintype.card_fin, ← mul_sum] at hstrong
  rw [inv_mul_le_iff₀ (Nat.cast_pos.mpr (NeZero.pos D))] at hstrong
  let B : Finset (Fin D) := univ.filter fun i =>
    (δ : ℝ) < dist (q.map fun y => cond y i) (PMF.uniformOfFintype Seed₂)
  refine ⟨B, Nat.le_floor ?_, fun i hiB => ⟨_, minEntropy_uniformOfFintype.ge, ?_⟩⟩
  · rw [le_div_iff₀ (NNReal.coe_pos.mpr hδ)]
    calc (#B : ℝ) * δ
        ≤ ∑ i ∈ B, dist (q.map fun y => cond y i) (PMF.uniformOfFintype Seed₂) := by
          simpa using B.card_nsmul_le_sum _ (δ : ℝ) fun i hi => (mem_filter.mp hi).2.le
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ B) fun _ _ _ => dist_nonneg
      _ ≤ _ := hstrong.trans_eq (mul_comm _ _)
  · simpa [B, StatisticallyClose] using hiB

/-! ### Conditional small-bias and the two-source extractor reduction -/

/-- **Conditional `(t + 1)`-wise small bias on good seeds**: if `p` has min-entropy at least `k₁`,
every seed `i ∉ B` condenses `q` to a `(log₂ |Seed₂| - Δ, γ)`-source, and `nmExt` is
`t`-non-malleable with advice for min-entropy `k₁`, then the good-coordinate marginal
`Bᶜ.restrict` of `(nmExt x (cond y i) i)_i` is `(t + 1)`-wise
`(2 * γ + 2 ^ (Δ + 1) * ε_nm)`-biased. -/
theorem isKWiseSmallBias_map_restrict_of_condenser
    {X Y Seed₂ : Type*} [Finite X] [Finite Y] {D : ℕ} [Fintype Seed₂] [Nonempty Seed₂]
    {cond : Y → Fin D → Seed₂} {nmExt : X → Seed₂ → Fin D → Bool}
    {p : PMF X} {q : PMF Y} {B : Finset (Fin D)} {k₁ Δ ε_nm : ℝ} {γ : ℝ≥0} {t : ℕ}
    (hp : k₁ ≤ minEntropy p)
    (hB : ∀ i ∉ B, IsSource (q.map fun y => cond y i) (Real.logb 2 (Fintype.card Seed₂) - Δ) γ)
    (hnm : IsAdviceNonMalleableExtractor nmExt t k₁ ε_nm) :
    IsKWiseSmallBias (t + 1) (2 * (γ : ℝ) + 2 ^ (Δ + 1) * ε_nm)
      ((p.bind fun x => q.map fun y => fun i => nmExt x (cond y i) i).map Bᶜ.restrict) := by
  classical
  cases nonempty_fintype X
  cases nonempty_fintype Y
  let Z : PMF (BitString D) := p.bind fun x => q.map fun y => fun i => nmExt x (cond y i) i
  intro S hS hSt
  rw [bias_map_restrict]
  let S' : Finset (Fin D) := S.map (Function.Embedding.subtype (· ∈ Bᶜ))
  change |bias Z S'| ≤ 2 * (γ : ℝ) + 2 ^ (Δ + 1) * ε_nm
  have hS'_ne : S'.Nonempty := hS.map
  have hS'_le : #S' ≤ t + 1 := by simpa [S', card_map] using hSt
  have hS'_good : ∀ i ∈ S', i ∉ B := fun i hi => by
    obtain ⟨⟨j, hj⟩, _, rfl⟩ := mem_map.mp hi
    exact mem_compl.mp hj
  obtain ⟨a₀, ha₀S'⟩ := hS'_ne
  let T : Finset (Fin D) := S'.erase a₀
  let m : ℕ := #T
  have hm : m ≤ t := by
    have hcard : #T + 1 = #S' := card_erase_add_one ha₀S'
    omega
  let e : Fin m ≃ T := T.equivFin.symm
  obtain ⟨R', hR'_ent, hR'_close⟩ := hB a₀ (hS'_good a₀ ha₀S')
  let joint : PMF (Seed₂ × Y) := q.map fun y => (cond y a₀, y)
  let R : PMF Seed₂ := q.map fun y => cond y a₀
  have hjoint_fst : joint.map Prod.fst = R := by
    simp only [joint, R, PMF.map_comp]
    rfl
  have hjoint_snd : joint.map Prod.snd = q := by
    dsimp only [joint]
    rw [PMF.map_comp]
    exact PMF.map_id q
  let τ : Seed₂ → PMF Y := conditionalSnd joint
  have hbind_τ : R.bind τ = q := by
    have hrecon := bind_conditionalSnd joint
    have hsnd := congrArg (PMF.map Prod.snd) hrecon
    rw [hjoint_fst, hjoint_snd, PMF.map_bind] at hsnd
    have hid : (fun a => ((τ a).map (a, ·)).map Prod.snd) = τ :=
      funext fun a => (PMF.map_comp _ _ _).trans (PMF.map_id _)
    rwa [hid] at hsnd
  have hτ_cond {r : Seed₂} {y : Y} (hr : r ∈ R.support) (hy : y ∈ (τ r).support) :
      cond y a₀ = r := by
    have hmem : (r, y) ∈ joint.support :=
      (mem_support_conditionalSnd_iff joint r (by rwa [hjoint_fst]) y).mp hy
    obtain ⟨y', _, hy'⟩ := (PMF.mem_support_map_iff (fun a => (cond a a₀, a)) q (r, y)).mp hmem
    obtain ⟨h1, h2⟩ := Prod.mk.inj hy'
    rw [← h2]
    exact h1
  let evalCond (r : Seed₂) : ℝ :=
    if r ∈ R.support then
      ∑ x : X, (p x).toReal *
        ∑ y : Y, (τ r y).toReal * chi ℝ S' (fun i => nmExt x (cond y i) i)
    else 0
  have hbias_Z : bias Z S' = ∑ r : Seed₂, (R r).toReal * evalCond r := by
    simp only [bias, Z, sum_bind_mul, sum_map_mul]
    conv_lhs => rw [← hbind_τ]
    simp only [sum_bind_mul, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    by_cases hr : r ∈ R.support
    · simp only [evalCond, hr, ↓reduceIte, mul_sum]
      exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
    · simp [(R.apply_eq_zero_iff r).mpr hr]
  have heval_abs (r : Seed₂) : |evalCond r| ≤ 1 := by
    unfold evalCond
    split_ifs
    · exact abs_sum_toReal_mul_le p fun x _ => abs_sum_toReal_mul_le (τ r) fun y _ =>
        (abs_chi ..).le
    · simp
  have hswap_R : |bias Z S' - ∑ r : Seed₂, (R' r).toReal * evalCond r| ≤ 2 * (γ : ℝ) := by
    rw [hbias_Z]
    linarith [abs_sum_mul_sub_le R R' evalCond heval_abs, show dist R R' ≤ γ from hR'_close]
  let μ : PMF (Seed₂ → Y) := Probability.PMF.pi τ
  have hμ_exp (x : X) (r : Seed₂) :
      ∑ y : Y, (τ r y).toReal * chi ℝ S' (fun i => nmExt x (cond y i) i) =
        ∑ g : Seed₂ → Y, (μ g).toReal * chi ℝ S' (fun i => nmExt x (cond (g r) i) i) := by
    rw [← pi_map_eval τ r,
      sum_map_mul μ (fun g => g r) fun y => chi ℝ S' (fun i => nmExt x (cond y i) i)]
  have hR'_eq :
      ∑ r : Seed₂, (R' r).toReal * evalCond r =
        ∑ g : Seed₂ → Y, (μ g).toReal *
          ∑ r : Seed₂, (R' r).toReal *
            if r ∈ R.support then
              ∑ x : X, (p x).toReal * chi ℝ S' (fun i => nmExt x (cond (g r) i) i)
            else 0 := by
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    by_cases hr : r ∈ R.support
    · simp only [evalCond, hr, ↓reduceIte, hμ_exp, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun g _ => sum_congr rfl fun x _ => by ring
    · simp only [evalCond, hr, ↓reduceIte, mul_zero, sum_const_zero]
  have hg_le (g : Seed₂ → Y) (hg : g ∈ μ.support) :
      |∑ r : Seed₂, (R' r).toReal *
          if r ∈ R.support then
            ∑ x : X, (p x).toReal * chi ℝ S' (fun i => nmExt x (cond (g r) i) i)
          else 0| ≤ 2 ^ (Δ + 1) * ε_nm := by
    let f : Fin m → Seed₂ → Seed₂ × Fin D := fun j r => (cond (g r) (e j : Fin D), (e j : Fin D))
    have hf : ∀ j r, f j r ≠ (r, a₀) := fun j r h =>
      (ne_of_mem_erase (e j).2) (congrArg Prod.snd h)
    have hχ (x : X) {r : Seed₂} (hr : r ∈ R.support) :
        chi ℝ S' (fun i => nmExt x (cond (g r) i) i) =
          BitString.signVal (nmExt x r a₀) *
            ∏ j : Fin m, BitString.signVal (nmExt x (f j r).1 (f j r).2) := by
      have hr_eq : cond (g r) a₀ = r :=
        hτ_cond hr ((mem_support_pi_iff τ g).mp hg r)
      have ha₀T : a₀ ∉ T := notMem_erase a₀ S'
      have hS'_eq : S' = insert a₀ T := (insert_erase ha₀S').symm
      rw [chi_eq_prod_signVal, hS'_eq, prod_insert ha₀T, hr_eq]
      congr 1
      rw [← prod_coe_sort T]
      exact (Fintype.prod_equiv e (fun j => BitString.signVal (nmExt x (f j r).1 (f j r).2))
        (fun i : T => BitString.signVal (nmExt x (cond (g r) i.1) i.1)) fun j => rfl).symm
    have hR'_mass (r : Seed₂) : (R' r).toReal ≤ 2 ^ Δ / (Fintype.card Seed₂ : ℝ) := by
      have hle := (le_minEntropy_iff R').mp hR'_ent r
      have hpow : (2 : ℝ) ^ (-(Real.logb 2 (Fintype.card Seed₂) - Δ)) =
          2 ^ Δ / (Fintype.card Seed₂ : ℝ) := by
        have hpos : (0 : ℝ) < Fintype.card Seed₂ := Nat.cast_pos.mpr Fintype.card_pos
        rw [neg_sub, sub_eq_add_neg, Real.rpow_add two_pos,
          Real.rpow_neg zero_le_two (Real.logb 2 (Fintype.card Seed₂)),
          Real.rpow_logb two_pos (by norm_num) hpos, div_eq_mul_inv]
      exact hle.trans_eq hpow
    have hcoef : 0 ≤ (2 : ℝ) ^ Δ / Fintype.card Seed₂ := by positivity
    calc _ ≤ ∑ r : Seed₂, (2 ^ Δ / (Fintype.card Seed₂ : ℝ)) *
            |∑ x : X, (p x).toReal *
              (BitString.signVal (nmExt x r a₀) *
                ∏ j : Fin m, BitString.signVal (nmExt x (f j r).1 (f j r).2))| := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => ?_)
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          split_ifs with hr
          · rw [sum_congr rfl fun x _ => congrArg (_ * ·) (hχ x hr)]
            exact mul_le_mul_of_nonneg_right (hR'_mass r) (abs_nonneg _)
          · simpa using mul_nonneg hcoef (abs_nonneg _)
      _ ≤ (2 ^ Δ / (Fintype.card Seed₂ : ℝ)) * (2 * (Fintype.card Seed₂ : ℝ) * ε_nm) := by
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left (sum_abs_signVal_mul_prod_le hnm hp a₀ hm f hf) hcoef
      _ = 2 ^ (Δ + 1) * ε_nm := by
          rw [Real.rpow_add two_pos, Real.rpow_one]
          field_simp
  have hR'_le : |∑ r : Seed₂, (R' r).toReal * evalCond r| ≤ 2 ^ (Δ + 1) * ε_nm := by
    rw [hR'_eq]
    exact abs_sum_toReal_mul_le μ hg_le
  linarith [abs_sub_abs_le_abs_sub (bias Z S') (∑ r : Seed₂, (R' r).toReal * evalCond r)]

/-- **Chattopadhyay–Zuckerman two-source extractor reduction**: combining a strong seeded
condenser `cond` (missing at most `q_bad` bad seeds, with min-entropy deficiency `Δ` and error
`γ` on good seeds), an advice `t`-non-malleable extractor `nmExt`, and a `(t + 1)`-independent
`(q_bad, ε_res)`-resilient function `f` of `(t + 1)`-independent bias at most `ε_bias` yields a
two-source extractor `fun x y => f fun i => nmExt x (cond y i) i`
[Chattopadhyay–Zuckerman][ChattopadhyayZuckerman2019]. -/
theorem isTwoSourceExtractor_of_resilient_condenser
    {X Y Seed₂ : Type*} [Finite X] [Finite Y] {D : ℕ} [NeZero D]
    [Fintype Seed₂] [Nonempty Seed₂]
    (cond : Y → Fin D → Seed₂) (nmExt : X → Seed₂ → Fin D → Bool) (f : BitString D → Bool)
    {k₁ k₂ Δ ε_nm ε_bias ε_res : ℝ} {t q_bad : ℕ} {γ : ℝ≥0}
    (hcond : ∀ q : PMF Y, k₂ ≤ minEntropy q →
      ∃ B : Finset (Fin D), #B ≤ q_bad ∧
        ∀ i ∉ B, IsSource (q.map fun y => cond y i) (Real.logb 2 (Fintype.card Seed₂) - Δ) γ)
    (hnm : IsAdviceNonMalleableExtractor nmExt t k₁ ε_nm)
    (hq_bad : q_bad ≤ D)
    (hf_bias : ∀ D' : PMF (BitString D), IsKWiseIndependent (t + 1) D' →
      |(∑ z, (D' z).toReal * BitString.bitVal ℝ (f z)) - 1 / 2| ≤ ε_bias)
    (hf_res : BitString.IsKWiseResilient (t + 1) q_bad ε_res f) :
    IsTwoSourceExtractor (fun x y => f fun i => nmExt x (cond y i) i) k₁ k₂
      (ε_bias + ε_res + (D : ℝ) ^ (t + 1) * (2 * (γ : ℝ) + 2 ^ (Δ + 1) * ε_nm)) := by
  intro p q hp hq
  obtain ⟨B, hBcard, hBgood⟩ := hcond q hq
  let Z : PMF (BitString D) := p.bind fun x => q.map fun y => fun i => nmExt x (cond y i) i
  have hmap : (p.bind fun x => q.map fun y => f fun i => nmExt x (cond y i) i) = Z.map f := by
    simp only [Z, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hε_nm : 0 ≤ ε_nm :=
    dist_nonneg.trans (hnm p hp (0 : Fin D) 0 (Nat.zero_le t) (fun j => Fin.elim0 j)
      (fun j => Fin.elim0 j))
  have hsmall := isKWiseSmallBias_map_restrict_of_condenser hp hBgood hnm
  have hres := dist_map_uniformOfFintype_bool_le_of_isKWiseSmallBias_restrict Z B f
    hBcard (by simpa using hq_bad) (by positivity) hsmall hf_bias hf_res
  rw [hmap]
  simpa using hres

/-- **Two-source extractor reduction using a strong seeded extractor**: instantiating
`isTwoSourceExtractor_of_resilient_condenser` with `Δ = 0` via Markov's inequality on
`IsStrongExtractor cond k₂ ε_ext`. -/
theorem isTwoSourceExtractor_of_resilient_strongExtractor
    {X Y Seed₂ : Type*} [Finite X] [Finite Y] {D : ℕ} [NeZero D]
    [Fintype Seed₂] [Nonempty Seed₂]
    (cond : Y → Fin D → Seed₂) (nmExt : X → Seed₂ → Fin D → Bool) (f : BitString D → Bool)
    {k₁ k₂ ε_ext ε_nm ε_bias ε_res : ℝ} {δ : ℝ≥0} {t q_bad : ℕ}
    (hδ : 0 < δ) (hcond : IsStrongExtractor cond k₂ ε_ext)
    (hnm : IsAdviceNonMalleableExtractor nmExt t k₁ ε_nm)
    (hq_floor : Nat.floor (ε_ext * D / δ) ≤ q_bad) (hq_bad : q_bad ≤ D)
    (hf_bias : ∀ D' : PMF (BitString D), IsKWiseIndependent (t + 1) D' →
      |(∑ z, (D' z).toReal * BitString.bitVal ℝ (f z)) - 1 / 2| ≤ ε_bias)
    (hf_res : BitString.IsKWiseResilient (t + 1) q_bad ε_res f) :
    IsTwoSourceExtractor (fun x y => f fun i => nmExt x (cond y i) i) k₁ k₂
      (ε_bias + ε_res + (D : ℝ) ^ (t + 1) * (2 * (δ : ℝ) + 2 * ε_nm)) := by
  have h := isTwoSourceExtractor_of_resilient_condenser (Δ := 0) cond nmExt f
    (fun q hq => by
      obtain ⟨B, hBcard, hBgood⟩ := exists_badSet_isSource_of_isStrongExtractor hcond hq hδ
      exact ⟨B, hBcard.trans hq_floor, fun i hi => by
        simpa only [sub_zero] using hBgood i hi⟩)
    hnm hq_bad hf_bias hf_res
  simpa using h

end Cslib.Probability
