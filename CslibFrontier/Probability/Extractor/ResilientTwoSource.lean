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
    have hL :
        (source.bind fun x => (PMF.uniformOfFintype Seed).map fun r =>
          (r, nmExt x r a₀, fun j => nmExt x (f j r).1 (f j r).2)) =
        (source.bind fun x => (PMF.uniformOfFintype Seed).map fun r =>
          (r, nmExt x r a₀)).map e := by
      rw [PMF.map_bind]
      refine congrArg (source.bind ·) (funext fun x => ?_)
      rw [PMF.map_comp]
      refine congrArg (fun g => (PMF.uniformOfFintype Seed).map g) (funext fun r => ?_)
      dsimp only [Function.comp_def, e]
      exact Prod.ext rfl (Prod.ext rfl (funext fun j => Fin.elim0 j))
    have hR :
        (source.bind fun x => (PMF.uniformOfFintype Seed).bind fun r =>
          (PMF.uniformOfFintype Bool).map fun b =>
            (r, b, fun j => nmExt x (f j r).1 (f j r).2)) =
        (PMF.uniformOfFintype (Seed × Bool)).map e := by
      have hinner (x : X) :
          ((PMF.uniformOfFintype Seed).bind fun r => (PMF.uniformOfFintype Bool).map fun b =>
            (r, b, fun j => nmExt x (f j r).1 (f j r).2)) =
          (PMF.uniformOfFintype (Seed × Bool)).map e := by
        rw [← uniformOfFintype_prod, PMF.map_bind]
        refine congrArg ((PMF.uniformOfFintype Seed).bind ·) (funext fun r => ?_)
        rw [PMF.map_comp]
        refine congrArg (fun g => (PMF.uniformOfFintype Bool).map g) (funext fun b => ?_)
        dsimp only [Function.comp_def, e]
        exact Prod.ext rfl (Prod.ext rfl (funext fun j => Fin.elim0 j))
      simp_rw [hinner, PMF.bind_const]
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
  let g (x : X) (r : Seed) : Fin m → Bool := fun j => nmExt x (f j r).1 (f j r).2
  let P₁ := p.bind fun x => (PMF.uniformOfFintype Seed).map fun r => (r, nmExt x r a₀, g x r)
  let P₂ := p.bind fun x => (PMF.uniformOfFintype Seed).bind fun r =>
    (PMF.uniformOfFintype Bool).map fun b => (r, b, g x r)
  have hdist : dist P₁ P₂ ≤ ε := hnm p hp a₀ m hm f hf
  let cTrue (r : Seed) (v : Fin m → Bool) : ℝ :=
    ∑ x : X, if nmExt x r a₀ = true ∧ g x r = v then (p x).toReal else 0
  let cFalse (r : Seed) (v : Fin m → Bool) : ℝ :=
    ∑ x : X, if nmExt x r a₀ = false ∧ g x r = v then (p x).toReal else 0
  have hcardS : (Fintype.card Seed : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hP₁ (r : Seed) (b : Bool) (v : Fin m → Bool) :
      (P₁ (r, b, v)).toReal =
        (∑ x : X, if nmExt x r a₀ = b ∧ g x r = v then (p x).toReal else 0) /
          Fintype.card Seed := by
    simp only [P₁, bind_apply_toReal, map_apply_toReal, PMF.uniformOfFintype_apply,
      ENNReal.toReal_inv, ENNReal.toReal_natCast]
    have hinner (x : X) :
        (∑ r' : Seed, if (r, b, v) = (r', nmExt x r' a₀, g x r') then
          (Fintype.card Seed : ℝ)⁻¹ else 0) =
          if nmExt x r a₀ = b ∧ g x r = v then (Fintype.card Seed : ℝ)⁻¹ else 0 := by
      have hr' : (∑ r' : Seed, if (r, b, v) = (r', nmExt x r' a₀, g x r') then
            (Fintype.card Seed : ℝ)⁻¹ else 0) =
          ∑ r' : Seed, if r' = r then
            (if nmExt x r a₀ = b ∧ g x r = v then (Fintype.card Seed : ℝ)⁻¹ else 0) else 0 := by
        refine sum_congr rfl fun r' _ => ?_
        by_cases hrr' : r' = r
        · subst hrr'
          simp [eq_comm]
        · have hne : (r, b, v) ≠ (r', nmExt x r' a₀, g x r') :=
            fun h => hrr' (congrArg Prod.fst h).symm
          simp [hrr', hne]
      rw [hr', sum_ite_eq', ite_eq_left (mem_univ r)]
    simp_rw [hinner, sum_div]
    refine sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  have hP₁_true (r : Seed) (v : Fin m → Bool) :
      (P₁ (r, true, v)).toReal = cTrue r v / Fintype.card Seed := hP₁ r true v
  have hP₁_false (r : Seed) (v : Fin m → Bool) :
      (P₁ (r, false, v)).toReal = cFalse r v / Fintype.card Seed := hP₁ r false v
  have hP₂ (r : Seed) (b : Bool) (v : Fin m → Bool) :
      (P₂ (r, b, v)).toReal = (cTrue r v + cFalse r v) / (2 * Fintype.card Seed) := by
    dsimp only [P₂]
    rw [bind_apply_toReal]
    have hinner (x : X) :
        (((PMF.uniformOfFintype Seed).bind fun r' =>
          (PMF.uniformOfFintype Bool).map fun b' => (r', b', g x r')) (r, b, v)).toReal =
          (Fintype.card Seed : ℝ)⁻¹ * (if g x r = v then (2 : ℝ)⁻¹ else 0) := by
      rw [bind_apply_toReal]
      have hr' : (∑ r' : Seed, ((PMF.uniformOfFintype Seed r').toReal) *
            (((PMF.uniformOfFintype Bool).map fun b' => (r', b', g x r')) (r, b, v)).toReal) =
          ∑ r' : Seed, if r' = r then (Fintype.card Seed : ℝ)⁻¹ *
            (if g x r = v then (2 : ℝ)⁻¹ else 0) else 0 := by
        refine sum_congr rfl fun r' _ => ?_
        rw [map_apply_toReal, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
          ENNReal.toReal_natCast]
        by_cases hrr' : r' = r
        · subst hrr'
          rw [ite_eq_left rfl]
          refine congrArg ((Fintype.card Seed : ℝ)⁻¹ * ·) ?_
          rw [Fintype.sum_bool]
          simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
            Fintype.card_bool, Nat.cast_ofNat]
          by_cases hg : g x r' = v
          · cases b <;> simp [hg]
          · have hgv : v ≠ g x r' := Ne.symm hg
            cases b <;> simp [hg, hgv]
        · have hzero :
              ∑ b' : Bool, (if (r, b, v) = (r', b', g x r') then
                (PMF.uniformOfFintype Bool b').toReal else 0) = 0 :=
            sum_eq_zero fun b' _ => ite_eq_right fun h => hrr' (congrArg Prod.fst h).symm
          rw [ite_eq_right hrr', hzero, mul_zero]
      rw [hr', sum_ite_eq', ite_eq_left (mem_univ r)]
    simp_rw [hinner]
    dsimp only [cTrue, cFalse]
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun x _ => ?_
    cases nmExt x r a₀ <;> by_cases hg : g x r = v <;> simp [hg] <;> ring
  have hdist_eq :
      2 * (Fintype.card Seed : ℝ) * dist P₁ P₂ =
        ∑ r : Seed, ∑ v : Fin m → Bool, |cTrue r v - cFalse r v| := by
    rw [dist_eq, Fintype.sum_prod_type]
    have hswap : (∑ r : Seed, ∑ bv : Bool × (Fin m → Bool),
          |(P₁ (r, bv)).toReal - (P₂ (r, bv)).toReal|) =
        ∑ r : Seed, ∑ v : Fin m → Bool, |cTrue r v - cFalse r v| / Fintype.card Seed := by
      refine sum_congr rfl fun r _ => ?_
      rw [Fintype.sum_prod_type, Fintype.sum_bool, ← sum_add_distrib]
      refine sum_congr rfl fun v _ => ?_
      rw [hP₁_true, hP₁_false, hP₂, hP₂]
      have h2S : 0 < 2 * (Fintype.card Seed : ℝ) := by
        have hSpos : (0 : ℝ) < Fintype.card Seed := Nat.cast_pos.mpr Fintype.card_pos
        positivity
      have h1 :
          |cTrue r v / Fintype.card Seed -
              (cTrue r v + cFalse r v) / (2 * Fintype.card Seed)| =
            |cTrue r v - cFalse r v| / (2 * Fintype.card Seed) := by
        rw [show cTrue r v / Fintype.card Seed -
                (cTrue r v + cFalse r v) / (2 * Fintype.card Seed) =
              (cTrue r v - cFalse r v) / (2 * Fintype.card Seed) by field_simp; ring,
          abs_div, abs_of_pos h2S]
      have h2 :
          |cFalse r v / Fintype.card Seed -
              (cTrue r v + cFalse r v) / (2 * Fintype.card Seed)| =
            |cTrue r v - cFalse r v| / (2 * Fintype.card Seed) := by
        rw [show cFalse r v / Fintype.card Seed -
                (cTrue r v + cFalse r v) / (2 * Fintype.card Seed) =
              (-(cTrue r v - cFalse r v)) / (2 * Fintype.card Seed) by field_simp; ring,
          abs_div, abs_neg, abs_of_pos h2S]
      rw [h1, h2]
      ring
    rw [hswap]
    simp_rw [← sum_div]
    field_simp
  have hr_le (r : Seed) :
      |∑ x : X, (p x).toReal *
          (BitString.signVal (nmExt x r a₀) * ∏ j : Fin m, BitString.signVal (g x r j))| ≤
        ∑ v : Fin m → Bool, |cTrue r v - cFalse r v| := by
    have hsplit : (∑ x : X, (p x).toReal *
          (BitString.signVal (nmExt x r a₀) * ∏ j : Fin m, BitString.signVal (g x r j))) =
        ∑ v : Fin m → Bool, (∏ j : Fin m, BitString.signVal (v j)) * (cFalse r v - cTrue r v) := by
      have hfib : (∑ x : X, (p x).toReal *
            (BitString.signVal (nmExt x r a₀) * ∏ j : Fin m, BitString.signVal (g x r j))) =
          ∑ v : Fin m → Bool, ∑ x : X, if g x r = v then (p x).toReal *
            (BitString.signVal (nmExt x r a₀) * ∏ j : Fin m, BitString.signVal (v j)) else 0 := by
        rw [sum_comm]
        refine sum_congr rfl fun x _ => ?_
        have hite : (∑ v : Fin m → Bool, if g x r = v then (p x).toReal *
              (BitString.signVal (nmExt x r a₀) * ∏ j : Fin m, BitString.signVal (v j)) else 0) =
            ∑ v : Fin m → Bool, if v = g x r then (p x).toReal *
              (BitString.signVal (nmExt x r a₀) * ∏ j : Fin m, BitString.signVal (v j)) else 0 :=
          sum_congr rfl fun v _ => by simp only [eq_comm]
        rw [hite, sum_ite_eq', ite_eq_left (mem_univ _)]
      rw [hfib]
      refine sum_congr rfl fun v _ => ?_
      simp only [cFalse, cTrue, mul_sub, mul_sum]
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun x _ => ?_
      cases nmExt x r a₀ <;> by_cases hg : g x r = v <;> simp [hg] <;> ring
    rw [hsplit]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v _ => ?_)
    have hprod_abs : |∏ j : Fin m, BitString.signVal (v j)| = 1 := by
      rw [Finset.abs_prod]
      exact prod_eq_one fun j _ => abs_signVal (v j)
    rw [abs_mul, hprod_abs, one_mul, abs_sub_comm]
  calc ∑ r : Seed, |∑ x : X, (p x).toReal *
          (BitString.signVal (nmExt x r a₀) * ∏ j : Fin m, BitString.signVal (g x r j))|
      ≤ ∑ r : Seed, ∑ v : Fin m → Bool, |cTrue r v - cFalse r v| := sum_le_sum fun r _ => hr_le r
    _ = 2 * (Fintype.card Seed : ℝ) * dist P₁ P₂ := hdist_eq.symm
    _ ≤ 2 * (Fintype.card Seed : ℝ) * ε := by
        gcongr

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
    ext ⟨i, r⟩
    rw [bind_map_prodMk_apply, PMF.bind_apply]
    have hinner (y : Y) :
        ((PMF.uniformOfFintype (Fin D)).map fun i' => (i', cond y i')) (i, r) =
          if r = cond y i then PMF.uniformOfFintype (Fin D) i else 0 := by
      rw [PMF.map_apply, tsum_eq_single i]
      · simp [Prod.mk.injEq]
      · intro i' hi'
        exact ite_eq_right fun h => hi' (congrArg Prod.fst h).symm
    have hL : (∑' y : Y, q y *
          ((PMF.uniformOfFintype (Fin D)).map fun i' => (i', cond y i')) (i, r)) =
        ∑' y : Y, q y * (if r = cond y i then PMF.uniformOfFintype (Fin D) i else 0) :=
      tsum_congr fun y => congrArg (q y * ·) (hinner y)
    rw [hL, PMF.map_apply, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun y => ?_
    split_ifs <;> simp [mul_comm]
  have hpairR : PMF.uniformOfFintype (Fin D × Seed₂) =
      (PMF.uniformOfFintype (Fin D)).bind fun i =>
        (PMF.uniformOfFintype Seed₂).map (i, ·) := by
    rw [uniformOfFintype_prod]
  rw [hpairL, hpairR, dist_bind_pair] at hstrong
  have hsum_le : ∑ i : Fin D, dist (q.map fun y => cond y i) (PMF.uniformOfFintype Seed₂) ≤
      (D : ℝ) * ε_ext := by
    have havg : (∑ i : Fin D, ((PMF.uniformOfFintype (Fin D) i).toReal *
          dist (q.map fun y => cond y i) (PMF.uniformOfFintype Seed₂))) =
        (D : ℝ)⁻¹ * ∑ i : Fin D, dist (q.map fun y => cond y i) (PMF.uniformOfFintype Seed₂) := by
      simp_rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        Fintype.card_fin, ← mul_sum]
    rw [havg] at hstrong
    have hD : (0 : ℝ) < D := Nat.cast_pos.mpr (NeZero.pos D)
    rwa [inv_mul_le_iff₀ hD] at hstrong
  let B : Finset (Fin D) := univ.filter fun i =>
    (δ : ℝ) < dist (q.map fun y => cond y i) (PMF.uniformOfFintype Seed₂)
  have hB_le : (#B : ℝ) * (δ : ℝ) ≤ (D : ℝ) * ε_ext := by
    calc (#B : ℝ) * (δ : ℝ)
        = ∑ _i ∈ B, (δ : ℝ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ B, dist (q.map fun y => cond y i) (PMF.uniformOfFintype Seed₂) :=
          sum_le_sum fun i hi => (mem_filter.mp hi).2.le
      _ ≤ ∑ i : Fin D, dist (q.map fun y => cond y i) (PMF.uniformOfFintype Seed₂) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ B) fun _ _ _ => dist_nonneg
      _ ≤ (D : ℝ) * ε_ext := hsum_le
  refine ⟨B, Nat.le_floor ?_, ?_⟩
  · rw [le_div_iff₀ (NNReal.coe_pos.mpr hδ)]
    linarith
  · intro i hiB
    refine ⟨PMF.uniformOfFintype Seed₂, minEntropy_uniformOfFintype.ge, ?_⟩
    rw [StatisticallyClose]
    have hle : dist (q.map fun y => cond y i) (PMF.uniformOfFintype Seed₂) ≤ δ := by
      by_contra hlt
      exact hiB (mem_filter.mpr ⟨mem_univ i, not_le.mp hlt⟩)
    exact_mod_cast hle

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
    rw [bias, sum_bind_mul]
    have hx_eq (x : X) :
        ∑ z : BitString D, ((q.map fun y => fun i => nmExt x (cond y i) i) z).toReal * chi ℝ S' z =
          ∑ r : Seed₂, (R r).toReal *
            if r ∈ R.support then
              ∑ y : Y, (τ r y).toReal * chi ℝ S' (fun i => nmExt x (cond y i) i)
            else 0 := by
      rw [sum_map_mul]
      conv_lhs => rw [← hbind_τ]
      rw [sum_bind_mul]
      refine sum_congr rfl fun r _ => ?_
      by_cases hr : r ∈ R.support
      · rw [ite_eq_left hr]
      · have hzero : (R r).toReal = 0 := by
          rw [(R.apply_eq_zero_iff r).mpr hr, ENNReal.toReal_zero]
        rw [hzero, zero_mul, zero_mul]
    simp_rw [hx_eq, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    dsimp only [evalCond]
    by_cases hr : r ∈ R.support
    · simp_rw [ite_eq_left hr]
      rw [mul_sum]
      refine sum_congr rfl fun x _ => by ring
    · have hzero : (R r).toReal = 0 := by
        rw [(R.apply_eq_zero_iff r).mpr hr, ENNReal.toReal_zero]
      simp [hzero]
  have heval_abs (r : Seed₂) : |evalCond r| ≤ 1 := by
    dsimp only [evalCond]
    by_cases hr : r ∈ R.support
    · rw [ite_eq_left hr]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ x : X, |(p x).toReal *
              ∑ y : Y, (τ r y).toReal * chi ℝ S' (fun i => nmExt x (cond y i) i)|
          ≤ ∑ x : X, (p x).toReal * 1 := by
            refine sum_le_sum fun x _ => ?_
            rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
            refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
            refine (abs_sum_le_sum_abs _ _).trans_eq ?_
            calc ∑ y : Y, |(τ r y).toReal * chi ℝ S' (fun i => nmExt x (cond y i) i)|
                = ∑ y : Y, (τ r y).toReal * 1 := by
                  refine sum_congr rfl fun y _ => ?_
                  rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, abs_chi]
              _ = 1 := by rw [← sum_mul, sum_toReal, one_mul]
        _ = 1 := by rw [← sum_mul, sum_toReal, one_mul]
    · rw [ite_eq_right hr, abs_zero]
      exact zero_le_one
  have hswap_R : |bias Z S' - ∑ r : Seed₂, (R' r).toReal * evalCond r| ≤ 2 * (γ : ℝ) := by
    rw [hbias_Z]
    have hdist := abs_sum_mul_sub_le R R' evalCond heval_abs
    rw [StatisticallyClose] at hR'_close
    have hγ : dist R R' ≤ γ := by exact_mod_cast hR'_close
    linarith
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
    have hterm (r : Seed₂) :
        evalCond r = ∑ g : Seed₂ → Y, (μ g).toReal *
          if r ∈ R.support then
            ∑ x : X, (p x).toReal * chi ℝ S' (fun i => nmExt x (cond (g r) i) i)
          else 0 := by
      dsimp only [evalCond]
      by_cases hr : r ∈ R.support
      · rw [ite_eq_left hr]
        simp_rw [ite_eq_left hr, hμ_exp]
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun g _ => sum_congr rfl fun x _ => by ring
      · simp only [ite_eq_right hr, mul_zero, sum_const_zero]
    simp_rw [hterm]
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun g _ => sum_congr rfl fun r _ => by ring
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
    have hnm_sum := sum_abs_signVal_mul_prod_le hnm hp a₀ hm f hf
    calc |∑ r : Seed₂, (R' r).toReal *
            if r ∈ R.support then
              ∑ x : X, (p x).toReal * chi ℝ S' (fun i => nmExt x (cond (g r) i) i)
            else 0|
        ≤ ∑ r : Seed₂, |(R' r).toReal *
            if r ∈ R.support then
              ∑ x : X, (p x).toReal * chi ℝ S' (fun i => nmExt x (cond (g r) i) i)
            else 0| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ r : Seed₂, (2 ^ Δ / (Fintype.card Seed₂ : ℝ)) *
            |∑ x : X, (p x).toReal *
              (BitString.signVal (nmExt x r a₀) *
                ∏ j : Fin m, BitString.signVal (nmExt x (f j r).1 (f j r).2))| := by
          refine sum_le_sum fun r _ => ?_
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          by_cases hr : r ∈ R.support
          · rw [ite_eq_left hr]
            have hsum_eq :
                (∑ x : X, (p x).toReal * chi ℝ S' (fun i => nmExt x (cond (g r) i) i)) =
                  ∑ x : X, (p x).toReal *
                    (BitString.signVal (nmExt x r a₀) *
                      ∏ j : Fin m, BitString.signVal (nmExt x (f j r).1 (f j r).2)) :=
              sum_congr rfl fun x _ => congrArg (_ * ·) (hχ x hr)
            rw [hsum_eq]
            exact mul_le_mul_of_nonneg_right (hR'_mass r) (abs_nonneg _)
          · rw [ite_eq_right hr, abs_zero, mul_zero]
            exact mul_nonneg (div_nonneg (Real.rpow_nonneg zero_le_two _) (Nat.cast_nonneg _))
              (abs_nonneg _)
      _ = (2 ^ Δ / (Fintype.card Seed₂ : ℝ)) *
            ∑ r : Seed₂, |∑ x : X, (p x).toReal *
              (BitString.signVal (nmExt x r a₀) *
                ∏ j : Fin m, BitString.signVal (nmExt x (f j r).1 (f j r).2))| :=
          (mul_sum _ _ _).symm
      _ ≤ (2 ^ Δ / (Fintype.card Seed₂ : ℝ)) * (2 * (Fintype.card Seed₂ : ℝ) * ε_nm) :=
          mul_le_mul_of_nonneg_left hnm_sum
            (div_nonneg (Real.rpow_nonneg zero_le_two _) (Nat.cast_nonneg _))
      _ = 2 ^ (Δ + 1) * ε_nm := by
          have hcard : (Fintype.card Seed₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
          rw [Real.rpow_add two_pos, Real.rpow_one]
          field_simp
  have hR'_le : |∑ r : Seed₂, (R' r).toReal * evalCond r| ≤ 2 ^ (Δ + 1) * ε_nm := by
    rw [hR'_eq]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ g : Seed₂ → Y, |(μ g).toReal *
            ∑ r : Seed₂, (R' r).toReal *
              if r ∈ R.support then
                ∑ x : X, (p x).toReal * chi ℝ S' (fun i => nmExt x (cond (g r) i) i)
              else 0|
        ≤ ∑ g : Seed₂ → Y, (μ g).toReal * (2 ^ (Δ + 1) * ε_nm) := by
          refine sum_le_sum fun g _ => ?_
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          by_cases hg : g ∈ μ.support
          · exact mul_le_mul_of_nonneg_left (hg_le g hg) ENNReal.toReal_nonneg
          · rw [(μ.apply_eq_zero_iff g).mpr hg, ENNReal.toReal_zero, zero_mul, zero_mul]
      _ = 2 ^ (Δ + 1) * ε_nm := by rw [← sum_mul, sum_toReal, one_mul]
  have htri := abs_sub_le (bias Z S') (∑ r : Seed₂, (R' r).toReal * evalCond r) 0
  rw [sub_zero, sub_zero] at htri
  linarith

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
