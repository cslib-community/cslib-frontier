/-
Copyright (c) 2026 Mayank Rathee, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.OfFn
import CslibFrontier.Foundations.Data.Code.Johnson
import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson
import CslibFrontier.Foundations.Data.Code.ProximityGap.Unique
import CslibFrontier.Foundations.Data.Hamming
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.UniformBound
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.LinearCombination

/-!
# Coset-Folding Correlated Agreement, Out-of-Domain DEEP Quotienting, and DEEP-ALI Soundness

This module connects the Reed–Solomon proximity-gap and batched FRI IOP developments of
`CslibFrontier.Crypto.Protocols.FRI` to algebraic constraint linking and out-of-domain ("sampling
outside the box") polynomial protocols across three layers:

1. **General `a`-to-1 coset-folding correlated-agreement soundness** (`FoldSoundness`):
   `CslibFrontier.Crypto.Protocols.FRI.Folding` defines arbitrary-arity fiberwise coset folding
   `foldWord g ω f z : Fin N → F` for any `a ≥ 1` with `(a : F) ≠ 0` and proves fiberwise lifting
   (`exists_mem_reedSolomon_weighted_agree_lift`), while `FRI.Soundness` / `FRI.JohnsonSoundness`
   specialize folding soundness to power-of-two schedules `2 ^ stepLog i`. Here we establish
   standalone single-step folding soundness bounds directly on `foldWord g ω f z` for **arbitrary**
   positive arity `a` (including odd and composite radices) in both the unique-decoding regime
   (`toOuterMeasure_foldWord_reedSolomon_close_le_unique`) and the integer-weighted Guruswami–Sudan
   Johnson regime (`toOuterMeasure_foldWord_reedSolomon_weighted_agree_le_johnson_exact`).

2. **Out-of-domain DEEP quotienting, degree restoration, and Johnson list bounds** (`DeepQuotient`):
   formalizes polynomial quotienting `deepQuotientPoly p z = p /ₘ (X - C z)` and word-level virtual
   quotienting `deepQuotientWord α f z y = fun s => (f s - y) / (α s - z)` following the DEEP
   (*Domain Extending for Eliminating Pretenders*) technique of
   [BenSassonGoldbergKoppartySaraf2020]. Proves Reed–Solomon closure
   (`deepQuotientWord_mem_reedSolomon`), exact degree restoration and out-of-domain evaluation
   pinning from correlated agreement on any subset `D'` avoiding `z`
   (`exists_poly_of_deepQuotientWord_agree`), unique interpolation on `D'`
   (`eq_of_degree_lt_of_eval_eq_on`), and finite candidate-polynomial list bounds `agreePolyList`
   across both the unique-decoding radius (`card_agreePolyList_le_one_of_unique`) and the exact
   integer Johnson radius `|ι| * (k - 1) < a ^ 2` (`card_agreePolyList_le_of_johnson`, via
   [Johnson1962]).

3. **DEEP-ALI (Algebraic Linking IOP with Out-of-Domain Sampling) & Batched FRI Bridge**
   (`DeepALI`): formalizes multi-column masked polynomial constraint systems `DeepALISystem` (with
   monic zerofiers `Z_m(X)`, multiplicative trace shifts `maskShift u * X`, split
   composition-quotient chunks via `polyDegreeChunk`, and an out-of-domain sampling set `oodDom`),
   the interactive protocol game `deepALIGame` delegating low-degree testing of all mask and
   quotient-chunk DEEP words to a single `(m + 2)`-round `friSmoothBatchIOP` execution
   ([BenSassonCarmonIshaiKoppartySaraf2020], Section 8.2), the honest prover `honestDeepALIProver`
   with perfect completeness (`deepALIGame_honest_eq_pure_true`), deterministic correlated-agreement
   witness extraction (`exists_polys_of_batchStmt_mem_proximityLang`), and **unconditional adaptive
   interactive soundness** in both the unique-decoding regime (`deepALIGame_le_of_unique`) and the
   `1 - √ρ - η` Johnson list-decoding regime (`deepALIGame_le_of_johnson_eta`, using this library's
   explicit Siegel constants for batched FRI; internal theorem and page locators of
   [BenSassonGoldbergKoppartySaraf2020] were not re-verified against the primary PDF). Binary 2-to-1
   `FRIParams` corollaries follow via `FRIParams.toSmooth`
   (`deepALIGame_ofBinary_le_of_johnson_eta`).

## Main definitions

* `Cslib.Crypto.Protocols.FRI.deepQuotientPoly`, `Cslib.Crypto.Protocols.FRI.deepQuotientWord`:
  out-of-domain polynomial and evaluation-word DEEP quotient operators.
* `Cslib.Crypto.Protocols.FRI.agreePolyList`: finite candidate list of polynomials of degree `< k`
  agreeing with a word `w : ι → F` on at least `a` coordinates.
* `Cslib.Crypto.Protocols.FRI.constraintDegBound`, `Cslib.Crypto.Protocols.FRI.polyDegreeChunk`:
  tight univariate degree bound for masked multivariate constraints and degree-`(k + 1)` chunk
  decomposition of composition quotients.
* `Cslib.Crypto.Protocols.FRI.DeepALISystem`, `Cslib.Crypto.Protocols.FRI.DeepALIOpening`,
  `Cslib.Crypto.Protocols.FRI.DeepALIProver`, `Cslib.Crypto.Protocols.FRI.deepALIGame`,
  `Cslib.Crypto.Protocols.FRI.honestDeepALIProver`: masked algebraic constraint system,
  out-of-domain opening record, adaptive prover strategy, interactive DEEP-ALI + batched FRI game,
  and honest prover.

## Main results

* `Cslib.Crypto.Protocols.FRI.toOuterMeasure_foldWord_reedSolomon_close_le_unique`,
  `Cslib.Crypto.Protocols.FRI.toOuterMeasure_foldWord_reedSolomon_weighted_agree_le_johnson_exact`:
  standalone arbitrary-arity `a`-to-1 coset-folding proximity-gap and weighted correlated-agreement
  soundness bounds.
* `Cslib.Crypto.Protocols.FRI.mul_deepQuotientPoly_add_eval`,
  `Cslib.Crypto.Protocols.FRI.degree_deepQuotientPoly_lt`,
  `Cslib.Crypto.Protocols.FRI.deepQuotientWord_mem_reedSolomon`,
  `Cslib.Crypto.Protocols.FRI.exists_poly_of_deepQuotientWord_agree`: algebraic identity, degree
  drop, Reed–Solomon closure, and correlated-agreement degree restoration with evaluation pinning at
  the out-of-domain point.
* `Cslib.Crypto.Protocols.FRI.card_agreePolyList_le_one_of_unique`,
  `Cslib.Crypto.Protocols.FRI.card_agreePolyList_le_of_johnson`: unique-decoding (`≤ 1`) and exact
  integer Johnson (`≤ n * (a - (k - 1)) / (a ^ 2 - n * (k - 1))`) candidate list-size bounds.
* `Cslib.Crypto.Protocols.FRI.sum_X_pow_mul_polyDegreeChunk`,
  `Cslib.Crypto.Protocols.FRI.DeepALISystem.natDegree_evalMaskPoly_le`,
  `Cslib.Crypto.Protocols.FRI.DeepALISystem.prod_X_sub_C_dvd_evalMaskPoly_iff`: exact chunk
  reconstruction, tight masked-constraint degree bound, and pointwise subgroup/root-set constraint
  characterization.
* `Cslib.Crypto.Protocols.FRI.deepALIGame_honest_eq_pure_true`: perfect completeness of DEEP-ALI
  composed with smooth batched FRI.
* `Cslib.Crypto.Protocols.FRI.exists_polys_of_batchStmt_mem_proximityLang`,
  `Cslib.Crypto.Protocols.FRI.deepALIGame_le_of_unique`,
  `Cslib.Crypto.Protocols.FRI.deepALIGame_le_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.deepALIGame_ofBinary_le_of_johnson_eta`: correlated-agreement
  polynomial extraction and unconditional adaptive soundness of DEEP-ALI across the unique-decoding
  and `1 - √ρ - η` Johnson list-decoding regimes.

## References

* [E. Ben-Sasson, L. Goldberg, S. Kopparty, S. Saraf,
  *DEEP-FRI: Sampling Outside the Box Improves Soundness*][BenSassonGoldbergKoppartySaraf2020]
* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf,
  *Proximity Gaps for Reed–Solomon Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
* [E. Ben-Sasson, I. Bentov, Y. Horesh, M. Riabzev,
  *Fast Reed–Solomon Interactive Oracle Proofs of Proximity*][BenSassonBentovHoreshRiabzev2018]
* [S. M. Johnson, *A new upper bound for error-correcting codes*][Johnson1962]
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open Finset Polynomial Cslib.Code Cslib.Crypto.Protocols.BCS Cslib.Probability
open scoped BigOperators ENNReal

/-! ### Part 1: Standalone `a`-to-1 Coset-Folding Correlated-Agreement Soundness Bridge -/

section FoldSoundness

private lemma foldWord_eq_finCongr_sum {F : Type*} [Field F] (g ω : F) {a N : ℕ} (ha : 1 ≤ a)
    (f : Fin (a * N) → F) (z : F) :
    (∑ r : Fin ((a - 1) + 1), z ^ r.val • foldComp g ω f (finCongr (Nat.sub_add_cancel ha) r)) =
      foldWord g ω f z := by
  rw [foldWord_eq_sum_smul]
  exact Equiv.sum_comp (finCongr (Nat.sub_add_cancel ha)) fun r : Fin a =>
    z ^ r.val • foldComp g ω f r

private lemma cosetPoint_pow_injective {F : Type*} [Field F] {g ω : F} {a N : ℕ}
    (hg : g ≠ 0) (ha_pos : 0 < a) (hω : IsPrimitiveRoot ω (a * N)) :
    Function.Injective (cosetPoint (g ^ a) (ω ^ a) N) :=
  cosetPoint_injective (pow_ne_zero a hg)
    (by simpa only [Nat.mul_div_cancel_left N ha_pos] using
      hω.pow_of_dvd ha_pos.ne' ⟨N, rfl⟩)

/-- **Standalone `a`-to-1 coset-folding soundness in the unique-decoding regime**
(`2 * (e / a) + k ≤ N`, derived from [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5 and 6.1]
and `exists_mem_reedSolomon_weighted_agree_lift`): for any field `F`, nonzero coset offset `g`,
positive folding arity `a` with `(a : F) ≠ 0`, target size `N > 0`, and primitive `(a * N)`-th root
of unity `ω`, if `f : Fin (a * N) → F` has Hamming distance strictly greater than `e` from
`reedSolomon (cosetPoint g ω (a * N)) (a * k)`, then `foldWord g ω f z` lies within Hamming distance
`e / a` of `reedSolomon (cosetPoint (g ^ a) (ω ^ a) N) k` with probability at most
`((a - 1) * N) / |F|` over uniform `z : F`. -/
theorem toOuterMeasure_foldWord_reedSolomon_close_le_unique
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {g ω : F} {a N k e : ℕ}
    (hg : g ≠ 0) (ha : (a : F) ≠ 0) (hN : 0 < N) (hω : IsPrimitiveRoot ω (a * N))
    (huniq : 2 * (e / a) + k ≤ N)
    {f : Fin (a * N) → F}
    (hfar : ∀ c ∈ reedSolomon (cosetPoint g ω (a * N)) (a * k), e < hammingDist f c) :
    (PMF.uniformOfFintype F).toOuterMeasure
        {z : F | ∃ c' ∈ reedSolomon (cosetPoint (g ^ a) (ω ^ a) N) k,
          hammingDist (foldWord g ω f z) c' ≤ e / a} ≤
      (((a - 1) * N : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  have ha_pos : 0 < a := Nat.pos_of_ne_zero fun h => ha (by simp only [h, Nat.cast_zero])
  let eqA : Fin ((a - 1) + 1) ≃ Fin a := finCongr (Nat.sub_add_cancel ha_pos)
  refine Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_div Fintype.card_pos ?_
  rw [mul_comm ((a - 1) * N)]
  refine Nat.mul_le_mul_left (Fintype.card F) ?_
  by_contra hgt
  push Not at hgt
  obtain ⟨D', hD'_card, v', hv', hD'_agree⟩ :=
    exists_correlatedAgreement_curve_unique (cosetPoint_pow_injective hg ha_pos hω)
      (by simpa only [Fintype.card_fin] using huniq)
      (fun r => foldComp g ω f (eqA r)) _
      (by simpa only [Fintype.card_fin] using hgt)
      fun z hz => by
        rw [foldWord_eq_finCongr_sum g ω ha_pos f z]
        exact (Finset.mem_filter.mp hz).2
  obtain ⟨c, hc_mem, _, hsum⟩ :=
    exists_mem_reedSolomon_weighted_agree_lift hg ha hN hω f (fun r => v' (eqA.symm r))
      (fun r => hv' (eqA.symm r)) (fun _ => 1)
  have hsub : D' ⊆ Finset.univ.filter fun j : Fin N =>
      ∀ r : Fin a, foldComp g ω f r j = v' (eqA.symm r) j := fun j hj =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, fun r => by
      simpa only [Equiv.apply_symm_apply] using hD'_agree j hj (eqA.symm r)⟩
  have hpush : ∀ j : Fin N, pushWeight (a := a) (fun _ : Fin (a * N) => 1) j = a := fun j => by
    simp only [pushWeight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
  have hagree_ge : a * (N - e / a) ≤ (Finset.univ.filter fun i => f i = c i).card := by
    calc a * (N - e / a)
        ≤ a * D'.card := Nat.mul_le_mul_left a (by simpa only [Fintype.card_fin] using hD'_card)
      _ = ∑ j ∈ D', pushWeight (a := a) (fun _ : Fin (a * N) => 1) j := by
          simp only [hpush, Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N =>
            ∀ r : Fin a, foldComp g ω f r j = v' (eqA.symm r) j),
            pushWeight (fun _ => 1) j :=
          Finset.sum_le_sum_of_subset (f := pushWeight (a := a) (fun _ : Fin (a * N) => 1)) hsub
      _ ≤ (Finset.univ.filter fun i => f i = c i).card := by
          simpa only [Finset.sum_const, smul_eq_mul, mul_one] using hsum
  have htot := card_filter_eq_add_hammingDist f c
  rw [Fintype.card_fin] at htot
  have hdiv_le : a * (e / a) ≤ e := Nat.mul_div_le e a
  have hmul_sub : a * (N - e / a) = a * N - a * (e / a) := Nat.mul_sub a N (e / a)
  have hlt := hfar c hc_mem
  omega

/-- **Standalone integer-weighted `a`-to-1 coset-folding correlated-agreement bound in the
Guruswami–Sudan Johnson regime** (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5, 6.2, and 7.2]): for arbitrary folding arity
`a ≥ 1` with `(a : F) ≠ 0`, weights `W : Fin (a * N) → ℕ` bounded pointwise by `M₀ > 0` with sum at
most `W_tot`, and Guruswami–Sudan parameters `(m_GS, D)` at fiber cap `a * M₀`, if no codeword in
`reedSolomon (cosetPoint g ω (a * N)) (a * k)` achieves `W`-weighted agreement `> B` with `f`, then
`foldWord g ω f z` achieves `(pushWeight W)`-weighted agreement `> B` with a codeword in
`reedSolomon (cosetPoint (g ^ a) (ω ^ a) N) k` with probability at most
`johnsonCurveBound N m_GS (k - 1) D (a - 1) W_tot / |F|`. -/
theorem toOuterMeasure_foldWord_reedSolomon_weighted_agree_le_johnson_exact
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {g ω : F} {a N k m_GS D M₀ W_tot B : ℕ}
    (hg : g ≠ 0) (ha : (a : F) ≠ 0) (hN : 0 < N) (hω : IsPrimitiveRoot ω (a * N))
    (hk : 1 ≤ k) (hm_GS : 1 ≤ m_GS) (hM₀ : 0 < M₀)
    {W : Fin (a * N) → ℕ} (hW_le : ∀ i, W i ≤ M₀) (hW_sum : ∑ i, W i ≤ W_tot)
    (hk_le : k ≤ (B + 1 + a * M₀ - 1) / (a * M₀))
    (hinterp : N * (m_GS * (m_GS + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m_GS * ((B + 1 + a * M₀ - 1) / (a * M₀)))
    {f : Fin (a * N) → F}
    (hfar : ∀ c ∈ reedSolomon (cosetPoint g ω (a * N)) (a * k),
      (∑ i ∈ Finset.univ.filter (fun i => f i = c i), W i) ≤ B) :
    (PMF.uniformOfFintype F).toOuterMeasure
        {z : F | ∃ c' ∈ reedSolomon (cosetPoint (g ^ a) (ω ^ a) N) k,
          B < ∑ j ∈ Finset.univ.filter (fun j => foldWord g ω f z j = c' j), pushWeight W j} ≤
      (ProximityGap.johnsonCurveBound N m_GS (k - 1) D (a - 1) W_tot : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) := by
  classical
  have ha_pos : 0 < a := Nat.pos_of_ne_zero fun h => ha (by simp only [h, Nat.cast_zero])
  let eqA : Fin ((a - 1) + 1) ≃ Fin a := finCongr (Nat.sub_add_cancel ha_pos)
  refine Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_div Fintype.card_pos ?_
  rw [mul_comm (ProximityGap.johnsonCurveBound _ _ _ _ _ _)]
  refine Nat.mul_le_mul_left (Fintype.card F) ?_
  by_contra hgt
  push Not at hgt
  obtain ⟨D', hD'_wt, v', hv', hD'_agree⟩ :=
    exists_weighted_correlatedAgreement_curve_johnson
      (W := pushWeight W) (M := a * M₀) (W_tot := W_tot) (B_W := B + 1)
      (cosetPoint_pow_injective hg ha_pos hω) hk hm_GS (Nat.mul_pos ha_pos hM₀)
      (pushWeight_le hW_le) ((sum_pushWeight W).trans_le hW_sum) hk_le
      (by simpa only [Fintype.card_fin] using hinterp) hroot
      (fun r => foldComp g ω f (eqA r)) _
      (by simpa only [Fintype.card_fin] using hgt)
      fun z hz => by
        obtain ⟨c', hc', hwt⟩ := (Finset.mem_filter.mp hz).2
        refine ⟨c', hc', ?_⟩
        rw [foldWord_eq_finCongr_sum g ω ha_pos f z]
        exact Nat.succ_le_of_lt hwt
  obtain ⟨c, hc_mem, _, hsum⟩ :=
    exists_mem_reedSolomon_weighted_agree_lift hg ha hN hω f (fun r => v' (eqA.symm r))
      (fun r => hv' (eqA.symm r)) W
  have hsub : D' ⊆ Finset.univ.filter fun j : Fin N =>
      ∀ r : Fin a, foldComp g ω f r j = v' (eqA.symm r) j := fun j hj =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, fun r => by
      simpa only [Equiv.apply_symm_apply] using hD'_agree j hj (eqA.symm r)⟩
  have hle_B : B + 1 ≤ B :=
    hD'_wt.trans ((Finset.sum_le_sum_of_subset hsub).trans (hsum.trans (hfar c hc_mem)))
  omega

end FoldSoundness

/-! ### Part 2: Out-of-Domain DEEP Quotienting, Degree Restoration, and List Size Bounds -/

section DeepQuotient

/-- **Out-of-domain DEEP polynomial quotient**: divides `p` by the monic linear factor `X - C z`
(`(p - C (p.eval z)) / (X - C z)`), lowering the degree by `1` while recording `p.eval z`. -/
@[expose] noncomputable def deepQuotientPoly {F : Type*} [Field F] (p : F[X]) (z : F) : F[X] :=
  p /ₘ (Polynomial.X - Polynomial.C z)

/-- **Exact polynomial division identity for `deepQuotientPoly`**:
`(X - C z) * deepQuotientPoly p z + C (p.eval z) = p`. -/
theorem mul_deepQuotientPoly_add_eval {F : Type*} [Field F] (p : F[X]) (z : F) :
    (Polynomial.X - Polynomial.C z) * deepQuotientPoly p z + Polynomial.C (p.eval z) = p := by
  rw [deepQuotientPoly, add_comm, ← modByMonic_X_sub_C_eq_C_eval]
  exact modByMonic_add_div p (Polynomial.X - Polynomial.C z)

/-- **Degree drop of `deepQuotientPoly`**: if `deg(p) < k + 1`, then
`deg(deepQuotientPoly p z) < k`. -/
theorem degree_deepQuotientPoly_lt {F : Type*} [Field F] {p : F[X]} {k : ℕ}
    (hp : p.degree < (k + 1 : ℕ)) (z : F) :
    (deepQuotientPoly p z).degree < k := by
  rcases eq_or_ne (deepQuotientPoly p z) 0 with h0 | h0
  · rw [h0, degree_zero]
    exact WithBot.bot_lt_coe k
  · have hm : (Polynomial.X - Polynomial.C z).Monic := monic_X_sub_C z
    have hp0 : p ≠ 0 := fun h => h0 (by simp only [deepQuotientPoly, h, zero_divByMonic])
    have hlt : p.natDegree < k + 1 := (natDegree_lt_iff_degree_lt hp0).mpr hp
    have hle : (Polynomial.X - Polynomial.C z).natDegree ≤ p.natDegree :=
      natDegree_le_natDegree (not_lt.mp ((divByMonic_eq_zero_iff hm).not.mp h0))
    rw [natDegree_X_sub_C] at hle
    rw [degree_eq_natDegree h0, deepQuotientPoly, natDegree_divByMonic p hm, natDegree_X_sub_C,
      Nat.cast_lt]
    omega

/-- **Word-level DEEP quotient oracle**: virtual evaluation word `s ↦ (f s - y) / (α s - z)`
testing simultaneously that `f` comes from a low-degree polynomial `p` and that `p.eval z = y`
([BenSassonGoldbergKoppartySaraf2020]). -/
@[expose] def deepQuotientWord {F ι : Type*} [Field F]
    (α : ι → F) (f : ι → F) (z y : F) : ι → F :=
  fun s => (f s - y) / (α s - z)

/-- On any domain `α : ι → F` avoiding `z`, `deepQuotientWord` of an honest evaluation word
`s ↦ p.eval (α s)` at `y = p.eval z` coincides pointwise with evaluating `deepQuotientPoly p z`. -/
theorem deepQuotientWord_eval_eq {F ι : Type*} [Field F] {α : ι → F} (p : F[X]) {z : F}
    (hz : ∀ s : ι, α s ≠ z) :
    deepQuotientWord α (fun s => p.eval (α s)) z (p.eval z) =
      fun s => (deepQuotientPoly p z).eval (α s) := by
  funext s
  have hsub : α s - z ≠ 0 := sub_ne_zero.mpr (hz s)
  have hid := congrArg (Polynomial.eval (α s)) (mul_deepQuotientPoly_add_eval p z)
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C] at hid
  change (p.eval (α s) - p.eval z) / (α s - z) = (deepQuotientPoly p z).eval (α s)
  rw [div_eq_iff hsub]
  linear_combination -hid

/-- **Reed–Solomon completeness of DEEP quotienting**: if `deg(p) < k + 1` and `z` lies outside the
evaluation domain `α`, then `deepQuotientWord α (fun s => p.eval (α s)) z (p.eval z)` belongs to
`reedSolomon α k`. -/
theorem deepQuotientWord_mem_reedSolomon {F ι : Type*} [Field F] {α : ι → F} {p : F[X]} {k : ℕ}
    (hp : p.degree < (k + 1 : ℕ)) {z : F} (hz : ∀ s : ι, α s ≠ z) :
    deepQuotientWord α (fun s => p.eval (α s)) z (p.eval z) ∈ reedSolomon α k := by
  rw [deepQuotientWord_eval_eq p hz]
  exact eval_mem_reedSolomon α (degree_deepQuotientPoly_lt hp z)

/-- **DEEP correlated-agreement degree restoration and evaluation pinning**: if `z` avoids `α '' D'`
and `deepQuotientWord α f z y` agrees on `D'` with a codeword `v ∈ reedSolomon α k`, then there
exists a polynomial `p` of degree `< k + 1` that evaluates to `y` at `z` and agrees with `f` on all
of `D'`. -/
theorem exists_poly_of_deepQuotientWord_agree {F ι : Type*} [Field F] {α : ι → F}
    {f v : ι → F} {z y : F} {k : ℕ} {D' : Finset ι}
    (hz : ∀ s ∈ D', α s ≠ z) (hv : v ∈ reedSolomon α k)
    (hagree : ∀ s ∈ D', deepQuotientWord α f z y s = v s) :
    ∃ p : F[X], p.degree < (k + 1 : ℕ) ∧ p.eval z = y ∧ ∀ s ∈ D', f s = p.eval (α s) := by
  obtain ⟨q, hq_deg, rfl⟩ := mem_reedSolomon.mp hv
  let p : F[X] := (Polynomial.X - Polynomial.C z) * q + Polynomial.C y
  have hp_deg : p.degree < (k + 1 : ℕ) := by
    refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · rcases eq_or_ne q 0 with rfl | hq0
      · simp only [mul_zero, degree_zero]
        exact WithBot.bot_lt_coe _
      · rw [degree_mul, degree_X_sub_C, degree_eq_natDegree hq0]
        have hlt : q.natDegree < k := (natDegree_lt_iff_degree_lt hq0).mpr hq_deg
        exact_mod_cast (by omega : 1 + q.natDegree < k + 1)
    · exact degree_C_le.trans_lt (WithBot.coe_lt_coe.mpr (Nat.zero_lt_succ k))
  have hp_eval_z : p.eval z = y := by
    simp only [p, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, zero_add]
  refine ⟨p, hp_deg, hp_eval_z, fun s hs => ?_⟩
  have hsub : α s - z ≠ 0 := sub_ne_zero.mpr (hz s hs)
  have hdiv : (f s - y) / (α s - z) = q.eval (α s) := hagree s hs
  rw [div_eq_iff hsub] at hdiv
  simp only [p, eval_add, eval_mul, eval_sub, eval_X, eval_C]
  linear_combination hdiv

/-- Two polynomials of degree `< k` that agree on `D'` of size `≥ k` along an injective domain map
`α : ι → F` are identical. -/
theorem eq_of_degree_lt_of_eval_eq_on {F ι : Type*} [Field F] {α : ι → F}
    (hα : Function.Injective α) {k : ℕ} {D' : Finset ι} (hcard : k ≤ D'.card)
    {p₁ p₂ : F[X]} (hp₁ : p₁.degree < k) (hp₂ : p₂.degree < k)
    (heq : ∀ s ∈ D', p₁.eval (α s) = p₂.eval (α s)) :
    p₁ = p₂ := by
  classical
  by_contra hne
  have hsub0 : p₁ - p₂ ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (p₁ - p₂).degree < k := (degree_sub_le p₁ p₂).trans_lt (max_lt hp₁ hp₂)
  have hnat : (p₁ - p₂).natDegree < k := (natDegree_lt_iff_degree_lt hsub0).mpr hdeg
  have himg : D'.image α ⊆ (p₁ - p₂).roots.toFinset := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨s, hs, rfl⟩
    rw [Multiset.mem_toFinset, mem_roots hsub0, IsRoot.def, eval_sub, sub_eq_zero]
    exact heq s hs
  have hle : D'.card ≤ (p₁ - p₂).natDegree := by
    calc D'.card
        = (D'.image α).card := (Finset.card_image_of_injective D' hα).symm
      _ ≤ (p₁ - p₂).roots.toFinset.card := Finset.card_le_card himg
      _ ≤ (p₁ - p₂).roots.card := Multiset.toFinset_card_le _
      _ ≤ (p₁ - p₂).natDegree := card_roots' _
  omega

/-- Embedding of coefficient vectors `Fin k → F` as polynomials of degree `< k` over a semiring. -/
private noncomputable def coeffVecEquivPoly {F : Type*} [Semiring F] [DecidableEq F] (k : ℕ) :
    (Fin k → F) ↪ F[X] :=
  ⟨Polynomial.ofFn k, Polynomial.injective_ofFn k⟩

/-- Finite list of all polynomials `p : F[X]` of degree `< k` agreeing with `w : ι → F` on at least
`a` coordinates of `α : ι → F`. -/
noncomputable def agreePolyList {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    (α : ι → F) (k : ℕ) (w : ι → F) (a : ℕ) : Finset F[X] :=
  open Classical in
  ((Finset.univ : Finset (Fin k → F)).map (coeffVecEquivPoly k)).filter fun p =>
    a ≤ (Finset.univ.filter fun s : ι => p.eval (α s) = w s).card

/-- Membership in `agreePolyList α k w a` characterizes `p.degree < k` with agreement `≥ a`. -/
@[simp]
theorem mem_agreePolyList {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {α : ι → F} {k a : ℕ} {w : ι → F} {p : F[X]} :
    p ∈ agreePolyList α k w a ↔
      p.degree < k ∧ a ≤ (Finset.univ.filter fun s : ι => p.eval (α s) = w s).card := by
  classical
  simp only [agreePolyList, Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and]
  refine and_congr_left fun _ => ⟨?_, fun hp => ?_⟩
  · rintro ⟨v, rfl⟩
    rw [coeffVecEquivPoly]
    exact Polynomial.ofFn_degree_lt v
  · refine ⟨fun d => p.coeff d.val, ?_⟩
    ext n
    rw [coeffVecEquivPoly]
    change (Polynomial.ofFn k fun d : Fin k => p.coeff d.val).coeff n = p.coeff n
    by_cases hn : n < k
    · exact Polynomial.ofFn_coeff_eq_val_of_lt _ hn
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_lt hn),
        coeff_eq_zero_of_degree_lt (hp.trans_le (Nat.cast_le.mpr (Nat.le_of_not_lt hn)))]

private lemma card_inter_agree_le_sub_one {F ι : Type*} [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι] {α : ι → F} (hα : Function.Injective α) {k : ℕ} (hk : 1 ≤ k)
    (w : ι → F) {p₁ p₂ : F[X]} (hp₁ : p₁.degree < k) (hp₂ : p₂.degree < k) (hne : p₁ ≠ p₂) :
    ((Finset.univ.filter fun s => p₁.eval (α s) = w s) ∩
      (Finset.univ.filter fun s => p₂.eval (α s) = w s)).card ≤ k - 1 := by
  by_contra hgt
  have hge : k ≤ ((Finset.univ.filter fun s => p₁.eval (α s) = w s) ∩
      (Finset.univ.filter fun s => p₂.eval (α s) = w s)).card := by omega
  refine hne (eq_of_degree_lt_of_eval_eq_on hα hge hp₁ hp₂ fun s hs => ?_)
  have hs₁ := (Finset.mem_filter.mp (Finset.mem_inter.mp hs).1).2
  have hs₂ := (Finset.mem_filter.mp (Finset.mem_inter.mp hs).2).2
  exact hs₁.trans hs₂.symm

/-- **Unique-decoding list-size bound (`#agreePolyList ≤ 1`)**: when `Fintype.card ι + k ≤ 2 * a`,
at most one polynomial of degree `< k` agrees with `w` on `≥ a` points. -/
theorem card_agreePolyList_le_one_of_unique {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] {α : ι → F} (hα : Function.Injective α) {k a : ℕ}
    (huniq : Fintype.card ι + k ≤ 2 * a) (w : ι → F) :
    (agreePolyList α k w a).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr fun p₁ hp₁ p₂ hp₂ => ?_
  obtain ⟨hd₁, ha₁⟩ := mem_agreePolyList.mp hp₁
  obtain ⟨hd₂, ha₂⟩ := mem_agreePolyList.mp hp₂
  let S₁ := Finset.univ.filter fun s : ι => p₁.eval (α s) = w s
  let S₂ := Finset.univ.filter fun s : ι => p₂.eval (α s) = w s
  have hunion : (S₁ ∪ S₂).card ≤ Fintype.card ι := card_le_univ _
  have hinter_eq := Finset.card_union_add_card_inter S₁ S₂
  have hge : k ≤ (S₁ ∩ S₂).card := by
    change a ≤ S₁.card at ha₁
    change a ≤ S₂.card at ha₂
    omega
  exact eq_of_degree_lt_of_eval_eq_on hα hge hd₁ hd₂ fun s hs =>
    ((Finset.mem_filter.mp (Finset.mem_inter.mp hs).1).2).trans
      ((Finset.mem_filter.mp (Finset.mem_inter.mp hs).2).2).symm

/-- **Exact integer Johnson list-size bound for `agreePolyList`** ([Johnson1962], via
`Cslib.Code.card_mul_sub_le_of_le_card_of_card_inter_le`): for `1 ≤ k` and
`|ι| * (k - 1) < a ^ 2`, the number of polynomials of degree `< k` agreeing with `w` on at least `a`
points of `α` is at most `(|ι| * (a - (k - 1))) / (a ^ 2 - |ι| * (k - 1))`. -/
theorem card_agreePolyList_le_of_johnson {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] {α : ι → F} (hα : Function.Injective α) {k a : ℕ} (hk : 1 ≤ k)
    (hjohnson : Fintype.card ι * (k - 1) < a ^ 2) (w : ι → F) :
    (agreePolyList α k w a).card ≤
      (Fintype.card ι * (a - (k - 1))) / (a ^ 2 - Fintype.card ι * (k - 1)) := by
  classical
  have hpos : 0 < a ^ 2 - Fintype.card ι * (k - 1) := Nat.sub_pos_of_lt hjohnson
  refine (Nat.le_div_iff_mul_le hpos).mpr ?_
  exact card_mul_sub_le_of_le_card_of_card_inter_le (agreePolyList α k w a)
    (fun p => Finset.univ.filter fun s : ι => p.eval (α s) = w s)
    (fun _ hp => (mem_agreePolyList.mp hp).2)
    (fun _ hp₁ _ hp₂ hne => card_inter_agree_le_sub_one hα hk w
      (mem_agreePolyList.mp hp₁).1 (mem_agreePolyList.mp hp₂).1 hne)

end DeepQuotient

/-! ### Part 3: DEEP-ALI Protocol & Correlated-Agreement Soundness Bridge to Batched FRI -/

section DeepALI

/-- Tight univariate `natDegree` upper bound on a multivariate constraint polynomial
`p : MvPolynomial (Option (Fin M)) F` when `none` substitutes `X` and `some u` substitutes a masked
polynomial of `natDegree ≤ k`. -/
@[expose] noncomputable def constraintDegBound {F : Type*} [CommSemiring F] {M : ℕ}
    (p : MvPolynomial (Option (Fin M)) F) (k : ℕ) : ℕ :=
  p.support.sup fun μ => μ none + k * ∑ u : Fin M, μ (some u)

@[simp]
theorem constraintDegBound_zero {F : Type*} [CommSemiring F] {M : ℕ} (k : ℕ) :
    constraintDegBound (0 : MvPolynomial (Option (Fin M)) F) k = 0 := by
  simp only [constraintDegBound, MvPolynomial.support_zero, Finset.sup_empty, bot_eq_zero']

@[simp]
theorem constraintDegBound_C {F : Type*} [CommSemiring F] {M : ℕ} (c : F) (k : ℕ) :
    constraintDegBound (MvPolynomial.C c : MvPolynomial (Option (Fin M)) F) k = 0 := by
  classical
  rw [constraintDegBound, MvPolynomial.support_C]
  split_ifs <;> simp

@[simp]
theorem constraintDegBound_X_none {F : Type*} [CommSemiring F] [Nontrivial F] {M : ℕ} (k : ℕ) :
    constraintDegBound (MvPolynomial.X none : MvPolynomial (Option (Fin M)) F) k = 1 := by
  rw [constraintDegBound, MvPolynomial.support_X, Finset.sup_singleton]
  simp

@[simp]
theorem constraintDegBound_X_some {F : Type*} [CommSemiring F] [Nontrivial F] {M : ℕ}
    (u : Fin M) (k : ℕ) :
    constraintDegBound (MvPolynomial.X (some u) : MvPolynomial (Option (Fin M)) F) k = k := by
  rw [constraintDegBound, MvPolynomial.support_X, Finset.sup_singleton]
  rw [Finset.sum_eq_single u]
  · simp
  · intro u' _ hu'
    exact Finsupp.single_eq_of_ne ((Option.some_injective _).ne hu')
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ u))

theorem constraintDegBound_add_le {F : Type*} [CommSemiring F] {M : ℕ}
    (p q : MvPolynomial (Option (Fin M)) F) (k : ℕ) :
    constraintDegBound (p + q) k ≤ max (constraintDegBound p k) (constraintDegBound q k) :=
  (Finset.sup_mono MvPolynomial.support_add).trans (le_of_eq Finset.sup_union)

@[simp]
theorem constraintDegBound_neg {F : Type*} [CommRing F] {M : ℕ}
    (p : MvPolynomial (Option (Fin M)) F) (k : ℕ) :
    constraintDegBound (-p) k = constraintDegBound p k := by
  have hsupp : (-p).support = p.support := by
    ext μ
    rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, ← neg_one_smul F p,
      MvPolynomial.coeff_smul, neg_one_smul, neg_ne_zero]
  simp only [constraintDegBound, hsupp]

theorem constraintDegBound_sub_le {F : Type*} [CommRing F] {M : ℕ}
    (p q : MvPolynomial (Option (Fin M)) F) (k : ℕ) :
    constraintDegBound (p - q) k ≤ max (constraintDegBound p k) (constraintDegBound q k) := by
  rw [sub_eq_add_neg, ← constraintDegBound_neg q k]
  exact constraintDegBound_add_le p (-q) k

theorem constraintDegBound_mul_le {F : Type*} [CommSemiring F] {M : ℕ}
    (p q : MvPolynomial (Option (Fin M)) F) (k : ℕ) :
    constraintDegBound (p * q) k ≤ constraintDegBound p k + constraintDegBound q k := by
  rw [constraintDegBound]
  refine Finset.sup_le fun μ hμ => ?_
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at hμ
  obtain ⟨⟨μ₁, μ₂⟩, hanti, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hμ
  have h₁ : μ₁ ∈ p.support := MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hne)
  have h₂ : μ₂ ∈ q.support := MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hne)
  rw [← Finset.mem_antidiagonal.mp hanti]
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, mul_add]
  have hle₁ : μ₁ none + k * ∑ u : Fin M, μ₁ (some u) ≤ constraintDegBound p k :=
    Finset.le_sup (f := fun ν : Option (Fin M) →₀ ℕ => ν none + k * ∑ u : Fin M, ν (some u)) h₁
  have hle₂ : μ₂ none + k * ∑ u : Fin M, μ₂ (some u) ≤ constraintDegBound q k :=
    Finset.le_sup (f := fun ν : Option (Fin M) →₀ ℕ => ν none + k * ∑ u : Fin M, ν (some u)) h₂
  omega

/-- Extract the `j`-th degree-`B` chunk `∑_{t < B} coeff(p, j * B + t) X^t` of `p : F[X]`. -/
@[expose] noncomputable def polyDegreeChunk {F : Type*} [Semiring F] (B : ℕ) (p : F[X])
    (j : ℕ) : F[X] :=
  open Classical in
  Polynomial.ofFn B fun t : Fin B => p.coeff (j * B + t.val)

/-- Every chunk `polyDegreeChunk (k + 1) p j` has degree strictly less than `k + 1`. -/
theorem degree_polyDegreeChunk_lt {F : Type*} [Semiring F] (k : ℕ) (p : F[X]) (j : ℕ) :
    (polyDegreeChunk (k + 1) p j).degree < (k + 1 : ℕ) := by
  classical
  rw [polyDegreeChunk]
  exact Polynomial.ofFn_degree_lt _

/-- **Exact degree-chunk decomposition**: any polynomial `p` of degree `< numChunks * (k + 1)`
equals `∑ j : Fin numChunks, X ^ (j * (k + 1)) * polyDegreeChunk (k + 1) p j`. -/
theorem sum_X_pow_mul_polyDegreeChunk {F : Type*} [Semiring F] {numChunks k : ℕ} {p : F[X]}
    (hp : p.degree < (numChunks * (k + 1) : ℕ)) :
    (∑ j : Fin numChunks, Polynomial.X ^ (j.val * (k + 1)) * polyDegreeChunk (k + 1) p j.val) =
      p := by
  classical
  ext c
  rw [finsetSum_coeff]
  by_cases hc : c < numChunks * (k + 1)
  · have hk1 : 0 < k + 1 := Nat.succ_pos k
    let j₀ : Fin numChunks :=
      ⟨c / (k + 1), (Nat.div_lt_iff_lt_mul hk1).mpr (by simpa only [mul_comm] using hc)⟩
    rw [Finset.sum_eq_single j₀]
    · have hle : j₀.val * (k + 1) ≤ c := by
        simpa only [j₀, mul_comm] using Nat.div_mul_le_self c (k + 1)
      have hrem : c - j₀.val * (k + 1) < k + 1 := by
        have hdiv : j₀.val * (k + 1) + c % (k + 1) = c := by
          dsimp only [j₀]
          rw [mul_comm, Nat.div_add_mod]
        have hmod := Nat.mod_lt c hk1
        omega
      rw [coeff_X_pow_mul', ite_eq_left hle, polyDegreeChunk,
        Polynomial.ofFn_coeff_eq_val_of_lt _ hrem, Nat.add_sub_of_le hle]
    · intro j _ hj_ne
      rw [coeff_X_pow_mul']
      split_ifs with hle
      · have hj_lt : j.val < j₀.val := by
          have hj_le : j.val ≤ c / (k + 1) :=
            (Nat.le_div_iff_mul_le hk1).mpr hle
          exact lt_of_le_of_ne hj_le (Fin.val_ne_of_ne hj_ne)
        have hge : k + 1 ≤ c - j.val * (k + 1) := by
          have hadd_le : j.val * (k + 1) + (k + 1) ≤ c := by
            have hmul : (j.val + 1) * (k + 1) ≤ j₀.val * (k + 1) :=
              Nat.mul_le_mul_right (k + 1) hj_lt
            have hle_c : j₀.val * (k + 1) ≤ c := by
              simpa only [j₀, mul_comm] using Nat.div_mul_le_self c (k + 1)
            nlinarith
          omega
        rw [polyDegreeChunk]
        exact Polynomial.ofFn_coeff_eq_zero_of_ge _ hge
      · rfl
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ j₀))
  · rw [coeff_eq_zero_of_degree_lt (hp.trans_le (Nat.cast_le.mpr (Nat.le_of_not_lt hc)))]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [coeff_X_pow_mul']
    split_ifs with hle
    · have hge : k + 1 ≤ c - j.val * (k + 1) := by
        have hadd_le : j.val * (k + 1) + (k + 1) ≤ c := by
          have hj1 : (j.val + 1) * (k + 1) ≤ numChunks * (k + 1) :=
            Nat.mul_le_mul_right (k + 1) j.isLt
          have hc' : numChunks * (k + 1) ≤ c := Nat.le_of_not_lt hc
          nlinarith
        omega
      rw [polyDegreeChunk]
      exact Polynomial.ofFn_coeff_eq_zero_of_ge _ hge
    · rfl

/-- **Masked Algebraic Constraint System for DEEP-ALI**: specifies smooth FRI parameters `params`
(fixing initial Reed–Solomon dimension `k = params.dim 0` and trace/chunk degree bound `< k + 1`),
`w` trace columns, `M` multiplicative trace mask entries `(maskCol u, maskShift u)`, `c_num`
polynomial constraints `constraintPoly m` with monic zerofier divisors `zerofier m`, `q_extra + 1`
composition-quotient chunks satisfying the tight degree budget `hquot_deg`, and a nonempty
out-of-domain sampling set `oodDom` disjoint from the FRI coset, its inverse mask shifts, and the
zerofier roots. -/
structure DeepALISystem (F : Type) [Field F] (w M c_num q_extra : ℕ) where
  /-- Underlying smooth FRI parameters on coset `cosetEval g ω d 0` of size `2 ^ d`. -/
  params : FRISmoothParams F
  /-- Trace column index read by each mask entry `u : Fin M`. -/
  maskCol : Fin M → Fin w
  /-- Multiplicative domain shift `γ_u` applied to the evaluation point in mask entry `u`. -/
  maskShift : Fin M → F
  /-- Multivariate polynomial constraint `C_m(X, Y_0, …, Y_{M-1})` for `m : Fin c_num`. -/
  constraintPoly : Fin c_num → MvPolynomial (Option (Fin M)) F
  /-- Monic zerofier / vanishing divisor `Z_m(X)` for constraint `m : Fin c_num`. -/
  zerofier : Fin c_num → F[X]
  /-- Non-emptiness / monicity of every constraint zerofier. -/
  hzerofier_monic : ∀ m : Fin c_num, (zerofier m).Monic
  /-- Tight quotient degree budget ensuring every valid witness quotient fits in `q_extra + 1`
  chunks of degree `< params.dim 0 + 1`. -/
  hquot_deg : ∀ m : Fin c_num,
    constraintDegBound (constraintPoly m) (params.dim 0) <
      (zerofier m).natDegree + (q_extra + 1) * (params.dim 0 + 1)
  /-- Finite out-of-domain sampling set ("outside the box"). -/
  oodDom : Finset F
  /-- `oodDom` is nonempty. -/
  hood_nonempty : oodDom.Nonempty
  /-- `oodDom` avoids the FRI evaluation coset `L₀`. -/
  hood_coset : ∀ z ∈ oodDom, ∀ s : Fin (2 ^ params.d),
    cosetEval params.g params.ω params.d 0 s ≠ z
  /-- Every shifted out-of-domain query `maskShift u * z` also avoids `L₀`. -/
  hood_mask : ∀ z ∈ oodDom, ∀ u : Fin M, ∀ s : Fin (2 ^ params.d),
    cosetEval params.g params.ω params.d 0 s ≠ maskShift u * z
  /-- No zerofier vanishes on `oodDom`. -/
  hood_zerofier : ∀ z ∈ oodDom, ∀ m : Fin c_num, (zerofier m).eval z ≠ 0

namespace DeepALISystem

variable {F : Type} [Field F] {w M c_num q_extra : ℕ}

/-- Initial FRI evaluation coset `L₀ : Fin (2 ^ d) → F` of `sys`. -/
@[expose] def evalDom (sys : DeepALISystem F w M c_num q_extra) : Fin (2 ^ sys.params.d) → F :=
  cosetEval sys.params.g sys.params.ω sys.params.d 0

/-- Injectivity of `sys.evalDom`. -/
theorem evalDom_injective (sys : DeepALISystem F w M c_num q_extra) :
    Function.Injective sys.evalDom :=
  cosetEval_injective sys.params.hg sys.params.hω (Nat.zero_le sys.params.d)

/-- Pointwise evaluation `C_m(x, y_mask)` of constraint `m` at point `x` and mask values `y_mask`.
-/
@[expose] noncomputable def evalConstraintPoint (sys : DeepALISystem F w M c_num q_extra)
    (m : Fin c_num) (x : F) (y_mask : Fin M → F) : F :=
  MvPolynomial.eval (Option.elim' x y_mask) (sys.constraintPoly m)

/-- Univariate polynomial `C_m(X, P_{maskCol 0}(maskShift 0 · X), …)` obtained by substituting the
shifted trace polynomials `P : Fin w → F[X]` into constraint `m`. -/
@[expose] noncomputable def evalMaskPoly (sys : DeepALISystem F w M c_num q_extra)
    (m : Fin c_num) (P : Fin w → F[X]) : F[X] :=
  MvPolynomial.eval₂ Polynomial.C
    (Option.elim' Polynomial.X fun u =>
      (P (sys.maskCol u)).comp (Polynomial.C (sys.maskShift u) * Polynomial.X))
    (sys.constraintPoly m)

/-- Evaluating `sys.evalMaskPoly m P` at `x : F` coincides with `sys.evalConstraintPoint m x` on the
shifted evaluations `u ↦ (P (maskCol u)).eval (maskShift u * x)`. -/
theorem eval_evalMaskPoly (sys : DeepALISystem F w M c_num q_extra)
    (m : Fin c_num) (P : Fin w → F[X]) (x : F) :
    (sys.evalMaskPoly m P).eval x =
      sys.evalConstraintPoint m x (fun u => (P (sys.maskCol u)).eval (sys.maskShift u * x)) := by
  change Polynomial.eval₂RingHom (RingHom.id F) x (sys.evalMaskPoly m P) = _
  rw [evalMaskPoly, MvPolynomial.hom_eval₂, evalConstraintPoint, MvPolynomial.eval]
  congr 1
  · ext c
    simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_id, eval_C, RingHom.id_apply]
  · funext v
    cases v <;>
      simp only [Option.elim'_none, Option.elim'_some, coe_eval₂RingHom, eval₂_id, eval_X,
        eval_comp, eval_mul, eval_C]

/-- **Tight univariate degree bound for `evalMaskPoly`**: when every `P i` has degree
`< sys.params.dim 0 + 1`, `(sys.evalMaskPoly m P).natDegree` is at most
`constraintDegBound (sys.constraintPoly m) (sys.params.dim 0)`. -/
theorem natDegree_evalMaskPoly_le (sys : DeepALISystem F w M c_num q_extra)
    (m : Fin c_num) {P : Fin w → F[X]}
    (hP : ∀ i : Fin w, (P i).degree < (sys.params.dim 0 + 1 : ℕ)) :
    (sys.evalMaskPoly m P).natDegree ≤
      constraintDegBound (sys.constraintPoly m) (sys.params.dim 0) := by
  classical
  have hcomp_le (u : Fin M) :
      ((P (sys.maskCol u)).comp
        (Polynomial.C (sys.maskShift u) * Polynomial.X)).natDegree ≤ sys.params.dim 0 := by
    refine (natDegree_comp_le).trans ?_
    have hlin : (Polynomial.C (sys.maskShift u) * Polynomial.X).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans (by simp only [natDegree_X, le_rfl])
    have hPu : (P (sys.maskCol u)).natDegree ≤ sys.params.dim 0 := by
      rcases eq_or_ne (P (sys.maskCol u)) 0 with h0 | h0
      · simp only [h0, natDegree_zero, Nat.zero_le]
      · exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt h0).mpr (hP (sys.maskCol u)))
    calc (P (sys.maskCol u)).natDegree *
          (Polynomial.C (sys.maskShift u) * Polynomial.X).natDegree
        ≤ sys.params.dim 0 * 1 := Nat.mul_le_mul hPu hlin
      _ = sys.params.dim 0 := mul_one _
  rw [evalMaskPoly, MvPolynomial.eval₂_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun μ hμ => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_prod_le _ _).trans ?_)
  let termPoly : Option (Fin M) → F[X] := Option.elim' Polynomial.X fun u =>
    (P (sys.maskCol u)).comp (Polynomial.C (sys.maskShift u) * Polynomial.X)
  have hsub : (∑ v ∈ μ.support, (termPoly v ^ μ v).natDegree) ≤
      ∑ v : Option (Fin M), (termPoly v ^ μ v).natDegree :=
    Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
  refine hsub.trans ?_
  rw [Fintype.sum_option]
  simp only [termPoly, Option.elim'_none, Option.elim'_some, natDegree_X_pow]
  have hmask_sum : (∑ u : Fin M,
      (((P (sys.maskCol u)).comp
        (Polynomial.C (sys.maskShift u) * Polynomial.X)) ^ μ (some u)).natDegree) ≤
      sys.params.dim 0 * ∑ u : Fin M, μ (some u) := by
    calc _ ≤ ∑ u : Fin M, μ (some u) * sys.params.dim 0 :=
          Finset.sum_le_sum fun u _ =>
            Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hcomp_le u))
      _ = (∑ u : Fin M, μ (some u)) * sys.params.dim 0 := (Finset.sum_mul _ _ _).symm
      _ = sys.params.dim 0 * ∑ u : Fin M, μ (some u) := mul_comm _ _
  exact (Nat.add_le_add_left hmask_sum _).trans
    (Finset.le_sup (f := fun μ : Option (Fin M) →₀ ℕ =>
      μ none + sys.params.dim 0 * ∑ u : Fin M, μ (some u)) hμ)

private lemma prod_X_sub_C_dvd_iff_forall_eval_eq_zero
    (H : Finset F) (q : F[X]) :
    (∏ x ∈ H, (Polynomial.X - Polynomial.C x)) ∣ q ↔ ∀ x ∈ H, q.eval x = 0 := by
  classical
  induction H using Finset.induction_on generalizing q with
  | empty =>
    simp only [Finset.prod_empty, one_dvd, Finset.notMem_empty, IsEmpty.forall_iff, implies_true]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.forall_mem_insert]
    refine ⟨fun hdvd => ⟨?_, ?_⟩, fun ⟨ha0, hs0⟩ => ?_⟩
    · exact dvd_iff_isRoot.mp (dvd_of_mul_right_dvd hdvd)
    · exact (ih q).mp (dvd_of_mul_left_dvd hdvd)
    · obtain ⟨q', rfl⟩ := dvd_iff_isRoot.mpr ha0
      refine mul_dvd_mul_left (Polynomial.X - Polynomial.C a) ((ih q').mpr fun x hx => ?_)
      have hxa : x - a ≠ 0 := sub_ne_zero.mpr fun h => ha (h ▸ hx)
      have hev := hs0 x hx
      simp only [eval_mul, eval_sub, eval_X, eval_C] at hev
      exact (mul_eq_zero.mp hev).resolve_left hxa

/-- **Pointwise root-set characterization of zerofier divisibility**: when `zerofier m =
∏ x ∈ H, (X - C x)` for a subset `H : Finset F`, divisibility `zerofier m ∣ evalMaskPoly m P` holds
if and only if the algebraic constraint vanishes at every `x ∈ H`. -/
theorem prod_X_sub_C_dvd_evalMaskPoly_iff
    (sys : DeepALISystem F w M c_num q_extra) (m : Fin c_num) (H : Finset F)
    (hZ : sys.zerofier m = ∏ x ∈ H, (Polynomial.X - Polynomial.C x)) (P : Fin w → F[X]) :
    sys.zerofier m ∣ sys.evalMaskPoly m P ↔
      ∀ x ∈ H,
        sys.evalConstraintPoint m x (fun u => (P (sys.maskCol u)).eval (sys.maskShift u * x)) =
          0 := by
  rw [hZ, prod_X_sub_C_dvd_iff_forall_eval_eq_zero]
  exact forall₂_congr fun x _ => by rw [sys.eval_evalMaskPoly]

/-- A polynomial tuple `P : Fin w → F[X]` is a valid witness for `sys` when each `P i` has degree
`< params.dim 0 + 1` and every constraint `evalMaskPoly m P` is divisible by `zerofier m`. -/
@[expose] def IsValidWitness (sys : DeepALISystem F w M c_num q_extra) (P : Fin w → F[X]) : Prop :=
  (∀ i : Fin w, (P i).degree < (sys.params.dim 0 + 1 : ℕ)) ∧
    ∀ m : Fin c_num, sys.zerofier m ∣ sys.evalMaskPoly m P

/-- Algebraic satisfiability of `sys`: existence of a low-degree polynomial tuple satisfying all
constraints. -/
@[expose] def Satisfiable (sys : DeepALISystem F w M c_num q_extra) : Prop :=
  ∃ P : Fin w → F[X], sys.IsValidWitness P

/-- Explicit algebraic-linking degree bound
`D_ALI = (q_extra + 1) * (params.dim 0 + 1) - 1 + ∑ m, (zerofier m).natDegree` governing the
out-of-domain DEEP soundness error. -/
@[expose] def linkDegBound (sys : DeepALISystem F w M c_num q_extra) : ℕ :=
  (q_extra + 1) * (sys.params.dim 0 + 1) - 1 + ∑ m : Fin c_num, (sys.zerofier m).natDegree

/-- Exact integer Johnson list-size bound `max 1 ((2 ^ d * (⌈α * 2 ^ d⌉₊ - k)) / ((⌈α * 2 ^ d⌉₊) ^ 2
- 2 ^ d * k))` for degree-`< k + 1` trace and quotient-chunk polynomials at relative agreement
threshold `α`. -/
@[expose] noncomputable def johnsonListBound (sys : DeepALISystem F w M c_num q_extra)
    (α : ℝ) : ℕ :=
  let n : ℕ := 2 ^ sys.params.d
  let k : ℕ := sys.params.dim 0
  let a : ℕ := ⌈α * (n : ℝ)⌉₊
  max 1 ((n * (a - k)) / (a ^ 2 - n * k))

end DeepALISystem

/-- Prover's out-of-domain evaluation claims in DEEP-ALI: `maskVals u` claims
`P_{maskCol u}(maskShift u * z)` and `quotVals j` claims `Q_j(z)`. -/
@[ext] structure DeepALIOpening (F : Type) (M q_extra : ℕ) where
  /-- Claimed evaluations at the `M` shifted out-of-domain points `maskShift u * z`. -/
  maskVals : Fin M → F
  /-- Claimed evaluations of the `q_extra + 1` composition-quotient chunks at `z`. -/
  quotVals : Fin (q_extra + 1) → F

namespace DeepALISystem

variable {F : Type} [Field F] {w M c_num q_extra : ℕ}

/-- Boolean algebraic linking check at out-of-domain challenge `z` and constraint weights `β`:
verifies `∑ m, β_m * C_m(z, maskVals) / Z_m(z) = ∑ j, z ^ (j * (k + 1)) * quotVals j`. -/
@[expose] noncomputable def linkCheck [DecidableEq F]
    (sys : DeepALISystem F w M c_num q_extra)
    (β : Fin c_num → F) (z : F) (op : DeepALIOpening F M q_extra) : Bool :=
  decide
    ((∑ m : Fin c_num,
        β m * (sys.evalConstraintPoint m z op.maskVals / (sys.zerofier m).eval z)) =
      ∑ j : Fin (q_extra + 1), z ^ (j.val * (sys.params.dim 0 + 1)) * op.quotVals j)

/-- Virtual `(M + q_extra)`-term `FRIBatchStmt` produced by DEEP quotienting:
* `base` is the `0`-th composition-quotient chunk's DEEP word
  `(Q_orc 0 s - quotVals 0) / (α s - z)`.
* `terms` packs the `M` mask DEEP words `(T (maskCol u) s - maskVals u) / (α s - maskShift u * z)`
  followed by the `q_extra` higher composition-quotient DEEP words. -/
@[expose] def batchStmt (sys : DeepALISystem F w M c_num q_extra)
    (T : Fin w → OracleTable sys.params.d F)
    (Q_orc : Fin (q_extra + 1) → OracleTable sys.params.d F)
    (z : F) (op : DeepALIOpening F M q_extra) :
    FRIBatchStmt F sys.params.d (M + q_extra) where
  base := deepQuotientWord sys.evalDom (Q_orc 0) z (op.quotVals 0)
  terms := Fin.addCases
    (fun u : Fin M =>
      deepQuotientWord sys.evalDom (T (sys.maskCol u)) (sys.maskShift u * z) (op.maskVals u))
    (fun j : Fin q_extra =>
      deepQuotientWord sys.evalDom (Q_orc j.succ) z (op.quotVals j.succ))

end DeepALISystem

/-- Adaptive (possibly randomized) cheating prover for `DeepALISystem`:
1. commits trace evaluation tables `T : Fin w → OracleTable d F`,
2. upon receiving random constraint-linking scalars `β : Fin c_num → F`, commits
   composition-quotient chunk tables `Q_orc : Fin (q_extra + 1) → OracleTable d F`, and
3. upon receiving out-of-domain sample `z ∈ oodDom`, outputs claimed evaluations `DeepALIOpening`
   together with an adaptive interactive prover for `friSmoothBatchIOP`. -/
structure DeepALIProver {F : Type} [Field F] {w M c_num q_extra : ℕ}
    (sys : DeepALISystem F w M c_num q_extra) where
  /-- Round-0 randomized trace oracle commitment. -/
  commitTrace : PMF (Fin w → OracleTable sys.params.d F)
  /-- Round-1 adaptive randomized composition-quotient chunk commitment given `(T, β)`. -/
  commitQuot :
    (Fin w → OracleTable sys.params.d F) → (Fin c_num → F) →
      PMF (Fin (q_extra + 1) → OracleTable sys.params.d F)
  /-- Round-2 adaptive randomized OOD opening and batched FRI continuation given `(T, β, Q_orc, z)`.
  -/
  openOOD :
    (Fin w → OracleTable sys.params.d F) → (Fin c_num → F) →
      (Fin (q_extra + 1) → OracleTable sys.params.d F) → F →
      PMF (DeepALIOpening F M q_extra ×
        InteractiveIOPProver sys.params.d F
          (FRIBatchChal F sys.params.d sys.params.q (M + q_extra)))

/-- **Interactive DEEP-ALI + Smooth Batched FRI Game**: runs `adv` across trace commitment, uniform
constraint linking `β : Fin c_num → F`, quotient commitment, uniform out-of-domain sampling
`z ∈ sys.oodDom`, the algebraic linking check `sys.linkCheck β z op`, and the `(m + 2)`-round
batched smooth FRI IOP `friSmoothBatchIOP sys.params (M + q_extra)`. -/
@[expose] noncomputable def deepALIGame {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {w M c_num q_extra : ℕ}
    (sys : DeepALISystem F w M c_num q_extra) (adv : DeepALIProver sys) : PMF Bool :=
  adv.commitTrace.bind fun T =>
    (PMF.uniformOfFintype (Fin c_num → F)).bind fun β =>
      (adv.commitQuot T β).bind fun Q_orc =>
        (PMF.uniformOfFinset sys.oodDom sys.hood_nonempty).bind fun z =>
          (adv.openOOD T β Q_orc z).bind fun ⟨op, P_fri⟩ =>
            if sys.linkCheck β z op = true then
              iopInteractiveGame (friSmoothBatchIOP sys.params (M + q_extra))
                (sys.batchStmt T Q_orc z op) P_fri
            else
              PMF.pure false

/-- Honest combined composition-quotient polynomial
`∑ m, C (β m) * (evalMaskPoly m P /ₘ zerofier m)` formed from a polynomial tuple
`P : Fin w → F[X]`. -/
@[expose] noncomputable def honestCombinedQuot {F : Type} [Field F] {w M c_num q_extra : ℕ}
    (sys : DeepALISystem F w M c_num q_extra) (P : Fin w → F[X]) (β : Fin c_num → F) : F[X] :=
  ∑ m : Fin c_num, Polynomial.C (β m) * (sys.evalMaskPoly m P /ₘ sys.zerofier m)

private lemma degree_honestCombinedQuot_lt {F : Type} [Field F] {w M c_num q_extra : ℕ}
    (sys : DeepALISystem F w M c_num q_extra) {P : Fin w → F[X]}
    (hP : sys.IsValidWitness P) (β : Fin c_num → F) :
    (honestCombinedQuot sys P β).degree <
      ((q_extra + 1) * (sys.params.dim 0 + 1) : ℕ) := by
  refine (degree_sum_le _ _).trans_lt ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro m _
  refine (degree_mul_le _ _).trans_lt (lt_of_le_of_lt (add_le_of_nonpos_left degree_C_le) ?_)
  let Q_m := sys.evalMaskPoly m P /ₘ sys.zerofier m
  rcases eq_or_ne Q_m 0 with h0 | h0
  · simp only [Q_m] at h0
    rw [h0, degree_zero]
    exact WithBot.bot_lt_coe _
  · have hm := sys.hzerofier_monic m
    have hle_deg : (sys.zerofier m).natDegree ≤ (sys.evalMaskPoly m P).natDegree :=
      natDegree_le_natDegree (not_lt.mp ((divByMonic_eq_zero_iff hm).not.mp h0))
    have hbound := (sys.natDegree_evalMaskPoly_le m hP.1).trans_lt (sys.hquot_deg m)
    rw [degree_eq_natDegree h0, natDegree_divByMonic _ hm, Nat.cast_lt]
    omega

/-- **Honest DEEP-ALI prover** given any polynomial tuple `P : Fin w → F[X]`: commits the coset
evaluations of `P`, commits the `(q_extra + 1)` degree-`(k + 1)` chunks of `honestCombinedQuot`,
opens their exact evaluations at `z`, and executes the honest causal `friSmoothBatchIOP` prover. -/
@[expose] noncomputable def honestDeepALIProver {F : Type} [Field F] [DecidableEq F]
    {w M c_num q_extra : ℕ}
    (sys : DeepALISystem F w M c_num q_extra) (P : Fin w → F[X]) : DeepALIProver sys where
  commitTrace := PMF.pure fun i s => (P i).eval (sys.evalDom s)
  commitQuot _ β :=
    let Q_comb := honestCombinedQuot sys P β
    PMF.pure fun j s =>
      (polyDegreeChunk (sys.params.dim 0 + 1) Q_comb j.val).eval (sys.evalDom s)
  openOOD T β Q_orc z :=
    let Q_comb := honestCombinedQuot sys P β
    let op : DeepALIOpening F M q_extra :=
      { maskVals := fun u => (P (sys.maskCol u)).eval (sys.maskShift u * z)
        quotVals := fun j =>
          (polyDegreeChunk (sys.params.dim 0 + 1) Q_comb j.val).eval z }
    let stmt := sys.batchStmt T Q_orc z op
    PMF.pure
      (op, InteractiveIOPProver.ofCausal fun r hist =>
        (friSmoothBatchIOP sys.params (M + q_extra)).proveRound r stmt () hist)

private lemma pmf_bind_eq_const_of_support {α β : Type*} (p : PMF α) (f : α → PMF β) (q : PMF β)
    (hf : ∀ a ∈ p.support, f a = q) :
    p.bind f = q := by
  rw [← PMF.bindOnSupport_eq_bind]
  have heq : (fun a (_ : a ∈ p.support) => f a) = fun _ _ => q :=
    funext fun a => funext fun ha => hf a ha
  rw [heq, PMF.bindOnSupport_eq_bind, PMF.bind_const]

/-- **Perfect completeness of DEEP-ALI + Smooth Batched FRI**: for every valid witness `P`
(`sys.IsValidWitness P`), `deepALIGame sys (honestDeepALIProver sys P)` outputs `true` with
probability `1`. -/
theorem deepALIGame_honest_eq_pure_true {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {w M c_num q_extra : ℕ}
    (sys : DeepALISystem F w M c_num q_extra) {P : Fin w → F[X]} (hP : sys.IsValidWitness P) :
    deepALIGame sys (honestDeepALIProver sys P) = PMF.pure true := by
  rw [deepALIGame, honestDeepALIProver]
  dsimp only
  rw [PMF.pure_bind]
  refine pmf_bind_eq_const_of_support _ _ _ fun β _ => ?_
  rw [PMF.pure_bind]
  refine pmf_bind_eq_const_of_support _ _ _ fun z hz_supp => ?_
  have hz : z ∈ sys.oodDom := (PMF.mem_support_uniformOfFinset_iff _ _).mp hz_supp
  rw [PMF.pure_bind]
  dsimp only
  let T₀ : Fin w → OracleTable sys.params.d F := fun i s => (P i).eval (sys.evalDom s)
  let Q_comb := honestCombinedQuot sys P β
  let Q_orc : Fin (q_extra + 1) → OracleTable sys.params.d F :=
    fun j s => (polyDegreeChunk (sys.params.dim 0 + 1) Q_comb j.val).eval (sys.evalDom s)
  let op : DeepALIOpening F M q_extra :=
    { maskVals := fun u => (P (sys.maskCol u)).eval (sys.maskShift u * z)
      quotVals := fun j =>
        (polyDegreeChunk (sys.params.dim 0 + 1) Q_comb j.val).eval z }
  have hlink : sys.linkCheck β z op = true := by
    simp only [DeepALISystem.linkCheck, decide_eq_true_eq, op]
    have hsum_chunks := congrArg (Polynomial.eval z)
      (sum_X_pow_mul_polyDegreeChunk (degree_honestCombinedQuot_lt sys hP β))
    simp only [eval_finsetSum, eval_mul, eval_pow, eval_X] at hsum_chunks
    rw [hsum_chunks, honestCombinedQuot, eval_finsetSum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hm := sys.hzerofier_monic m
    have hmod0 : sys.evalMaskPoly m P %ₘ sys.zerofier m = 0 :=
      (modByMonic_eq_zero_iff_dvd hm).mpr (hP.2 m)
    have hdiv_id := modByMonic_add_div (sys.evalMaskPoly m P) (sys.zerofier m)
    rw [hmod0, zero_add] at hdiv_id
    have hev := congrArg (Polynomial.eval z) hdiv_id
    rw [eval_mul, sys.eval_evalMaskPoly] at hev
    have hZ_ne : (sys.zerofier m).eval z ≠ 0 := sys.hood_zerofier z hz m
    rw [eval_mul, eval_C]
    congr 1
    rw [div_eq_iff hZ_ne, mul_comm, hev]
  have hrel : sys.params.batchCompletenessRel (M + q_extra)
      (sys.batchStmt T₀ Q_orc z op) () := by
    refine ⟨?_, ?_⟩
    · exact deepQuotientWord_mem_reedSolomon (degree_polyDegreeChunk_lt _ Q_comb 0)
        (sys.hood_coset z hz)
    · intro idx
      refine Fin.addCases (fun u => ?_) (fun j => ?_) idx
      · simp only [DeepALISystem.batchStmt, Fin.addCases_left]
        exact deepQuotientWord_mem_reedSolomon (hP.1 (sys.maskCol u))
          (sys.hood_mask z hz u)
      · simp only [DeepALISystem.batchStmt, Fin.addCases_right]
        exact deepQuotientWord_mem_reedSolomon
          (degree_polyDegreeChunk_lt _ Q_comb j.succ.val)
          (sys.hood_coset z hz)
  rw [ite_eq_left hlink, iopInteractiveGame_ofCausal_eq]
  have hconst : (fun chals : Fin (sys.params.m + 2) →
      FRIBatchChal F sys.params.d sys.params.q (M + q_extra) =>
      iopVerify (friSmoothBatchIOP sys.params (M + q_extra))
        (sys.batchStmt T₀ Q_orc z op) chals
        (fun j => (friSmoothBatchIOP sys.params (M + q_extra)).proveRound j
          (sys.batchStmt T₀ Q_orc z op) ()
          fun i => chals ⟨i.val, lt_trans i.isLt j.isLt⟩)) =
      Function.const _ true :=
    funext fun chals => friSmoothBatchIOP_complete sys.params (M + q_extra) _ () hrel chals
  rw [hconst, PMF.map_const]

/-- Candidate polynomial list for trace column `i : Fin w` at agreement threshold `a`: equals
`agreePolyList sys.evalDom (k + 1) (T i) a` when column `i` is referenced by at least one mask
entry, and `{0}` otherwise. -/
noncomputable def traceColCandList {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {w M c_num q_extra : ℕ} (sys : DeepALISystem F w M c_num q_extra)
    (T : Fin w → OracleTable sys.params.d F) (a : ℕ) (i : Fin w) : Finset F[X] :=
  if ∃ u : Fin M, sys.maskCol u = i then
    agreePolyList sys.evalDom (sys.params.dim 0 + 1) (T i) a
  else
    {0}

private lemma card_traceColCandList_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {w M c_num q_extra : ℕ} (sys : DeepALISystem F w M c_num q_extra)
    (T : Fin w → OracleTable sys.params.d F) {a L : ℕ} (hL1 : 1 ≤ L)
    (hcard : ∀ i : Fin w,
      (agreePolyList sys.evalDom (sys.params.dim 0 + 1) (T i) a).card ≤ L)
    (i : Fin w) :
    (traceColCandList sys T a i).card ≤ L := by
  unfold traceColCandList
  split_ifs
  · exact hcard i
  · simp only [Finset.card_singleton, hL1]

/-- **Deterministic correlated-agreement extraction bridge from `batchStmt ∈ batchProximityLang` to
candidate trace and quotient-chunk polynomials**: whenever `z ∈ sys.oodDom`,
`sys.params.dim 0 + 1 ≤ 2 ^ d - e`, and `sys.batchStmt T Q_orc z op ∈
sys.params.batchProximityLang (M + q_extra) e`, there exist:
1. a trace polynomial tuple `P : Fin w → F[X]` with `P i ∈ traceColCandList sys T (2 ^ d - e) i`,
   `deg(P i) < k + 1`, and `(P (maskCol u)).eval (maskShift u * z) = op.maskVals u` for all `u`, and
2. a quotient-chunk tuple `Q_poly : Fin (q_extra + 1) → F[X]` with
   `Q_poly j ∈ agreePolyList sys.evalDom (k + 1) (Q_orc j) (2 ^ d - e)`, `deg(Q_poly j) < k + 1`,
   and `(Q_poly j).eval z = op.quotVals j` for all `j`. -/
theorem exists_polys_of_batchStmt_mem_proximityLang {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {w M c_num q_extra e : ℕ}
    (sys : DeepALISystem F w M c_num q_extra)
    {T : Fin w → OracleTable sys.params.d F}
    {Q_orc : Fin (q_extra + 1) → OracleTable sys.params.d F}
    {z : F} (hz : z ∈ sys.oodDom) {op : DeepALIOpening F M q_extra}
    (hinterp_card : sys.params.dim 0 + 1 ≤ 2 ^ sys.params.d - e)
    (hmem : sys.batchStmt T Q_orc z op ∈ sys.params.batchProximityLang (M + q_extra) e) :
    ∃ (P : Fin w → F[X]) (Q_poly : Fin (q_extra + 1) → F[X]),
      P ∈ Fintype.piFinset (traceColCandList sys T (2 ^ sys.params.d - e)) ∧
      Q_poly ∈ Fintype.piFinset
        (fun j => agreePolyList sys.evalDom (sys.params.dim 0 + 1) (Q_orc j)
          (2 ^ sys.params.d - e)) ∧
      (∀ i : Fin w, (P i).degree < (sys.params.dim 0 + 1 : ℕ)) ∧
      (∀ j : Fin (q_extra + 1), (Q_poly j).degree < (sys.params.dim 0 + 1 : ℕ)) ∧
      (∀ u : Fin M, (P (sys.maskCol u)).eval (sys.maskShift u * z) = op.maskVals u) ∧
      (∀ j : Fin (q_extra + 1), (Q_poly j).eval z = op.quotVals j) := by
  classical
  obtain ⟨D', hD'_card, v₀, hv₀, v, hv, hagree⟩ := hmem
  have hQ0 : ∃ q₀ : F[X], q₀.degree < (sys.params.dim 0 + 1 : ℕ) ∧ q₀.eval z = op.quotVals 0 ∧
      ∀ s ∈ D', Q_orc 0 s = q₀.eval (sys.evalDom s) :=
    exists_poly_of_deepQuotientWord_agree (fun s _ => sys.hood_coset z hz s) hv₀
      (fun s hs => (hagree s hs).1)
  have hQsucc : ∀ j : Fin q_extra, ∃ qj : F[X],
      qj.degree < (sys.params.dim 0 + 1 : ℕ) ∧ qj.eval z = op.quotVals j.succ ∧
      ∀ s ∈ D', Q_orc j.succ s = qj.eval (sys.evalDom s) := fun j =>
    exists_poly_of_deepQuotientWord_agree (fun s _ => sys.hood_coset z hz s)
      (hv (Fin.natAdd M j)) fun s hs => by
        have h := (hagree s hs).2 (Fin.natAdd M j)
        simpa only [DeepALISystem.batchStmt, Fin.addCases_right] using h
  have hmask : ∀ u : Fin M, ∃ pu : F[X],
      pu.degree < (sys.params.dim 0 + 1 : ℕ) ∧
      pu.eval (sys.maskShift u * z) = op.maskVals u ∧
      ∀ s ∈ D', T (sys.maskCol u) s = pu.eval (sys.evalDom s) := fun u =>
    exists_poly_of_deepQuotientWord_agree (fun s _ => sys.hood_mask z hz u s)
      (hv (Fin.castAdd q_extra u)) fun s hs => by
        have h := (hagree s hs).2 (Fin.castAdd q_extra u)
        simpa only [DeepALISystem.batchStmt, Fin.addCases_left] using h
  let Q_poly : Fin (q_extra + 1) → F[X] :=
    Fin.cases hQ0.choose fun j => (hQsucc j).choose
  let P : Fin w → F[X] := fun i =>
    if hi : ∃ u : Fin M, sys.maskCol u = i then (hmask hi.choose).choose else 0
  have hQ_deg : ∀ j : Fin (q_extra + 1), (Q_poly j).degree < (sys.params.dim 0 + 1 : ℕ) :=
    Fin.cases hQ0.choose_spec.1 fun j => (hQsucc j).choose_spec.1
  have hQ_eval : ∀ j : Fin (q_extra + 1), (Q_poly j).eval z = op.quotVals j :=
    Fin.cases hQ0.choose_spec.2.1 fun j => (hQsucc j).choose_spec.2.1
  have hQ_ag : ∀ (j : Fin (q_extra + 1)) (s : Fin (2 ^ sys.params.d)), s ∈ D' →
      Q_orc j s = (Q_poly j).eval (sys.evalDom s) :=
    Fin.cases hQ0.choose_spec.2.2 fun j => (hQsucc j).choose_spec.2.2
  have hP_deg : ∀ i : Fin w, (P i).degree < (sys.params.dim 0 + 1 : ℕ) := fun i => by
    dsimp only [P]
    split_ifs with hi
    · exact (hmask hi.choose).choose_spec.1
    · rw [degree_zero]
      exact WithBot.bot_lt_coe _
  have hP_mask_eq : ∀ u : Fin M, P (sys.maskCol u) = (hmask u).choose := fun u => by
    have hi : ∃ u' : Fin M, sys.maskCol u' = sys.maskCol u := ⟨u, rfl⟩
    have hP_def : P (sys.maskCol u) = (hmask hi.choose).choose := dite_eq_left hi
    rw [hP_def]
    refine eq_of_degree_lt_of_eval_eq_on sys.evalDom_injective
      (hinterp_card.trans hD'_card) (hmask hi.choose).choose_spec.1 (hmask u).choose_spec.1
      fun s hs => ?_
    have h₁ := (hmask hi.choose).choose_spec.2.2 s hs
    have h₂ := (hmask u).choose_spec.2.2 s hs
    have hcol : T (sys.maskCol hi.choose) s = T (sys.maskCol u) s :=
      congrArg (fun c => T c s) hi.choose_spec
    exact h₁.symm.trans (hcol.trans h₂)
  refine ⟨P, Q_poly, ?_, ?_, hP_deg, hQ_deg,
    fun u => by rw [hP_mask_eq u]; exact (hmask u).choose_spec.2.1, hQ_eval⟩
  · rw [Fintype.mem_piFinset]
    intro i
    dsimp only [traceColCandList, P]
    split_ifs with hi
    · rw [mem_agreePolyList]
      refine ⟨(hmask hi.choose).choose_spec.1, hD'_card.trans (Finset.card_le_card fun s hs => ?_)⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ s, ?_⟩
      have h := (hmask hi.choose).choose_spec.2.2 s hs
      have hcol : T (sys.maskCol hi.choose) s = T i s :=
        congrArg (fun c => T c s) hi.choose_spec
      exact h.symm.trans hcol
    · exact Finset.mem_singleton_self 0
  · rw [Fintype.mem_piFinset]
    intro j
    rw [mem_agreePolyList]
    refine ⟨hQ_deg j, hD'_card.trans (Finset.card_le_card fun s hs => ?_)⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, (hQ_ag j s hs).symm⟩

/-- Full zerofier product `∏ m, sys.zerofier m`. -/
private noncomputable def zerofierProd {F : Type} [Field F] {w M c_num q_extra : ℕ}
    (sys : DeepALISystem F w M c_num q_extra) : F[X] :=
  ∏ m : Fin c_num, sys.zerofier m

/-- Cofactor `∏_{m' ≠ m} sys.zerofier m'` of constraint `m`. -/
private noncomputable def zerofierCofactor {F : Type} [Field F] {w M c_num q_extra : ℕ}
    (sys : DeepALISystem F w M c_num q_extra) (m : Fin c_num) : F[X] :=
  ∏ m' ∈ Finset.univ.erase m, sys.zerofier m'

/-- Clearing-denominators numerator `∑ m, C (β m) * evalMaskPoly m P * zerofierCofactor m`. -/
private noncomputable def linkNumerator {F : Type} [Field F] {w M c_num q_extra : ℕ}
    (sys : DeepALISystem F w M c_num q_extra) (P : Fin w → F[X]) (β : Fin c_num → F) : F[X] :=
  ∑ m : Fin c_num, Polynomial.C (β m) * sys.evalMaskPoly m P * zerofierCofactor sys m

/-- Assembled composition-quotient polynomial `∑ j, X ^ (j * (k + 1)) * Q_poly j`. -/
private noncomputable def assembleQuotPoly {F : Type} [Field F] {q_extra : ℕ} (k : ℕ)
    (Q_poly : Fin (q_extra + 1) → F[X]) : F[X] :=
  ∑ j : Fin (q_extra + 1), Polynomial.X ^ (j.val * (k + 1)) * Q_poly j

private lemma monic_zerofierProd {F : Type} [Field F] {w M c_num q_extra : ℕ}
    (sys : DeepALISystem F w M c_num q_extra) :
    (zerofierProd sys).Monic :=
  monic_prod_of_monic _ _ fun m _ => sys.hzerofier_monic m

private lemma monic_zerofierCofactor {F : Type} [Field F] {w M c_num q_extra : ℕ}
    (sys : DeepALISystem F w M c_num q_extra) (m : Fin c_num) :
    (zerofierCofactor sys m).Monic :=
  monic_prod_of_monic _ _ fun m' _ => sys.hzerofier_monic m'

private lemma zerofier_mul_cofactor {F : Type} [Field F] {w M c_num q_extra : ℕ}
    (sys : DeepALISystem F w M c_num q_extra) (m : Fin c_num) :
    sys.zerofier m * zerofierCofactor sys m = zerofierProd sys :=
  Finset.mul_prod_erase Finset.univ sys.zerofier (Finset.mem_univ m)

/-- **Single-tuple ALI divisibility escape bound (`≤ 1 / |F|`)**: for any `P : Fin w → F[X]` that
violates at least one constraint `¬ (sys.zerofier m₀ ∣ sys.evalMaskPoly m₀ P)`, at most
`|F| ^ (c_num - 1)` vectors `β : Fin c_num → F` satisfy `zerofierProd sys ∣ linkNumerator sys P β`.
-/
private lemma toOuterMeasure_zerofierProd_dvd_linkNumerator_le
    {F : Type} [Field F] [Fintype F] {w M c_num q_extra : ℕ}
    (sys : DeepALISystem F w M c_num q_extra) {P : Fin w → F[X]}
    {m₀ : Fin c_num} (hnot_dvd : ¬ (sys.zerofier m₀ ∣ sys.evalMaskPoly m₀ P)) :
    (PMF.uniformOfFintype (Fin c_num → F)).toOuterMeasure
        {β | zerofierProd sys ∣ linkNumerator sys P β} ≤
      (1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  let eSplit : (Fin c_num → F) ≃ F × ({m : Fin c_num // m ≠ m₀} → F) :=
    { toFun := fun β => (β m₀, fun m => β m.val)
      invFun := fun p m => if h : m = m₀ then p.1 else p.2 ⟨m, h⟩
      left_inv := fun β => funext fun m => by
        dsimp only
        split_ifs with h <;> simp only [h]
      right_inv := fun ⟨b₀, rest⟩ =>
        Prod.ext (dite_eq_left rfl) (funext fun ⟨m, hm⟩ => dite_eq_right hm) }
  let eSwap := eSplit.trans (Equiv.prodComm _ _)
  have hcond : ∀ rest : {m : Fin c_num // m ≠ m₀} → F,
      (Finset.univ.filter fun b₀ : F =>
        zerofierProd sys ∣ linkNumerator sys P (eSwap.symm (rest, b₀))).card ≤ 1 := by
    intro rest
    refine Finset.card_le_one.mpr fun b₁ hb₁ b₂ hb₂ => ?_
    by_contra hne
    have hd₁ : zerofierProd sys ∣ linkNumerator sys P (eSwap.symm (rest, b₁)) :=
      (Finset.mem_filter.mp hb₁).2
    have hd₂ : zerofierProd sys ∣ linkNumerator sys P (eSwap.symm (rest, b₂)) :=
      (Finset.mem_filter.mp hb₂).2
    have hsub_dvd : zerofierProd sys ∣
        linkNumerator sys P (eSwap.symm (rest, b₁)) -
          linkNumerator sys P (eSwap.symm (rest, b₂)) :=
      dvd_sub hd₁ hd₂
    have hdiff_eq :
        linkNumerator sys P (eSwap.symm (rest, b₁)) -
          linkNumerator sys P (eSwap.symm (rest, b₂)) =
        Polynomial.C (b₁ - b₂) * sys.evalMaskPoly m₀ P * zerofierCofactor sys m₀ := by
      unfold linkNumerator
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single m₀]
      · simp only [eSwap, eSplit, Equiv.symm_trans_apply, Equiv.prodComm_symm,
          Equiv.prodComm_apply, Prod.fst_swap, Equiv.coe_fn_symm_mk, ↓reduceDIte]
        rw [C_sub]
        ring
      · intro m _ hm
        simp only [eSwap, eSplit, Equiv.symm_trans_apply, Equiv.prodComm_symm,
          Equiv.prodComm_apply, Prod.snd_swap, Equiv.coe_fn_symm_mk, hm,
          ↓reduceDIte, sub_self]
      · intro hmem
        exact False.elim (hmem (Finset.mem_univ m₀))
    rw [hdiff_eq, ← zerofier_mul_cofactor sys m₀] at hsub_dvd
    have hcof_ne : zerofierCofactor sys m₀ ≠ 0 := (monic_zerofierCofactor sys m₀).ne_zero
    have hdvd_scaled : sys.zerofier m₀ ∣ Polynomial.C (b₁ - b₂) * sys.evalMaskPoly m₀ P :=
      (mul_dvd_mul_iff_right hcof_ne).mp hsub_dvd
    have hunit : b₁ - b₂ ≠ 0 := sub_ne_zero.mpr hne
    have hdvd_A : sys.zerofier m₀ ∣ sys.evalMaskPoly m₀ P := by
      have hmul := dvd_mul_of_dvd_right hdvd_scaled (Polynomial.C (b₁ - b₂)⁻¹)
      rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hunit, C_1, one_mul] at hmul
    exact hnot_dvd hdvd_A
  have hbound := Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_cond_le eSwap
    (fun _ => True) (fun β => zerofierProd sys ∣ linkNumerator sys P β)
    (p_top := 0) (p_bot := ((1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
    (by simp only [not_true_eq_false, Set.ofPred_false, MeasureTheory.measure_empty, le_rfl])
    (fun rest _ => Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_div Fintype.card_pos <|
      by
        rw [one_mul]
        simpa only [mul_one] using Nat.mul_le_mul_left (Fintype.card F) (hcond rest))
  simpa only [zero_add, Nat.cast_one] using hbound

private lemma natDegree_linkDiff_le {F : Type} [Field F] {w M c_num q_extra : ℕ}
    (sys : DeepALISystem F w M c_num q_extra)
    {P : Fin w → F[X]} (hP : ∀ i : Fin w, (P i).degree < (sys.params.dim 0 + 1 : ℕ))
    {Q_poly : Fin (q_extra + 1) → F[X]}
    (hQ : ∀ j : Fin (q_extra + 1), (Q_poly j).degree < (sys.params.dim 0 + 1 : ℕ))
    (β : Fin c_num → F) :
    (linkNumerator sys P β -
      assembleQuotPoly (sys.params.dim 0) Q_poly * zerofierProd sys).natDegree ≤
        sys.linkDegBound := by
  have hZprod_deg : (zerofierProd sys).natDegree =
      ∑ m : Fin c_num, (sys.zerofier m).natDegree :=
    natDegree_prod_of_monic _ _ fun m _ => sys.hzerofier_monic m
  have hpos_chunks : 1 ≤ (q_extra + 1) * (sys.params.dim 0 + 1) :=
    Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_sum_le_of_forall_le _ _ fun m _ => ?_
    have hcof_deg : (sys.zerofier m).natDegree + (zerofierCofactor sys m).natDegree =
        (zerofierProd sys).natDegree := by
      rw [← zerofier_mul_cofactor sys m,
        (sys.hzerofier_monic m).natDegree_mul (monic_zerofierCofactor sys m)]
    have hA_deg : (Polynomial.C (β m) * sys.evalMaskPoly m P).natDegree ≤
        constraintDegBound (sys.constraintPoly m) (sys.params.dim 0) :=
      (natDegree_C_mul_le _ _).trans (sys.natDegree_evalMaskPoly_le m hP)
    have hlt := sys.hquot_deg m
    refine (natDegree_mul_le).trans ?_
    rw [DeepALISystem.linkDegBound, ← hZprod_deg]
    omega
  · have hQ_sum_deg : (assembleQuotPoly (sys.params.dim 0) Q_poly).natDegree ≤
        (q_extra + 1) * (sys.params.dim 0 + 1) - 1 := by
      refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
      rcases eq_or_ne (Q_poly j) 0 with h0 | h0
      · simp only [h0, mul_zero, natDegree_zero, Nat.zero_le]
      · have hQj : (Q_poly j).natDegree < sys.params.dim 0 + 1 :=
          (natDegree_lt_iff_degree_lt h0).mpr (hQ j)
        have hj1 : (j.val + 1) * (sys.params.dim 0 + 1) ≤
            (q_extra + 1) * (sys.params.dim 0 + 1) :=
          Nat.mul_le_mul_right _ j.isLt
        have hlt_j : j.val * (sys.params.dim 0 + 1) + (Q_poly j).natDegree <
            (q_extra + 1) * (sys.params.dim 0 + 1) := by
          calc j.val * (sys.params.dim 0 + 1) + (Q_poly j).natDegree
              < j.val * (sys.params.dim 0 + 1) + (sys.params.dim 0 + 1) :=
                Nat.add_lt_add_left hQj _
            _ = (j.val + 1) * (sys.params.dim 0 + 1) := by ring
            _ ≤ (q_extra + 1) * (sys.params.dim 0 + 1) := hj1
        refine (natDegree_mul_le).trans ?_
        rw [natDegree_X_pow]
        omega
    refine (natDegree_mul_le).trans ?_
    rw [DeepALISystem.linkDegBound, ← hZprod_deg]
    omega

private lemma eval_linkDiff_eq_zero_of_linkCheck {F : Type} [Field F] [DecidableEq F]
    {w M c_num q_extra : ℕ}
    (sys : DeepALISystem F w M c_num q_extra)
    {P : Fin w → F[X]} {Q_poly : Fin (q_extra + 1) → F[X]}
    {β : Fin c_num → F} {z : F} (hz : z ∈ sys.oodDom) {op : DeepALIOpening F M q_extra}
    (hlink : sys.linkCheck β z op = true)
    (hP_eval : ∀ u : Fin M, (P (sys.maskCol u)).eval (sys.maskShift u * z) = op.maskVals u)
    (hQ_eval : ∀ j : Fin (q_extra + 1), (Q_poly j).eval z = op.quotVals j) :
    (linkNumerator sys P β -
      assembleQuotPoly (sys.params.dim 0) Q_poly * zerofierProd sys).eval z = 0 := by
  simp only [DeepALISystem.linkCheck, decide_eq_true_eq] at hlink
  have hmask_eq : op.maskVals =
      fun u => (P (sys.maskCol u)).eval (sys.maskShift u * z) :=
    funext fun u => (hP_eval u).symm
  rw [eval_sub, eval_mul, sub_eq_zero, linkNumerator, eval_finsetSum]
  have hnum : (∑ m : Fin c_num,
      (Polynomial.C (β m) * sys.evalMaskPoly m P * zerofierCofactor sys m).eval z) =
      (∑ m : Fin c_num,
        β m * (sys.evalConstraintPoint m z op.maskVals / (sys.zerofier m).eval z)) *
        (zerofierProd sys).eval z := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hZ_ne : (sys.zerofier m).eval z ≠ 0 := sys.hood_zerofier z hz m
    have hcof_eval := congrArg (Polynomial.eval z) (zerofier_mul_cofactor sys m)
    rw [eval_mul] at hcof_eval
    rw [eval_mul, eval_mul, eval_C, sys.eval_evalMaskPoly, ← hmask_eq, ← hcof_eval]
    field_simp
  rw [hnum, hlink, assembleQuotPoly, eval_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_pow, eval_X, hQ_eval j]

private lemma toOuterMeasure_uniformOfFinset_le_div {α : Type*}
    (S : Finset α) (hS : S.Nonempty) (E : Set α) {B : ℕ}
    (hcard : ∀ T : Finset α, (∀ x ∈ T, x ∈ S ∧ x ∈ E) → T.card ≤ B) :
    (PMF.uniformOfFinset S hS).toOuterMeasure E ≤ (B : ℝ≥0∞) / (S.card : ℝ≥0∞) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFinset]
  have hle : (S.filter (· ∈ E)).card ≤ B :=
    hcard _ fun x hx => ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr hle) _

/-- Master list-parameterized adaptive soundness theorem for `deepALIGame`: given candidate list cap
`L ≥ 1` at agreement `2 ^ d - e ≥ k + 1` and batched FRI soundness budget `ε_fri` on statements
outside `batchProximityLang`, bounds the total acceptance probability of any adaptive prover `adv`
on an unsatisfiable constraint system `sys`. -/
private lemma deepALIGame_le_of_listBound {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {w M c_num q_extra e L : ℕ} {ε_fri : ℝ≥0∞}
    (sys : DeepALISystem F w M c_num q_extra)
    (hunsat : ¬ sys.Satisfiable) (hL1 : 1 ≤ L)
    (hinterp_card : sys.params.dim 0 + 1 ≤ 2 ^ sys.params.d - e)
    (hlist : ∀ v : OracleTable sys.params.d F,
      (agreePolyList sys.evalDom (sys.params.dim 0 + 1) v (2 ^ sys.params.d - e)).card ≤ L)
    (hfri : ∀ (stmt : FRIBatchStmt F sys.params.d (M + q_extra)),
      stmt ∉ sys.params.batchProximityLang (M + q_extra) e →
      ∀ P_fri : InteractiveIOPProver sys.params.d F
        (FRIBatchChal F sys.params.d sys.params.q (M + q_extra)),
        iopInteractiveGame (friSmoothBatchIOP sys.params (M + q_extra)) stmt P_fri true ≤ ε_fri)
    (adv : DeepALIProver sys) :
    deepALIGame sys adv true ≤
      ((L ^ w : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) +
        ((L ^ (w + (q_extra + 1)) * sys.linkDegBound : ℕ) : ℝ≥0∞) /
          (sys.oodDom.card : ℝ≥0∞) +
        ε_fri := by
  classical
  rw [← PMF.toOuterMeasure_apply_singleton, deepALIGame]
  refine Cslib.Probability.PMF.toOuterMeasure_bind_le adv.commitTrace _ {true} fun T => ?_
  let a := 2 ^ sys.params.d - e
  let L_P : Finset (Fin w → F[X]) := Fintype.piFinset (traceColCandList sys T a)
  have hLP_card : L_P.card ≤ L ^ w := by
    rw [Fintype.card_piFinset]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_pow_card Finset.univ _ L fun i _ =>
        card_traceColCandList_le sys T hL1 (fun i => hlist (T i)) i
  have hP_deg_of_mem : ∀ P ∈ L_P, ∀ i : Fin w, (P i).degree < (sys.params.dim 0 + 1 : ℕ) := by
    intro P hP i
    have hi := (Fintype.mem_piFinset.mp hP) i
    dsimp only [traceColCandList] at hi
    split_ifs at hi
    · exact (mem_agreePolyList.mp hi).1
    · rw [Finset.mem_singleton.mp hi, degree_zero]
      exact WithBot.bot_lt_coe _
  let goodBeta : Set (Fin c_num → F) :=
    {β | ∀ P ∈ L_P, ¬ (zerofierProd sys ∣ linkNumerator sys P β)}
  have hbeta_err :
      (PMF.uniformOfFintype (Fin c_num → F)).toOuterMeasure goodBetaᶜ ≤
        ((L ^ w : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
    have hsub : goodBetaᶜ ⊆ ⋃ P ∈ L_P, {β | zerofierProd sys ∣ linkNumerator sys P β} := by
      intro β hβ
      simp only [goodBeta, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not] at hβ
      obtain ⟨P, hP, hdvd⟩ := hβ
      exact Set.mem_biUnion hP hdvd
    calc (PMF.uniformOfFintype (Fin c_num → F)).toOuterMeasure goodBetaᶜ
        ≤ (PMF.uniformOfFintype (Fin c_num → F)).toOuterMeasure
            (⋃ P ∈ L_P, {β | zerofierProd sys ∣ linkNumerator sys P β}) :=
          MeasureTheory.measure_mono hsub
      _ ≤ ∑ P ∈ L_P, (PMF.uniformOfFintype (Fin c_num → F)).toOuterMeasure
            {β | zerofierProd sys ∣ linkNumerator sys P β} :=
          MeasureTheory.measure_biUnion_finset_le _ _
      _ ≤ L_P.card • ((1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) := by
          refine Finset.sum_le_card_nsmul _ _ _ fun P hP => ?_
          obtain ⟨m₀, hm₀⟩ := not_forall.mp fun hall => hunsat ⟨P, hP_deg_of_mem P hP, hall⟩
          exact toOuterMeasure_zerofierProd_dvd_linkNumerator_le sys hm₀
      _ ≤ ((L ^ w : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
          rw [nsmul_eq_mul, mul_one_div]
          exact ENNReal.div_le_div_right (Nat.cast_le.mpr hLP_card) _
  rw [add_assoc]
  refine (Cslib.Probability.PMF.toOuterMeasure_bind_failure_le
    (PMF.uniformOfFintype (Fin c_num → F)) _ goodBeta {true} _ ?_).trans
    (add_le_add hbeta_err le_rfl)
  intro β _ hβ_good
  refine Cslib.Probability.PMF.toOuterMeasure_bind_le (adv.commitQuot T β) _ {true} fun Q_orc => ?_
  let L_Q : Finset (Fin (q_extra + 1) → F[X]) :=
    Fintype.piFinset fun j => agreePolyList sys.evalDom (sys.params.dim 0 + 1) (Q_orc j) a
  have hLQ_card : L_Q.card ≤ L ^ (q_extra + 1) := by
    rw [Fintype.card_piFinset]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_pow_card Finset.univ _ L fun j _ => hlist (Q_orc j)
  let goodZ : Set F :=
    {z | ∀ P ∈ L_P, ∀ Q_poly ∈ L_Q,
      (linkNumerator sys P β -
        assembleQuotPoly (sys.params.dim 0) Q_poly * zerofierProd sys).eval z ≠ 0}
  have hz_err :
      (PMF.uniformOfFinset sys.oodDom sys.hood_nonempty).toOuterMeasure goodZᶜ ≤
        ((L ^ (w + (q_extra + 1)) * sys.linkDegBound : ℕ) : ℝ≥0∞) / (sys.oodDom.card : ℝ≥0∞) := by
    refine toOuterMeasure_uniformOfFinset_le_div sys.oodDom sys.hood_nonempty goodZᶜ
      fun BadZ hBadZ => ?_
    have hcov : BadZ ⊆ (L_P ×ˢ L_Q).biUnion fun pq =>
        (linkNumerator sys pq.1 β -
          assembleQuotPoly (sys.params.dim 0) pq.2 * zerofierProd sys).roots.toFinset := by
      intro z hz_mem
      obtain ⟨_, hz_bad⟩ := hBadZ z hz_mem
      simp only [goodZ, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not] at hz_bad
      obtain ⟨P, hP, Q_poly, hQ, hev0⟩ := hz_bad
      rw [Finset.mem_biUnion]
      refine ⟨(P, Q_poly), Finset.mem_product.mpr ⟨hP, hQ⟩, ?_⟩
      have hdiff_ne : linkNumerator sys P β -
          assembleQuotPoly (sys.params.dim 0) Q_poly * zerofierProd sys ≠ 0 := fun h0 =>
        hβ_good P hP ⟨_, by rw [sub_eq_zero.mp h0, mul_comm]⟩
      rw [Multiset.mem_toFinset, mem_roots hdiff_ne, IsRoot.def]
      exact hev0
    calc BadZ.card
        ≤ ((L_P ×ˢ L_Q).biUnion fun pq =>
            (linkNumerator sys pq.1 β -
              assembleQuotPoly (sys.params.dim 0) pq.2 * zerofierProd sys).roots.toFinset).card :=
          Finset.card_le_card hcov
      _ ≤ ∑ pq ∈ L_P ×ˢ L_Q,
            (linkNumerator sys pq.1 β -
              assembleQuotPoly (sys.params.dim 0) pq.2 * zerofierProd sys).roots.toFinset.card :=
          Finset.card_biUnion_le
      _ ≤ (L_P ×ˢ L_Q).card • sys.linkDegBound := by
          refine Finset.sum_le_card_nsmul _ _ _ fun pq hpq => ?_
          obtain ⟨hP, hQ⟩ := Finset.mem_product.mp hpq
          exact (Multiset.toFinset_card_le _).trans <| (card_roots' _).trans <|
            natDegree_linkDiff_le sys (hP_deg_of_mem pq.1 hP)
              (fun j => (mem_agreePolyList.mp ((Fintype.mem_piFinset.mp hQ) j)).1) β
      _ ≤ L ^ (w + (q_extra + 1)) * sys.linkDegBound := by
          rw [smul_eq_mul, Finset.card_product, pow_add]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hLP_card hLQ_card)
  refine (Cslib.Probability.PMF.toOuterMeasure_bind_failure_le
    (PMF.uniformOfFinset sys.oodDom sys.hood_nonempty) _ goodZ {true} ε_fri ?_).trans
    (add_le_add hz_err le_rfl)
  intro z hz_supp hz_good
  have hz_ood : z ∈ sys.oodDom := (PMF.mem_support_uniformOfFinset_iff _ _).mp hz_supp
  refine Cslib.Probability.PMF.toOuterMeasure_bind_le (adv.openOOD T β Q_orc z) _ {true}
    fun ⟨op, P_fri⟩ => ?_
  by_cases hlink : sys.linkCheck β z op = true
  · simp only [hlink, ↓reduceIte, PMF.toOuterMeasure_apply_singleton]
    refine hfri (sys.batchStmt T Q_orc z op) (fun hmem => ?_) P_fri
    obtain ⟨P, Q_poly, hP_mem, hQ_mem, _, _, hP_eval, hQ_eval⟩ :=
      exists_polys_of_batchStmt_mem_proximityLang sys hz_ood hinterp_card hmem
    exact hz_good P hP_mem Q_poly hQ_mem
      (eval_linkDiff_eq_zero_of_linkCheck sys hz_ood hlink hP_eval hQ_eval)
  · have hlink_f : sys.linkCheck β z op = false := Bool.eq_false_iff.mpr hlink
    simp only [hlink_f, Bool.false_eq_true, ↓reduceIte, PMF.toOuterMeasure_apply_singleton,
      PMF.pure_apply, Bool.true_eq_false, zero_le]

/-- **Unconditional adaptive soundness of DEEP-ALI + Smooth Batched FRI across the unique-decoding
radius** (`2 * e + (sys.params.dim 0 + 1) ≤ 2 ^ d`): if `sys` is unsatisfiable, every adaptive
prover `adv` convinces the verifier with probability at most
`1 / |F| + sys.linkDegBound / #sys.oodDom + (2 * 2^d - 2^(d - totalLog)) / |F| +
((2^d - e - 1) / 2^d) ^ q`. -/
theorem deepALIGame_le_of_unique {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {w M c_num q_extra e : ℕ}
    (sys : DeepALISystem F w M c_num q_extra)
    (hunsat : ¬ sys.Satisfiable)
    (huniq : 2 * e + (sys.params.dim 0 + 1) ≤ 2 ^ sys.params.d)
    (adv : DeepALIProver sys) :
    deepALIGame sys adv true ≤
      (1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) +
        (sys.linkDegBound : ℝ≥0∞) / (sys.oodDom.card : ℝ≥0∞) +
        (((2 * 2 ^ sys.params.d - 2 ^ (sys.params.d - sys.params.totalLog) : ℕ) : ℝ≥0∞) /
            (Fintype.card F : ℝ≥0∞) +
          (((2 ^ sys.params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ sys.params.d : ℝ≥0∞)) ^
            sys.params.q) := by
  have hbound := deepALIGame_le_of_listBound (e := e) (L := 1) sys hunsat le_rfl (by omega)
    (fun v => card_agreePolyList_le_one_of_unique sys.evalDom_injective
      (by rw [Fintype.card_fin]; omega) v)
    (fun stmt hfar P_fri =>
      friSmoothBatchIOP_interactiveGame_proximity_le_of_unique sys.params (M + q_extra)
        (by omega) hfar P_fri)
    adv
  simpa only [one_pow, one_mul, Nat.cast_one] using hbound

/-- **Unconditional adaptive soundness of DEEP-ALI + Smooth Batched FRI up to the Johnson bound**
(`√ρ + η ≤ α ≤ 1`, `k + 1 ≤ ⌈α * 2 ^ d⌉₊`, `2 ^ d * k < (⌈α * 2 ^ d⌉₊) ^ 2`): if `sys` is
unsatisfiable, every adaptive prover `adv` convinces the verifier with probability at most
`(L ^ w) / |F| + (L ^ (w + q_extra + 1) * sys.linkDegBound) / #sys.oodDom +
ENNReal.ofReal (friSmoothBatchJohnsonEtaCommitError sys.params η + α ^ q)`, where
`L = sys.johnsonListBound α` (using this library's explicit Siegel constants for batched FRI). -/
theorem deepALIGame_le_of_johnson_eta {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {w M c_num q_extra : ℕ} {η α : ℝ}
    (sys : DeepALISystem F w M c_num q_extra)
    (hunsat : ¬ sys.Satisfiable) (hη : 0 < η)
    (hα_ge : Real.sqrt ((sys.params.dim 0 : ℝ) / (2 ^ sys.params.d : ℝ)) + η ≤ α)
    (hα_le : α ≤ 1)
    (hinterp_card : sys.params.dim 0 + 1 ≤ ⌈α * (2 ^ sys.params.d : ℝ)⌉₊)
    (hjohnson : 2 ^ sys.params.d * sys.params.dim 0 < ⌈α * (2 ^ sys.params.d : ℝ)⌉₊ ^ 2)
    (adv : DeepALIProver sys) :
    let L := sys.johnsonListBound α
    deepALIGame sys adv true ≤
      ((L ^ w : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) +
        ((L ^ (w + (q_extra + 1)) * sys.linkDegBound : ℕ) : ℝ≥0∞) /
          (sys.oodDom.card : ℝ≥0∞) +
        ENNReal.ofReal
          (friSmoothBatchJohnsonEtaCommitError sys.params η + α ^ sys.params.q) := by
  intro L
  let n : ℕ := 2 ^ sys.params.d
  let a : ℕ := ⌈α * (2 ^ sys.params.d : ℝ)⌉₊
  let e : ℕ := n - a
  have hnR_pos : (0 : ℝ) < (2 ^ sys.params.d : ℝ) := by positivity
  have ha_le_n : a ≤ n := by
    refine Nat.ceil_le.mpr ?_
    have hn_eq : ((n : ℕ) : ℝ) = (2 ^ sys.params.d : ℝ) := by
      simp only [n, Nat.cast_pow, Nat.cast_ofNat]
    rw [hn_eq]
    calc α * (2 ^ sys.params.d : ℝ) ≤ 1 * (2 ^ sys.params.d : ℝ) :=
          mul_le_mul_of_nonneg_right hα_le hnR_pos.le
      _ = (2 ^ sys.params.d : ℝ) := one_mul _
  have hsub_eq : 2 ^ sys.params.d - e = a := Nat.sub_sub_self ha_le_n
  refine deepALIGame_le_of_listBound (e := e) (L := L) sys hunsat (le_max_left 1 _)
    (by rwa [hsub_eq])
    (fun v => ?_)
    (fun stmt hfar P_fri => ?_)
    adv
  · rw [hsub_eq]
    refine (card_agreePolyList_le_of_johnson sys.evalDom_injective
      (Nat.succ_pos (sys.params.dim 0))
      (by
        dsimp only [a]
        simpa only [Fintype.card_fin, Nat.succ_sub_one, Nat.add_sub_cancel_right] using hjohnson)
      v).trans ?_
    dsimp only [L, DeepALISystem.johnsonListBound, a]
    simpa only [Fintype.card_fin, Nat.succ_sub_one, Nat.add_sub_cancel_right, Nat.cast_pow,
      Nat.cast_ofNat] using le_max_right 1 _
  · have hfar_corr : stmt ∉ sys.params.batchCorrAgreeLang (M + q_extra) α := by
      rw [FRISmoothParams.batchCorrAgreeLang,
        friBatchCorrAgreeLang_eq_proximityLang sys.params.initialCode (M + q_extra) hα_le]
      exact hfar
    exact friSmoothBatchIOP_interactiveGame_le_of_johnson_eta sys.params (M + q_extra) hη hα_ge
      hfar_corr P_fri

/-- **Binary 2-to-1 `FRIParams` specialization of `deepALIGame_le_of_johnson_eta`** (when
`sys.params = binParams.toSmooth`). -/
theorem deepALIGame_ofBinary_le_of_johnson_eta {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {w M c_num q_extra : ℕ} {η α : ℝ}
    (binParams : FRIParams F)
    (sys : DeepALISystem F w M c_num q_extra) (hsys : sys.params = binParams.toSmooth)
    (hunsat : ¬ sys.Satisfiable) (hη : 0 < η)
    (hα_ge : Real.sqrt ((binParams.dim 0 : ℝ) / (2 ^ binParams.d : ℝ)) + η ≤ α)
    (hα_le : α ≤ 1)
    (hinterp_card : binParams.dim 0 + 1 ≤ ⌈α * (2 ^ binParams.d : ℝ)⌉₊)
    (hjohnson : 2 ^ binParams.d * binParams.dim 0 < ⌈α * (2 ^ binParams.d : ℝ)⌉₊ ^ 2)
    (adv : DeepALIProver sys) :
    let L := sys.johnsonListBound α
    deepALIGame sys adv true ≤
      ((L ^ w : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) +
        ((L ^ (w + (q_extra + 1)) * sys.linkDegBound : ℕ) : ℝ≥0∞) /
          (sys.oodDom.card : ℝ≥0∞) +
        ENNReal.ofReal
          (friBatchJohnsonEtaCommitError binParams η + α ^ binParams.q) := by
  intro L
  have hdim : sys.params.dim 0 = binParams.dim 0 := by
    rw [hsys, binParams.toSmooth_dim (Nat.zero_le _)]
  have hd : sys.params.d = binParams.d := by rw [hsys]
  have hq : sys.params.q = binParams.q := by rw [hsys]
  have herr : friSmoothBatchJohnsonEtaCommitError sys.params η =
      friBatchJohnsonEtaCommitError binParams η := by
    rw [hsys]
    simp only [friBatchJohnsonEtaCommitError, friSmoothBatchJohnsonEtaCommitError,
      binParams.toSmooth_totalLog, binParams.toSmooth_dim (Nat.zero_le _)]
  rw [← herr, ← hq]
  exact deepALIGame_le_of_johnson_eta sys hunsat hη
    (by rwa [hdim, hd]) hα_le (by rwa [hdim, hd]) (by rwa [hdim, hd]) adv

end DeepALI

end Cslib.Crypto.Protocols.FRI
