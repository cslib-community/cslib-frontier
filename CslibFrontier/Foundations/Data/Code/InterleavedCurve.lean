/-
Copyright (c) 2026 Mayank Rathee, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.BerlekampWelch
public import CslibFrontier.Foundations.Data.Code.Interleaved
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve
import CslibFrontier.Foundations.Data.Code.ProximityGap.Unique
import CslibFrontier.Foundations.Data.Hamming
import CslibFrontier.Probability.PMF.UniformBound

/-!
# Curve-batched, Johnson-bound, and uniquely decoded interleaved Reed–Solomon codes

`CslibFrontier.Foundations.Data.Code.Interleaved` formalizes `κ`-interleaved linear codes
`Cslib.Code.interleavedLinear κ C` and random-vector row combinations
`i ↦ ∑ r : Fin m, z r • W i r` up to one-third minimum distance for general linear codes and up to
the unique-decoding radius `2 * e + k ≤ |ι|` for Reed–Solomon codes. This module extends that API in
three directions for `#5968` and `#643`:

1. **Uniqueness and joint Berlekamp–Welch decoding in the unique-decoding regime**
   (`eq_of_mem_interleavedLinear_reedSolomon`, `berlekampWelchInterleaved`): inside
   `2 * e + k ≤ |ι|`, at most one interleaved Reed–Solomon codeword lies within column-Hamming
   distance `e` of a received matrix `W : ι → κ → F`, and running `Cslib.Code.berlekampWelch` on
   each row followed by a joint column-distance check `≤ e` succeeds if and only if the rows share
   correlated agreement on at least `|ι| - e` coordinates
   (`berlekampWelchInterleaved_eq_some_iff`, `berlekampWelchInterleaved_eq_none_iff`).
2. **Single-scalar power / parameterized-curve batching in the unique-decoding regime**
   (`toOuterMeasure_sum_pow_smul_reedSolomon_close_le`,
   `exists_unique_mem_interleavedLinear_reedSolomon_of_pow`, derived from
   [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5 and 6.1] via
   `Cslib.Code.exists_correlatedAgreement_curve_unique`): replacing `m` independent random scalars
   `z : Fin m → F` by powers `1, z, …, z ^ (m - 1)` of a single uniform scalar `z : F` bounds the
   false-closeness probability of any `e`-far matrix `W : ι → Fin m → F` by
   `((m - 1) * |ι|) / |F|` uniformly for all `m : ℕ`, with unique interleaved-codeword recovery
   above that threshold.
3. **Johnson-bound (`1 - √ρ`) interleaved Reed–Solomon proximity bounds** for both
   **affine-vector batching** (`z : Fin m → F`, row-count-independent error) and **single-scalar
   power batching** (`z : F`):
   * explicit-parameter Guruswami–Sudan `(m_GS, D)` steps via
     `Cslib.Code.ProximityGap.johnsonCurveBound`
     (`toOuterMeasure_sum_smul_reedSolomon_close_le_johnson_exact`,
     `toOuterMeasure_sum_pow_smul_reedSolomon_close_le_johnson_exact`);
   * closed-form multiplicity and `η`-gap (`(e : ℝ) / |ι| ≤ 1 - √(k / |ι|) - η`) bounds using this
     library's explicit Siegel constants `1800 * [(m - 1) *] (m_GS + 1) ^ 6 * |ι| ^ 2 / (ρ * |F|)`
     and `115200 * [(m - 1) *] |ι| ^ 2 / (ρ * η ^ 6 * |F|)` (original finite-constant variants in
     the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.2, 1.5, 1.6, and 6.2],
     matching `CslibFrontier.Foundations.Data.Code.ProximityGap.Curve`).

## Main definitions

* `Cslib.Code.berlekampWelchInterleaved`: row-wise Berlekamp–Welch decoder with a joint
  column-Hamming distance check `≤ e` for `κ`-interleaved Reed–Solomon codes.

## Main results

* `Cslib.Code.eq_of_mem_interleavedLinear_reedSolomon`: uniqueness of interleaved Reed–Solomon
  decoding within `2 * e + k ≤ |ι|`.
* `Cslib.Code.degree_lt_of_berlekampWelchInterleaved_eq_some`,
  `Cslib.Code.hammingDist_le_of_berlekampWelchInterleaved_eq_some`,
  `Cslib.Code.berlekampWelchInterleaved_eq_some_iff`,
  `Cslib.Code.berlekampWelchInterleaved_eq_none_iff`: unconditional soundness and unique-decoding
  characterization of `berlekampWelchInterleaved`.
* `Cslib.Code.toOuterMeasure_sum_pow_smul_reedSolomon_close_le`,
  `Cslib.Code.exists_unique_mem_interleavedLinear_reedSolomon_of_pow`: single-scalar
  `((m - 1) * |ι|) / |F|` interleaved Reed–Solomon proximity bound and unique extraction in the
  unique-decoding regime.
* `Cslib.Code.toOuterMeasure_sum_smul_reedSolomon_close_le_johnson_exact`,
  `Cslib.Code.toOuterMeasure_sum_smul_reedSolomon_close_le_johnson`,
  `Cslib.Code.toOuterMeasure_sum_smul_reedSolomon_close_le_johnson_of_eta`: row-count-independent
  affine-vector interleaved Reed–Solomon proximity bounds up to the Johnson bound.
* `Cslib.Code.toOuterMeasure_sum_pow_smul_reedSolomon_close_le_johnson_exact`,
  `Cslib.Code.toOuterMeasure_sum_pow_smul_reedSolomon_close_le_johnson`,
  `Cslib.Code.toOuterMeasure_sum_pow_smul_reedSolomon_close_le_johnson_of_eta`: single-scalar
  curve-batched interleaved Reed–Solomon proximity bounds up to the Johnson bound.

## References

* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf,
  *Proximity Gaps for Reed–Solomon Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
* [L. R. Welch, E. R. Berlekamp, *Error correction for algebraic block codes*][WelchBerlekamp1986]
-/

public section

namespace Cslib.Code

open Cslib.Probability Finset
open scoped BigOperators ENNReal Polynomial

/-! ### Uniqueness and joint Berlekamp–Welch decoding for interleaved Reed–Solomon codes -/

section UniqueAndDecoder

private lemma hammingDist_row_le {ι κ M : Type*} [Fintype ι] [DecidableEq M] [DecidableEq (κ → M)]
    (W₁ W₂ : ι → κ → M) (r : κ) :
    hammingDist (fun i => W₁ i r) (fun i => W₂ i r) ≤ hammingDist W₁ W₂ :=
  Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact fun h => hi (congrFun h r)

/-- **Unique decoding for interleaved Reed–Solomon codes**: with distinct evaluation points
`α : ι → F` and `2 * e + k ≤ |ι|`, at most one interleaved codeword
`V ∈ interleavedLinear κ (reedSolomon α k)` lies within column-Hamming distance `e` of `W`. -/
theorem eq_of_mem_interleavedLinear_reedSolomon {F ι κ : Type*} [Field F] [DecidableEq F]
    [Fintype ι] [Fintype κ] {α : ι → F} (hα : Function.Injective α)
    {e k : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {W V₁ V₂ : ι → κ → F}
    (hV₁ : V₁ ∈ interleavedLinear κ (reedSolomon α k))
    (hV₂ : V₂ ∈ interleavedLinear κ (reedSolomon α k))
    (hd₁ : hammingDist W V₁ ≤ e) (hd₂ : hammingDist W V₂ ≤ e) :
    V₁ = V₂ := by
  classical
  funext i r
  exact congrFun (eq_of_hammingDist_le_reedSolomon (f := fun j => W j r) hα hunique
    (mem_interleavedLinear.1 hV₁ r) (mem_interleavedLinear.1 hV₂ r)
    ((hammingDist_row_le W V₁ r).trans hd₁) ((hammingDist_row_le W V₂ r).trans hd₂)) i

private def acceptIfClose {F ι κ : Type*} [Semiring F] [Fintype ι]
    [DecidableEq (κ → F)] (α : ι → F) (e : ℕ) (W : ι → κ → F) (P : κ → F[X]) : Option (κ → F[X]) :=
  if hammingDist (fun i r => (P r).eval (α i)) W ≤ e then some P else none

open Classical in
/-- **Joint Berlekamp–Welch decoder for `κ`-interleaved Reed–Solomon codes**: decodes each row
`i ↦ W i r` (`r : κ`) via `Cslib.Code.berlekampWelch α e k` and accepts the resulting polynomial
family `P : κ → F[X]` when the joint column-Hamming distance from `i r ↦ (P r).eval (α i)` to `W`
is at most `e` (enforcing correlated agreement across all rows, not merely independent per-row
proximity). As with `Cslib.Code.berlekampWelch`, solutions are chosen noncomputably and no running
time is claimed. -/
noncomputable def berlekampWelchInterleaved {F ι κ : Type*} [Field F] [Fintype ι] [Fintype κ]
    [DecidableEq F] (α : ι → F) (e k : ℕ) (W : ι → κ → F) : Option (κ → F[X]) :=
  if h : ∀ r : κ, (berlekampWelch α e k fun i => W i r).isSome then
    acceptIfClose α e W (fun r => (berlekampWelch α e k fun i => W i r).get (h r))
  else
    none

/-- **Degree soundness of `berlekampWelchInterleaved`**: for every received matrix `W`, every row
polynomial returned by `berlekampWelchInterleaved α e k W` has degree strictly less than `k`. -/
theorem degree_lt_of_berlekampWelchInterleaved_eq_some {F ι κ : Type*} [Field F] [Fintype ι]
    [Fintype κ] [DecidableEq F] {α : ι → F} {e k : ℕ} {W : ι → κ → F} {P : κ → F[X]}
    (h : berlekampWelchInterleaved α e k W = some P) (r : κ) :
    (P r).degree < k := by
  classical
  unfold berlekampWelchInterleaved acceptIfClose at h
  split_ifs at h with hsome _
  cases h
  exact degree_lt_of_berlekampWelch_eq_some (Option.some_get (hsome r)).symm

/-- **Joint distance soundness of `berlekampWelchInterleaved`**: for every received matrix `W`, an
output `P` of `berlekampWelchInterleaved α e k W` evaluates to an interleaved codeword within
column-Hamming distance `e` of `W`. -/
theorem hammingDist_le_of_berlekampWelchInterleaved_eq_some {F ι κ : Type*} [Field F] [Fintype ι]
    [Fintype κ] [DecidableEq F] {α : ι → F} {e k : ℕ} {W : ι → κ → F} {P : κ → F[X]}
    (h : berlekampWelchInterleaved α e k W = some P) :
    hammingDist (fun i r => (P r).eval (α i)) W ≤ e := by
  classical
  unfold berlekampWelchInterleaved acceptIfClose at h
  split_ifs at h with _ hdist
  exact Option.some.inj h ▸ hdist

/-- **Characterization of `berlekampWelchInterleaved` in the unique-decoding regime**
(`2 * e + k ≤ |ι|`): with distinct evaluation points `α : ι → F`, the decoder returns `some P` if
and only if every `P r` has degree `< k` and `i r ↦ (P r).eval (α i)` has column-Hamming distance
at most `e` from `W`. -/
theorem berlekampWelchInterleaved_eq_some_iff {F ι κ : Type*} [Field F] [Fintype ι] [Fintype κ]
    [DecidableEq F] {α : ι → F} (hα : Function.Injective α)
    {e k : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι) {W : ι → κ → F} {P : κ → F[X]} :
    berlekampWelchInterleaved α e k W = some P ↔
      (∀ r : κ, (P r).degree < k) ∧ hammingDist (fun i r => (P r).eval (α i)) W ≤ e := by
  classical
  refine ⟨fun h => ⟨degree_lt_of_berlekampWelchInterleaved_eq_some h,
    hammingDist_le_of_berlekampWelchInterleaved_eq_some h⟩, fun ⟨hdeg, hdist⟩ => ?_⟩
  have hbw (r : κ) := berlekampWelch_eq_some hα hunique (hdeg r)
    ((hammingDist_row_le (fun i r => (P r).eval (α i)) W r).trans hdist)
  have hsome : ∀ r : κ, (berlekampWelch α e k fun i => W i r).isSome := fun r => by simp [hbw r]
  have hget : (fun r : κ => (berlekampWelch α e k fun i => W i r).get (hsome r)) = P :=
    funext fun r => Option.some.inj ((Option.some_get (hsome r)).trans (hbw r))
  unfold berlekampWelchInterleaved
  rw [dite_eq_left hsome, hget]
  exact ite_eq_left hdist

/-- **Failure characterization of `berlekampWelchInterleaved` in the unique-decoding regime**
(`2 * e + k ≤ |ι|`): the decoder returns `none` if and only if `W` has column-Hamming distance
strictly greater than `e` from every codeword of `interleavedLinear κ (reedSolomon α k)`. -/
theorem berlekampWelchInterleaved_eq_none_iff {F ι κ : Type*} [Field F] [Fintype ι] [Fintype κ]
    [DecidableEq F] {α : ι → F} (hα : Function.Injective α)
    {e k : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι) {W : ι → κ → F} :
    berlekampWelchInterleaved α e k W = none ↔
      ∀ V ∈ interleavedLinear κ (reedSolomon α k), e < hammingDist W V := by
  classical
  refine ⟨fun hnone V hV => not_le.1 fun hdist => ?_, fun hfar => ?_⟩
  · choose P hP_deg hP_eval using fun r => mem_reedSolomon.1 (mem_interleavedLinear.1 hV r)
    have hVEq : (fun i r => (P r).eval (α i)) = V := funext fun i => funext fun r =>
      congrFun (hP_eval r) i
    exact Option.some_ne_none _ (((berlekampWelchInterleaved_eq_some_iff hα hunique
      (W := W) (P := P)).2 ⟨hP_deg, by rwa [hVEq, hammingDist_comm]⟩).symm.trans hnone)
  · rcases hbw : berlekampWelchInterleaved α e k W with _ | P
    · rfl
    · exact absurd (hammingDist_comm (fun i r => (P r).eval (α i)) W ▸
        hammingDist_le_of_berlekampWelchInterleaved_eq_some hbw)
        (hfar _ (mem_interleavedLinear.2 fun r => eval_mem_reedSolomon α
          (degree_lt_of_berlekampWelchInterleaved_eq_some hbw r))).not_ge

end UniqueAndDecoder

/-! ### Single-scalar curve-batched Reed–Solomon proximity in the unique-decoding regime -/

section CurveUnique

private lemma eq_zero_of_fin_zero {ι M : Type*} [Zero M] (W : ι → Fin 0 → M) : W = 0 :=
  funext fun _ => funext fun r => r.elim0

private lemma curve_eval_eq_sum_pow {F ι : Type*} [Semiring F] {m : ℕ}
    (W : ι → Fin m → F) (z : F) :
    (∑ r : Fin m, z ^ (r : ℕ) • fun i => W i r) = fun i => ∑ r : Fin m, z ^ (r : ℕ) • W i r := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply]

private lemma toOuterMeasure_sum_pow_smul_le_div_of_curve {F ι : Type*}
    [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {α : ι → F} {e k m : ℕ} (B : ℕ → ℕ)
    (hca : ∀ (r : ℕ) (u : Fin (r + 1) → ι → F) (S : Finset F),
      B (r + 1) < S.card →
      (∀ z ∈ S, ∃ c ∈ reedSolomon α k,
        hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c ≤ e) →
      ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
        ∃ v : Fin (r + 1) → ι → F, (∀ j, v j ∈ reedSolomon α k) ∧
          ∀ i ∈ D', ∀ j, u j i = v j i)
    {W : ι → Fin m → F}
    (hfar : ∀ V ∈ interleavedLinear (Fin m) (reedSolomon α k), e < hammingDist W V) :
    (PMF.uniformOfFintype F).toOuterMeasure
        {z : F | ∃ c ∈ reedSolomon α k,
          hammingDist (fun i => ∑ r : Fin m, z ^ (r : ℕ) • W i r) c ≤ e} ≤
      (B m : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  rcases m with _ | r
  · refine False.elim ((hfar 0 (Submodule.zero_mem _)).not_ge ?_)
    rw [eq_zero_of_fin_zero W, hammingDist_self]
    exact Nat.zero_le e
  · refine Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_div Fintype.card_pos ?_
    rw [mul_comm (B (r + 1))]
    refine Nat.mul_le_mul_left (Fintype.card F) (le_of_not_gt fun hlt => ?_)
    obtain ⟨D', hD', v, hv, hag⟩ := hca r (fun j i => W i j) _ hlt fun z hz =>
      curve_eval_eq_sum_pow W z ▸ (Finset.mem_filter.1 hz).2
    obtain ⟨V, hV, hdist⟩ := exists_mem_interleavedLinear_hammingDist_le_iff.2 ⟨D', hD', v, hv, hag⟩
    exact (hfar V hV).not_ge hdist

/-- **Single-scalar curve-batched Reed–Solomon proximity bound in the unique-decoding regime**
(`2 * e + k ≤ |ι|`, derived from [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5 and 6.1] via
`Cslib.Code.exists_correlatedAgreement_curve_unique`): over a finite field `F` with distinct
evaluation points `α : ι → F`, if `W : ι → Fin m → F` has column-Hamming distance strictly greater
than `e` from `interleavedLinear (Fin m) (reedSolomon α k)`, then a single uniformly sampled scalar
`z : F` produces a power row combination `i ↦ ∑ r : Fin m, z ^ (r : ℕ) • W i r` within Hamming
distance `e` of `reedSolomon α k` with probability at most `((m - 1) * |ι|) / |F|` uniformly for all
`m : ℕ`. -/
theorem toOuterMeasure_sum_pow_smul_reedSolomon_close_le
    {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {e k m : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {W : ι → Fin m → F}
    (hfar : ∀ V ∈ interleavedLinear (Fin m) (reedSolomon α k), e < hammingDist W V) :
    (PMF.uniformOfFintype F).toOuterMeasure
        {z : F | ∃ c ∈ reedSolomon α k,
          hammingDist (fun i => ∑ r : Fin m, z ^ (r : ℕ) • W i r) c ≤ e} ≤
      (((m - 1) * Fintype.card ι : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  toOuterMeasure_sum_pow_smul_le_div_of_curve (fun m => (m - 1) * Fintype.card ι)
    (fun r u S hlt hS => by
      rw [Nat.add_sub_cancel] at hlt
      exact exists_correlatedAgreement_curve_unique hα hunique u S hlt hS)
    hfar

/-- **Single-scalar curve-batched correlated agreement and unique extraction in the
unique-decoding regime** (`2 * e + k ≤ |ι|`): if `i ↦ ∑ r : Fin m, z ^ (r : ℕ) • W i r` lies within
Hamming distance `e` of `reedSolomon α k` with probability strictly greater than
`((m - 1) * |ι|) / |F|` over uniform `z : F`, then there exists a unique interleaved codeword
`V ∈ interleavedLinear (Fin m) (reedSolomon α k)` within column-Hamming distance `e` of `W`. -/
theorem exists_unique_mem_interleavedLinear_reedSolomon_of_pow
    {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {e k m : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {W : ι → Fin m → F}
    (hprob : (((m - 1) * Fintype.card ι : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) <
      (PMF.uniformOfFintype F).toOuterMeasure
        {z : F | ∃ c ∈ reedSolomon α k,
          hammingDist (fun i => ∑ r : Fin m, z ^ (r : ℕ) • W i r) c ≤ e}) :
    ∃! V : ι → Fin m → F,
      V ∈ interleavedLinear (Fin m) (reedSolomon α k) ∧ hammingDist W V ≤ e := by
  have hex : ∃ V ∈ interleavedLinear (Fin m) (reedSolomon α k), hammingDist W V ≤ e := by
    by_contra! hfar
    exact hprob.not_ge (toOuterMeasure_sum_pow_smul_reedSolomon_close_le hα hunique hfar)
  obtain ⟨V, hV, hdist⟩ := hex
  exact ⟨V, ⟨hV, hdist⟩, fun V' ⟨hV', hdist'⟩ =>
    eq_of_mem_interleavedLinear_reedSolomon hα hunique hV' hV hdist' hdist⟩

end CurveUnique

/-! ### Johnson-bound (`1 - √ρ`) interleaved Reed–Solomon proximity bounds -/

section JohnsonRegime

private lemma zero_add_sum_smul_eq {F ι R : Type*} [AddCommMonoid F] [Semiring R] [Module R F]
    {m : ℕ} (W : ι → Fin m → F) (z : Fin m → R) :
    (0 : ι → F) + (∑ r : Fin m, z r • fun i => W i r) = fun i => ∑ r : Fin m, z r • W i r := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply, zero_add, Finset.sum_apply, Pi.smul_apply]

/-- **Explicit-parameter Guruswami–Sudan interleaved Reed–Solomon proximity bound up to the Johnson
bound (affine-vector batching)** (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.2 and 1.6], derived via
`Cslib.Code.exists_correlatedAgreement_affine_johnson`): for any Guruswami–Sudan multiplicity
`m_GS ≥ 1` and weighted degree `D` satisfying `k ≤ |ι| - e`,
`|ι| * (m_GS * (m_GS + 1) / 2) < #(Sudan.monomials (k - 1) D)`, and `D < m_GS * (|ι| - e)`, any
`e`-far word `W : ι → Fin m → F` produces an `e`-close uniform row combination
`i ↦ ∑ r, z r • W i r` with probability at most
`johnsonCurveBound |ι| m_GS (k - 1) D 1 |ι| / |F|`, with **zero dependence on the row count `m`**
and no auxiliary list-size hypothesis. -/
theorem toOuterMeasure_sum_smul_reedSolomon_close_le_johnson_exact
    {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {k m e m_GS D : ℕ}
    (hk : 1 ≤ k) (hm_GS : 1 ≤ m_GS)
    (hk_le : k ≤ Fintype.card ι - e)
    (hinterp : Fintype.card ι * (m_GS * (m_GS + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m_GS * (Fintype.card ι - e))
    {W : ι → Fin m → F}
    (hfar : ∀ V ∈ interleavedLinear (Fin m) (reedSolomon α k), e < hammingDist W V) :
    (PMF.uniformOfFintype (Fin m → F)).toOuterMeasure
        {z | ∃ c ∈ reedSolomon α k, hammingDist (fun i => ∑ r : Fin m, z r • W i r) c ≤ e} ≤
      (ProximityGap.johnsonCurveBound (Fintype.card ι) m_GS (k - 1) D 1 (Fintype.card ι) :
        ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  refine Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_div Fintype.card_pos ?_
  rw [Fintype.card_fun, Fintype.card_fin]
  refine le_of_not_gt fun hlt => ?_
  obtain ⟨D', hD', _, _, v, hv, hag⟩ :=
    exists_correlatedAgreement_affine_johnson hα hk hm_GS hk_le hinterp hroot 0
      (fun r i => W i r) _ hlt fun z hz => zero_add_sum_smul_eq W z ▸ (Finset.mem_filter.1 hz).2
  obtain ⟨V, hV, hdist⟩ := exists_mem_interleavedLinear_hammingDist_le_iff.2
    ⟨D', hD', v, hv, fun i hi r => (hag i hi).2 r⟩
  exact (hfar V hV).not_ge hdist

/-- **Original explicit-constant interleaved Reed–Solomon proximity bound up to the Johnson bound
(affine-vector batching, multiplicity form)** (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.2 and 1.6], derived via
`Cslib.Code.exists_correlatedAgreement_affine_johnson_of_multiplicity`): for `1 ≤ k ≤ |ι|`,
`m_GS ≥ 1`, and `(e : ℝ) / |ι| ≤ 1 - √ρ - √ρ / (2 * m_GS)` (`ρ = k / |ι|`), an `e`-far word
`W : ι → Fin m → F` produces an `e`-close uniform row combination with probability at most
`1800 * (m_GS + 1) ^ 6 * |ι| ^ 2 / (ρ * |F|)`, uniformly for all `m : ℕ` (using this library's
explicit Siegel constant rather than the paper's displayed finite constant). -/
theorem toOuterMeasure_sum_smul_reedSolomon_close_le_johnson
    {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {e k m_GS m : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hm_GS : 1 ≤ m_GS)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m_GS : ℝ)))
    {W : ι → Fin m → F}
    (hfar : ∀ V ∈ interleavedLinear (Fin m) (reedSolomon α k), e < hammingDist W V) :
    (PMF.uniformOfFintype (Fin m → F)).toOuterMeasure
        {z | ∃ c ∈ reedSolomon α k, hammingDist (fun i => ∑ r : Fin m, z r • W i r) c ≤ e} ≤
      ENNReal.ofReal
        (1800 * ((m_GS + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ))) := by
  classical
  let T : Finset (Fin m → F) := Finset.univ.filter fun z =>
    ∃ c ∈ reedSolomon α k, hammingDist (fun i => ∑ r : Fin m, z r • W i r) c ≤ e
  refine Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_of_dens_le _ T
    (fun z hz => Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ z, hz⟩)) ?_
  rw [Finset.nnratCast_dens, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  refine le_of_not_gt fun hlt => ?_
  obtain ⟨D', hD', _, _, v, hv, hag⟩ :=
    exists_correlatedAgreement_affine_johnson_of_multiplicity hα hk hkn hm_GS he 0
      (fun r i => W i r) T hlt fun z hz => zero_add_sum_smul_eq W z ▸ (Finset.mem_filter.1 hz).2
  obtain ⟨V, hV, hdist⟩ := exists_mem_interleavedLinear_hammingDist_le_iff.2
    ⟨D', hD', v, hv, fun i hi r => (hag i hi).2 r⟩
  exact (hfar V hV).not_ge hdist

private lemma siegel_multiplicity_le_eta {c n_sq ρ q η m_val : ℝ}
    (hc : 0 ≤ c) (hn : 0 ≤ n_sq) (hρ : 0 < ρ) (hq : 0 < q) (hη : 0 < η)
    (hpow : m_val ^ 6 ≤ 64 / (η ^ 6)) :
    1800 * c * (m_val ^ 6) * n_sq / (ρ * q) ≤ 115200 * c * n_sq / (ρ * (η ^ 6) * q) := by
  calc 1800 * c * (m_val ^ 6) * n_sq / (ρ * q)
      ≤ 1800 * c * (64 / (η ^ 6)) * n_sq / (ρ * q) := by gcongr
    _ = 115200 * c * n_sq / (ρ * (η ^ 6) * q) := by
        field_simp
        ring

/-- **Original explicit-constant interleaved Reed–Solomon proximity bound up to `1 - √ρ - η`
(affine-vector batching)** (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.2 and 1.6], derived via
`toOuterMeasure_sum_smul_reedSolomon_close_le_johnson` and
`Cslib.Code.ProximityGap.exists_multiplicity_of_eta`): for `1 ≤ k ≤ |ι|`, `η > 0`, and
`(e : ℝ) / |ι| ≤ 1 - √ρ - η`, an `e`-far word `W : ι → Fin m → F` produces an `e`-close uniform row
combination with probability at most `115200 * |ι| ^ 2 / (ρ * η ^ 6 * |F|)`, independent of the row
count `m : ℕ` (using this library's explicit Siegel constant). -/
theorem toOuterMeasure_sum_smul_reedSolomon_close_le_johnson_of_eta
    {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {e k m : ℕ} {η : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hη : 0 < η)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) - η)
    {W : ι → Fin m → F}
    (hfar : ∀ V ∈ interleavedLinear (Fin m) (reedSolomon α k), e < hammingDist W V) :
    (PMF.uniformOfFintype (Fin m → F)).toOuterMeasure
        {z | ∃ c ∈ reedSolomon α k, hammingDist (fun i => ∑ r : Fin m, z r • W i r) c ≤ e} ≤
      ENNReal.ofReal
        (115200 * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ))) := by
  obtain ⟨m_GS, hm_GS, he', hpow⟩ := ProximityGap.exists_multiplicity_of_eta hk hkn hη he
  refine (toOuterMeasure_sum_smul_reedSolomon_close_le_johnson hα hk hkn hm_GS he' hfar).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hn : 1 ≤ Fintype.card ι := hk.trans hkn
  simpa only [mul_one] using siegel_multiplicity_le_eta zero_le_one (sq_nonneg _)
    (by positivity) (Nat.cast_pos.2 Fintype.card_pos) hη hpow

/-- **Explicit-parameter Guruswami–Sudan interleaved Reed–Solomon proximity bound up to the Johnson
bound (single-scalar power batching)** (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5 and 6.2], derived via
`Cslib.Code.exists_correlatedAgreement_curve_johnson`): for any `e`-far word `W : ι → Fin m → F`,
a single uniform scalar `z : F` produces an `e`-close power combination
`i ↦ ∑ r : Fin m, z ^ (r : ℕ) • W i r` with probability at most
`johnsonCurveBound |ι| m_GS (k - 1) D (m - 1) |ι| / |F|` uniformly for all `m : ℕ`. -/
theorem toOuterMeasure_sum_pow_smul_reedSolomon_close_le_johnson_exact
    {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {k m e m_GS D : ℕ}
    (hk : 1 ≤ k) (hm_GS : 1 ≤ m_GS)
    (hk_le : k ≤ Fintype.card ι - e)
    (hinterp : Fintype.card ι * (m_GS * (m_GS + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m_GS * (Fintype.card ι - e))
    {W : ι → Fin m → F}
    (hfar : ∀ V ∈ interleavedLinear (Fin m) (reedSolomon α k), e < hammingDist W V) :
    (PMF.uniformOfFintype F).toOuterMeasure
        {z : F | ∃ c ∈ reedSolomon α k,
          hammingDist (fun i => ∑ r : Fin m, z ^ (r : ℕ) • W i r) c ≤ e} ≤
      (ProximityGap.johnsonCurveBound (Fintype.card ι) m_GS (k - 1) D (m - 1)
        (Fintype.card ι) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  toOuterMeasure_sum_pow_smul_le_div_of_curve
    (fun m => ProximityGap.johnsonCurveBound (Fintype.card ι) m_GS (k - 1) D (m - 1)
      (Fintype.card ι))
    (fun r u S hlt hS => by
      rw [Nat.add_sub_cancel] at hlt
      exact exists_correlatedAgreement_curve_johnson hα hk hm_GS hk_le hinterp hroot u S hlt hS)
    hfar

/-- **Original explicit-constant interleaved Reed–Solomon proximity bound up to the Johnson bound
(single-scalar power batching, multiplicity form)** (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5 and 6.2]): for `1 ≤ k ≤ |ι|`, `m_GS ≥ 1`, and
`(e : ℝ) / |ι| ≤ 1 - √ρ - √ρ / (2 * m_GS)`, an `e`-far word `W : ι → Fin m → F` produces an
`e`-close single-scalar power combination with probability at most
`1800 * (m - 1) * (m_GS + 1) ^ 6 * |ι| ^ 2 / (ρ * |F|)` uniformly for all `m : ℕ` (using this
library's explicit Siegel constant). -/
theorem toOuterMeasure_sum_pow_smul_reedSolomon_close_le_johnson
    {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {e k m_GS m : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hm_GS : 1 ≤ m_GS)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m_GS : ℝ)))
    {W : ι → Fin m → F}
    (hfar : ∀ V ∈ interleavedLinear (Fin m) (reedSolomon α k), e < hammingDist W V) :
    (PMF.uniformOfFintype F).toOuterMeasure
        {z : F | ∃ c ∈ reedSolomon α k,
          hammingDist (fun i => ∑ r : Fin m, z ^ (r : ℕ) • W i r) c ≤ e} ≤
      ENNReal.ofReal
        (1800 * ((m - 1 : ℕ) : ℝ) * ((m_GS + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ))) := by
  classical
  rcases m with _ | r
  · refine False.elim ((hfar 0 (Submodule.zero_mem _)).not_ge ?_)
    rw [eq_zero_of_fin_zero W, hammingDist_self]
    exact Nat.zero_le e
  · rw [Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have hemp : {z : F | ∃ c ∈ reedSolomon α k,
          hammingDist (fun i => ∑ r : Fin 1, z ^ (r : ℕ) • W i r) c ≤ e} = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun z ⟨c, hc, hd⟩ => by
          refine (hfar (fun i _ => c i) (mem_interleavedLinear.2 fun _ => hc)).not_ge
            (le_trans (Finset.card_le_card fun i hi => ?_) hd)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.sum_univ_one, Fin.val_zero,
            pow_zero, one_smul] at hi ⊢
          exact fun hEq => hi (funext fun j => Fin.eq_zero j ▸ hEq)
      rw [hemp]
      simp
    · let T : Finset F := Finset.univ.filter fun z =>
        ∃ c ∈ reedSolomon α k, hammingDist (fun i => ∑ j : Fin (r + 1), z ^ (j : ℕ) • W i j) c ≤ e
      refine Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_of_dens_le _ T
        (fun z hz => Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ z, hz⟩)) ?_
      rw [Finset.nnratCast_dens]
      obtain ⟨hk_sub, hinterp, hroot, hjb⟩ :=
        ProximityGap.johnson_curve_params_bound hk hkn hm_GS hr he
      have hcard_le := le_of_not_gt fun hlt => by
        obtain ⟨D', hD', v, hv, hag⟩ :=
          exists_correlatedAgreement_curve_johnson hα hk (by omega) hk_sub hinterp hroot
            (fun j i => W i j) T hlt fun z hz =>
              curve_eval_eq_sum_pow W z ▸ (Finset.mem_filter.1 hz).2
        obtain ⟨V, hV, hdist⟩ :=
          exists_mem_interleavedLinear_hammingDist_le_iff.2 ⟨D', hD', v, hv, hag⟩
        exact (hfar V hV).not_ge hdist
      simpa only [div_div] using div_le_div_of_nonneg_right
        ((Nat.cast_le.2 hcard_le).trans hjb) (Nat.cast_nonneg (Fintype.card F))

/-- **Original explicit-constant interleaved Reed–Solomon proximity bound up to `1 - √ρ - η`
(single-scalar power batching)** (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5 and 6.2]): for `1 ≤ k ≤ |ι|`, `η > 0`, and
`(e : ℝ) / |ι| ≤ 1 - √ρ - η`, an `e`-far word `W : ι → Fin m → F` produces an `e`-close
single-scalar power combination with probability at most
`115200 * (m - 1) * |ι| ^ 2 / (ρ * η ^ 6 * |F|)` uniformly for all `m : ℕ` (using this library's
explicit Siegel constant). -/
theorem toOuterMeasure_sum_pow_smul_reedSolomon_close_le_johnson_of_eta
    {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {e k m : ℕ} {η : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hη : 0 < η)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) - η)
    {W : ι → Fin m → F}
    (hfar : ∀ V ∈ interleavedLinear (Fin m) (reedSolomon α k), e < hammingDist W V) :
    (PMF.uniformOfFintype F).toOuterMeasure
        {z : F | ∃ c ∈ reedSolomon α k,
          hammingDist (fun i => ∑ r : Fin m, z ^ (r : ℕ) • W i r) c ≤ e} ≤
      ENNReal.ofReal
        (115200 * ((m - 1 : ℕ) : ℝ) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ))) := by
  obtain ⟨m_GS, hm_GS, he', hpow⟩ := ProximityGap.exists_multiplicity_of_eta hk hkn hη he
  refine (toOuterMeasure_sum_pow_smul_reedSolomon_close_le_johnson hα hk hkn hm_GS he' hfar).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hn : 1 ≤ Fintype.card ι := hk.trans hkn
  exact siegel_multiplicity_le_eta (Nat.cast_nonneg _) (sq_nonneg _)
    (by positivity) (Nat.cast_pos.2 Fintype.card_pos) hη hpow

end JohnsonRegime

end Cslib.Code
