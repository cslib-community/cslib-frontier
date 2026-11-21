/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.Soundness
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson
import CslibFrontier.Foundations.Data.Code.ProximityGap.Unique
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Unconditional Unique-Decoding and Johnson-Bound Smooth & Binary FRI, IOP, and BCS-FRI Soundness

This module discharges the per-round and uniform degree-`(l⁽ⁱ⁾ - 1)` curve proximity-gap hypotheses
of `CslibFrontier.Crypto.Protocols.FRI.Soundness` unconditionally for the single-word
(`OracleTable d F`) smooth `2 ^ stepLog i`-to-1 FRI IOP `Cslib.Crypto.Protocols.FRI.friSmoothIOP`
(and its binary 2-to-1 specialization `Cslib.Crypto.Protocols.FRI.friIOP`) in both the
unique-decoding regime and the Johnson-bound regime, combining
`Cslib.Code.exists_correlatedAgreement_curve_unique`
([BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5 and 6.1]) and
`Cslib.Code.exists_weighted_correlatedAgreement_curve_johnson`
([BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5, 6.2, and 7.2]) with
`Cslib.Crypto.Protocols.FRI.friSmoothIOP_rbrSound`, the per-round commit and summed interactive IOP
soundness providers (`friSmoothCommitGame_le_of_weightedCurveGapPerRound`,
`friSmoothIOP_interactiveGame_le_of_weightedCurveGapPerRound`), and the two-channel BCS
random-oracle soundness provider
`Cslib.Crypto.Protocols.FRI.friSmoothBCS_romSoundness_bound_of_weightedCurveGap` /
`Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound` ([BenSassonBentovHoreshRiabzev2018];
[BenSassonChiesaSpooner2016]; [ChiesaYogev2024]).

## Scope and relationship to the source theorems

* Lemma 8.2 (printed pp. 38–39, proved via the commit-phase bad-event sum in Section 8.2.1,
  printed pp. 41–43, p. 42) and Theorem 8.3 (printed p. 39, proved on printed p. 40 by applying
  Lemma 8.2) of the accepted *Journal of the ACM* (2023) manuscript
  ([BenSassonCarmonIshaiKoppartySaraf2020]) are interactive IOP soundness theorems for *batched*
  FRI establishing correlated agreement of the initial functions; BCS random-oracle soundness bounds
  are separate compositions.
* Folding in `friSmoothIOP` supports an arbitrary smooth schedule `l⁽ⁱ⁾ = 2 ^ stepLog i ≥ 2` per
  round (specializing to binary `l⁽ⁱ⁾ = 2` via `FRIParams.toSmooth`). Across the `m` folding rounds,
  the curve degree `l⁽ⁱ⁾ - 1` multiplies the target domain size `domainSize (i + 1)`, so
  `∑ i, (l⁽ⁱ⁾ - 1) * domainSize (i + 1) = 2 ^ d - 2 ^ (d - totalLog)` telescopes exactly
  (`FRISmoothParams.sum_arity_sub_one_mul_domainSize`), keeping both the unique-decoding commit
  error `(1 - 1 / 2 ^ totalLog) * (2 ^ d / |F|)` and the Siegel-interpolation Johnson commit error
  `friSmoothJohnsonCommitError` independent of `m` and the per-round arities `l⁽ⁱ⁾` (mirroring the
  telescoping on printed p. 43 of [BenSassonCarmonIshaiKoppartySaraf2020]).
* In the Johnson regime, `friSmoothJohnsonRoundBound`, `friSmoothJohnsonCommitBound`,
  `friSmoothJohnsonEtaCommitBound`, `friSmoothJohnsonCommitError`, and their binary counterparts use
  this library's original explicit Siegel-interpolation constants for all `mJ ≥ 1`
  (`1800 * (mJ + 1) ^ 6 * …` and `115200 * … / η ^ 6` using `η` directly rather than
  `min(η, √ρ / 20)` in eq. 1.3), which are not uniformly smaller at small `mJ` than the constants
  displayed in JACM Lemma 8.2 / Theorem 8.3. Exact correspondence with JACM Theorem 8.3's displayed
  error expression remains open on `#5968`.
* All binary `FRIParams` soundness theorems are proved as short corollaries of the smooth theorems
  via `FRIParams.toSmooth` with zero duplicated proofs.

## Main definitions

* `Cslib.Crypto.Protocols.FRI.friSmoothUniqueCommitError` &
  `Cslib.Crypto.Protocols.FRI.friUniqueCommitError`: closed-form telescoping unique-decoding
  commit-phase error `(1 - 1 / 2 ^ totalLog) * (2 ^ d / |F|)` (and binary `(1 - 1 / 2 ^ m)`).
* `Cslib.Crypto.Protocols.FRI.friSmoothJohnsonRoundBound`,
  `Cslib.Crypto.Protocols.FRI.friSmoothJohnsonCommitBound`,
  `Cslib.Crypto.Protocols.FRI.friSmoothJohnsonEtaCommitBound`, &
  `Cslib.Crypto.Protocols.FRI.friSmoothJohnsonCommitError`: smooth per-round, uniform round-0,
  uniform `η`-gap, and closed-form telescoping Siegel-interpolation Johnson commit budgets/errors
  (with binary counterparts `friJohnsonRoundBound`, `friJohnsonCommitBound`,
  `friJohnsonEtaCommitBound`, `friJohnsonCommitError`).

## Main results

### Smooth & binary unique-decoding regime (`2 * e + params.dim 0 ≤ 2 ^ params.d`)
* `Cslib.Crypto.Protocols.FRI.weightedCurveGapPerRound_of_unique` &
  `Cslib.Crypto.Protocols.FRI.weightedCurveGapBound_of_unique` (binary:
  `weightedLineGapPerRound_of_unique`, `weightedLineGapBound_of_unique`).
* `Cslib.Crypto.Protocols.FRI.friSmoothCommitGame_le_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friSmoothIOP_interactiveGame_le_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friSmoothIOP_rbrSound_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBCS_romSoundness_bound_of_unique`, &
  `FRI.friSmoothBCS_romSoundness_bound_of_prover_verifier_of_unique` (and binary counterparts).

### Smooth & binary Johnson-bound regime (`δ ≤ 1 - √ρ - √ρ / (2 * mJ)` and discrete bounds)
* `Cslib.Crypto.Protocols.FRI.weightedCurveGapPerRound_of_johnson_discrete`,
  `Cslib.Crypto.Protocols.FRI.weightedCurveGapBound_of_johnson_discrete`,
  `Cslib.Crypto.Protocols.FRI.friSmoothCommitGame_le_of_johnson_discrete`, &
  `Cslib.Crypto.Protocols.FRI.friSmoothIOP_interactiveGame_le_of_johnson_discrete` (and binary
  counterparts).
* `Cslib.Crypto.Protocols.FRI.weightedCurveGapPerRound_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.weightedCurveGapBound_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.weightedCurveGapBound_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.friSmoothCommitGame_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friSmoothIOP_interactiveGame_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friSmoothIOP_rbrSound_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBCS_romSoundness_bound_of_johnson`, &
  `FRI.friSmoothBCS_romSoundness_bound_of_prover_verifier_of_johnson` (and binary counterparts).

## References

* [E. Ben-Sasson, I. Bentov, Y. Horesh, M. Riabzev, *Fast Reed–Solomon Interactive Oracle Proofs
  of Proximity*][BenSassonBentovHoreshRiabzev2018]
* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, *Proximity Gaps for Reed–Solomon
  Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024]
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Finset
open Cslib.Code
open Cslib.OracleComp
open Cslib.Crypto.Protocols.BCS
open Cslib.Probability

section Helpers

variable {F : Type} [Field F]

/-- Exact integer ceiling-division identity `⌈(M * N - e) / M⌉ = N - ⌊e / M⌋` for `0 < M` and
`e ≤ M * N`. -/
private theorem ceil_div_sub_eq_sub_div {M N e : ℕ} (hM : 0 < M) (he : e ≤ M * N) :
    (M * N - e + M - 1) / M = N - e / M := by
  have hmod : e % M < M := Nat.mod_lt e hM
  have hdiv : M * (e / M) + e % M = e := Nat.div_add_mod e M
  have hq_le : e / M ≤ N := by
    by_contra hgt
    have h1 : N + 1 ≤ e / M := by omega
    have h2 : M * (N + 1) ≤ M * (e / M) := Nat.mul_le_mul_left M h1
    have h3 : M * N + M ≤ e := by
      have : M * (N + 1) = M * N + M := by ring
      omega
    omega
  have hmul_sub : M * (N - e / M) = M * N - M * (e / M) := Nat.mul_sub M N (e / M)
  have hlo : (N - e / M) * M ≤ M * N - e + M - 1 := by
    rw [mul_comm (N - e / M) M, hmul_sub]
    omega
  have hhi : M * N - e + M - 1 < (N - e / M + 1) * M := by
    rw [add_mul, one_mul, mul_comm (N - e / M) M, hmul_sub]
    omega
  exact le_antisymm
    (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hM).mpr hhi))
    ((Nat.le_div_iff_mul_le hM).mpr hlo)

omit [Field F] in
private theorem sum_natCast_div_ennreal {ι : Type*} (s : Finset ι) (x : ι → ℕ) (D : ℕ) :
    (∑ i ∈ s, ((x i : ℕ) : ℝ≥0∞) / (D : ℝ≥0∞)) =
      ((∑ i ∈ s, x i : ℕ) : ℝ≥0∞) / (D : ℝ≥0∞) := by
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Nat.cast_sum]

omit [Field F] in
private theorem sum_div_le_div_sum {ι : Type*} (s : Finset ι) (x : ι → ℕ) {k₀ : ℕ}
    (hk₀ : 0 < k₀) :
    (∑ i ∈ s, x i / k₀) ≤ (∑ i ∈ s, x i) / k₀ := by
  refine (Nat.le_div_iff_mul_le hk₀).mpr ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => Nat.div_mul_le_self (x i) k₀

omit [Field F] in
private theorem natCast_div_eq_ofReal {N D : ℕ} (hD : 0 < D) :
    ((N : ℝ≥0∞) / (D : ℝ≥0∞)) = ENNReal.ofReal ((N : ℝ) / (D : ℝ)) := by
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  rw [ENNReal.ofReal_div_of_pos hDR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

private theorem cast_two_pow_sub_eq_smooth (params : FRISmoothParams F) :
    (((2 ^ params.d - 2 ^ (params.d - params.totalLog) : ℕ) : ℝ)) =
      (1 - (1 : ℝ) / (2 : ℝ) ^ params.totalLog) * ((2 : ℝ) ^ params.d) := by
  have hle : 2 ^ (params.d - params.totalLog) ≤ 2 ^ params.d :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  have hsplit : (2 : ℝ) ^ params.d =
      (2 : ℝ) ^ (params.d - params.totalLog) * (2 : ℝ) ^ params.totalLog := by
    rw [← pow_add, Nat.sub_add_cancel params.htotal]
  have h2t_ne : ((2 : ℝ) ^ params.totalLog) ≠ 0 := by positivity
  calc (((2 ^ params.d - 2 ^ (params.d - params.totalLog) : ℕ) : ℝ))
      = (2 : ℝ) ^ params.d - (2 : ℝ) ^ (params.d - params.totalLog) := by
          rw [Nat.cast_sub hle]
          push_cast
          rfl
    _ = (2 : ℝ) ^ (params.d - params.totalLog) * (2 : ℝ) ^ params.totalLog -
          (2 : ℝ) ^ (params.d - params.totalLog) *
            (((2 : ℝ) ^ params.totalLog) / ((2 : ℝ) ^ params.totalLog)) := by
          rw [← hsplit, div_self h2t_ne, mul_one]
    _ = (1 - (1 : ℝ) / (2 : ℝ) ^ params.totalLog) * ((2 : ℝ) ^ params.d) := by
          rw [hsplit]
          ring

private theorem sum_fin_arity_sub_one_succ {α : Type*} {a : ℕ} (ha : 1 ≤ a)
    (u : Fin a → α → F) (z : F) :
    (∑ r : Fin ((a - 1) + 1), z ^ r.val • u (finCongr (Nat.sub_add_cancel ha) r)) =
      ∑ r : Fin a, z ^ r.val • u r := by
  let eqA : Fin ((a - 1) + 1) ≃ Fin a := finCongr (Nat.sub_add_cancel ha)
  have hfun : (fun r : Fin ((a - 1) + 1) => z ^ r.val • u (eqA r)) =
      fun r => z ^ (eqA r).val • u (eqA r) := by
    funext r
    rfl
  rw [show (fun r : Fin ((a - 1) + 1) => z ^ r.val • u (finCongr (Nat.sub_add_cancel ha) r)) =
    fun r => z ^ (eqA r).val • u (eqA r) from hfun]
  exact Equiv.sum_comp eqA (fun r : Fin a => z ^ r.val • u r)

/-- At `params.toSmooth`, twice the round-`0` smooth folding drop
`2 ^ d - 2 ^ (d - firstStepLog)` is bounded by `2 ^ d`. -/
theorem two_mul_toSmooth_first_sub_le (params : FRIParams F) :
    2 * (2 ^ params.d - 2 ^ (params.d - params.toSmooth.firstStepLog)) ≤ 2 ^ params.d := by
  rw [params.toSmooth_firstStepLog]
  rcases Nat.eq_zero_or_pos params.d with hd | hd
  · simp [hd]
  · have hsplit : 2 ^ params.d = 2 * 2 ^ (params.d - 1) := by
      have : params.d = (params.d - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    omega

private theorem toSmooth_first_sub_eq_of_pos (params : FRIParams F) (hd : 0 < params.d) :
    2 ^ params.d - 2 ^ (params.d - params.toSmooth.firstStepLog) = 2 ^ (params.d - 1) := by
  rw [params.toSmooth_firstStepLog]
  have hsplit : 2 ^ params.d = 2 * 2 ^ (params.d - 1) := by
    have : params.d = (params.d - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ']
  omega

end Helpers

/-! ### Unconditional Smooth Unique-Decoding FRI, Summed IOP, & BCS-FRI ROM Soundness -/

section SmoothUniqueDecoding

variable {F : Type} [Field F]

/-- **Unconditional per-round unique-decoding `WeightedCurveGapPerRound`** across all `m`
single-word smooth FRI folding rounds (instantiating
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5 and 6.1] for degree-`(l⁽ⁱ⁾ - 1)` curves at
each round via `FRISmoothParams.two_mul_div_add_dim_le`).

Discharges `UniqueCurveGapHypothesis` directly from
`Cslib.Code.exists_correlatedAgreement_curve_unique` over any field `F` of characteristic `≠ 2`,
yielding per-round exceptional-scalar budget `(params.arity i - 1) * params.domainSize (i + 1)`
(telescoping over all `m` rounds to `2 ^ d - 2 ^ (d - totalLog) < 2 ^ d`) with zero gap-assumption
premise. -/
theorem weightedCurveGapPerRound_of_unique [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) :
    WeightedCurveGapPerRound params (2 ^ params.d - e - 1)
      (fun i => (params.arity i - 1) * params.domainSize (i.val + 1)) := by
  refine weightedCurveGapPerRound_of_uniqueCurveGap params huniq ?_
  intro i u Z hZ_gt hZ_close
  have ha : 1 ≤ params.arity i := le_trans (by omega) (params.two_le_arity i)
  let eqA : Fin ((params.arity i - 1) + 1) ≃ Fin (params.arity i) :=
    finCongr (Nat.sub_add_cancel ha)
  have huniq_i :
      2 * (e / 2 ^ params.cumLog (i.val + 1)) + params.dim (i.val + 1) ≤
        Fintype.card (Fin (params.domainSize (i.val + 1))) := by
    simpa only [Fintype.card_fin] using params.two_mul_div_add_dim_le huniq i
  have hα_inj : Function.Injective (params.eval (i.val + 1)) :=
    cosetEval_injective params.hg params.hω
      ((params.cumLog_le_totalLog i.isLt).trans params.htotal)
  have hclose' : ∀ z ∈ Z, ∃ c ∈ params.rsCode (i.val + 1),
      hammingDist (∑ r : Fin ((params.arity i - 1) + 1), z ^ r.val • u (eqA r)) c ≤
        e / 2 ^ params.cumLog (i.val + 1) := by
    intro z hz
    rw [sum_fin_arity_sub_one_succ ha u z]
    exact hZ_close z hz
  obtain ⟨D', hD'_card, v', hv', hD'_agree⟩ :=
    exists_correlatedAgreement_curve_unique hα_inj huniq_i (fun r => u (eqA r)) Z
      (by simpa only [Fintype.card_fin] using hZ_gt) hclose'
  refine ⟨D', fun r => v' (eqA.symm r), fun r => hv' (eqA.symm r),
    by simpa only [Fintype.card_fin] using hD'_card, fun j hj r => ?_⟩
  have h := hD'_agree j hj (eqA.symm r)
  simpa only [Equiv.apply_symm_apply] using h

/-- **Unconditional uniform unique-decoding `WeightedCurveGapBound`** for all `m` single-word smooth
FRI folding rounds (`B_commit = 2 ^ d - 2 ^ (d - firstStepLog)`), obtained as a monotonicity
corollary of `weightedCurveGapPerRound_of_unique`. -/
theorem weightedCurveGapBound_of_unique [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) :
    WeightedCurveGapBound params (2 ^ params.d - e - 1)
      (2 ^ params.d - 2 ^ (params.d - params.firstStepLog)) :=
  (weightedCurveGapPerRound_of_unique params huniq).mono
    params.arity_sub_one_mul_domainSize_le_first

/-- Closed-form telescoping commit-phase error `(1 - 1 / 2 ^ totalLog) * (2 ^ d / |F|)` across all
`m` single-word smooth FRI folding rounds in the unique-decoding regime (`< 2 ^ d / |F|`
independently of `m` and per-round arities `l⁽ⁱ⁾`). -/
@[expose] noncomputable def friSmoothUniqueCommitError [Fintype F]
    (params : FRISmoothParams F) : ℝ :=
  (1 - (1 : ℝ) / (2 : ℝ) ^ params.totalLog) * ((2 ^ params.d : ℝ) / (Fintype.card F : ℝ))

/-- Exact telescoping sum of per-round smooth unique-decoding folding escape budgets in `ℝ≥0∞`. -/
theorem sum_friSmoothUniqueRoundEscape_eq [Fintype F] (params : FRISmoothParams F) :
    (∑ i : Fin params.m,
      (((params.arity i - 1) * params.domainSize (i.val + 1) : ℕ) : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞)) =
    ENNReal.ofReal (friSmoothUniqueCommitError params) := by
  rw [sum_natCast_div_ennreal, params.sum_arity_sub_one_mul_domainSize,
    natCast_div_eq_ofReal Fintype.card_pos, cast_two_pow_sub_eq_smooth, mul_div_assoc,
    friSmoothUniqueCommitError]

/-- **Unconditional summed commit-phase soundness of single-word `friSmoothIOP` in the
unique-decoding regime**: for `stmt ∉ params.proximityLang e`, `friSmoothCommitGame` exceeds
agreement `2 ^ d - e - 1` with probability at most `(2 ^ d - 2 ^ (d - totalLog)) / |F|`
(`= ENNReal.ofReal (friSmoothUniqueCommitError params)`). -/
theorem friSmoothCommitGame_le_of_unique [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    friSmoothCommitGame params (2 ^ params.d - e - 1) stmt P true ≤
      ((2 ^ params.d - 2 ^ (params.d - params.totalLog) : ℕ) : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) := by
  refine (friSmoothCommitGame_le_of_weightedCurveGapPerRound params
    (weightedCurveGapPerRound_of_unique params huniq) hfar P).trans_eq ?_
  rw [sum_natCast_div_ennreal, params.sum_arity_sub_one_mul_domainSize]

/-- **Unconditional summed interactive soundness of single-word `friSmoothIOP` in the
unique-decoding regime**: for `stmt ∉ params.proximityLang e` and any adaptive prover `P`, the
acceptance probability is at most
`(2 ^ d - 2 ^ (d - totalLog)) / |F| + ((2 ^ d - e - 1) / 2 ^ d) ^ q` (telescoping independently of
`m` and per-round arities `l⁽ⁱ⁾`). -/
theorem friSmoothIOP_interactiveGame_le_of_unique [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    iopInteractiveGame (friSmoothIOP params) stmt P true ≤
      ((2 ^ params.d - 2 ^ (params.d - params.totalLog) : ℕ) : ℝ≥0∞) /
          (Fintype.card F : ℝ≥0∞) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  refine (friSmoothIOP_interactiveGame_le_of_weightedCurveGapPerRound params
    (weightedCurveGapPerRound_of_unique params huniq) hfar P).trans_eq ?_
  rw [friSmoothSumError, sum_natCast_div_ennreal, params.sum_arity_sub_one_mul_domainSize]

/-- **Unconditional round-by-round soundness of single-word `friSmoothIOP` in the unique-decoding
regime** ([BenSassonBentovHoreshRiabzev2018];
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5 and 6.1]). -/
theorem friSmoothIOP_rbrSound_of_unique [Fintype F] [DecidableEq F] (params : FRISmoothParams F)
    {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) :
    IOPRoundByRoundSoundness (friSmoothIOP params) (params.proximityLang e)
      (friSmoothDoomed params (2 ^ params.d - e - 1))
      (friSmoothGoodStep params (2 ^ params.d - e - 1)) ∧
    ∀ stmt ∉ params.proximityLang e, ∀ pref π,
      friSmoothDoomed params (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params (2 ^ params.d - e - 1) stmt pref π c} ≤
      friSmoothRBRError params e (2 ^ params.d - 2 ^ (params.d - params.firstStepLog)) :=
  ⟨friSmoothIOP_rbrSound params e,
    friSmoothRBREscape_of_weightedCurveGap params (weightedCurveGapBound_of_unique params huniq)⟩

/-- **Unconditional adaptive smooth BCS-FRI ROM soundness in the unique-decoding regime**
([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]), composing `weightedCurveGapBound_of_unique`
with `friSmoothBCS_romSoundness_bound_of_weightedCurveGap`. -/
theorem friSmoothBCS_romSoundness_bound_of_unique [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friSmoothIOP params) encSym (params.proximityLang e) P) Q_MT) :
    bcsSoundnessGame (friSmoothIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSmoothRBRError params e (2 ^ params.d - 2 ^ (params.d - params.firstStepLog)) +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friSmoothBCS_romSoundness_bound_of_weightedCurveGap params
    (weightedCurveGapBound_of_unique params huniq) hdec σ hFS hMT

/-- **Unconditional adaptive smooth BCS-FRI ROM soundness with separate prover/verifier Merkle
budgets in the unique-decoding regime** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]). -/
theorem friSmoothBCS_romSoundness_bound_of_prover_verifier_of_unique [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friSmoothIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSmoothRBRError params e (2 ^ params.d - 2 ^ (params.d - params.firstStepLog)) +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friSmoothBCS_romSoundness_bound_of_prover_verifier_of_weightedCurveGap params
    (weightedCurveGapBound_of_unique params huniq) hdec σ hMT hFS hops

end SmoothUniqueDecoding

/-! ### Unconditional Smooth Johnson-Bound FRI, Summed IOP, & BCS-FRI ROM Soundness -/

section SmoothJohnsonBound

variable {F : Type} [Field F]

/-- Per-round smooth Siegel-interpolation bad-scalar bound for single-word smooth FRI in the
Johnson regime with multiplicity slack `mJ` at folding round `i : Fin params.m`:
`(1800 * (mJ + 1) ^ 6 * ((params.arity i - 1) * params.domainSize (i.val + 1)) *
(2 ^ params.d) ^ 2) / params.dim 0` (using this library's original explicit Siegel constant
`1800 * (mJ + 1) ^ 6`, telescoping over all `m` rounds without an `O(m)` factor). -/
abbrev friSmoothJohnsonRoundBound (params : FRISmoothParams F) (mJ : ℕ) (i : Fin params.m) : ℕ :=
  (1800 * (mJ + 1) ^ 6 * ((params.arity i - 1) * params.domainSize (i.val + 1)) *
    (2 ^ params.d) ^ 2) / params.dim 0

/-- Conservative uniform per-round commit-phase exceptional-scalar bound for single-word smooth FRI
in the Johnson regime with multiplicity slack `mJ`:
`(1800 * (mJ + 1) ^ 6 * (2 ^ params.d - 2 ^ (params.d - params.firstStepLog)) *
(2 ^ params.d) ^ 2) / params.dim 0`. -/
abbrev friSmoothJohnsonCommitBound (params : FRISmoothParams F) (mJ : ℕ) : ℕ :=
  (1800 * (mJ + 1) ^ 6 * (2 ^ params.d - 2 ^ (params.d - params.firstStepLog)) *
    (2 ^ params.d) ^ 2) / params.dim 0

/-- At round `0`, `friSmoothJohnsonRoundBound` coincides exactly with
`friSmoothJohnsonCommitBound`. -/
theorem friSmoothJohnsonRoundBound_zero (params : FRISmoothParams F) (mJ : ℕ) (hm : 0 < params.m) :
    friSmoothJohnsonRoundBound params mJ ⟨0, hm⟩ = friSmoothJohnsonCommitBound params mJ := by
  have h0 : (params.arity ⟨0, hm⟩ - 1) * params.domainSize 1 =
      2 ^ params.d - 2 ^ (params.d - params.firstStepLog) := by
    have hsplit := params.domainSize_eq_arity_mul_succ ⟨0, hm⟩
    have hdom0 : params.domainSize 0 = 2 ^ params.d := by
      simp [FRISmoothParams.domainSize, FRISmoothParams.cumLog]
    have hdom1 : params.domainSize 1 = 2 ^ (params.d - params.firstStepLog) := by
      have hcum1 : params.cumLog 1 = params.firstStepLog := by
        rw [params.cumLog_succ ⟨0, hm⟩, FRISmoothParams.cumLog, friCumLog_zero, Nat.zero_add]
        simp only [FRISmoothParams.firstStepLog, hm, ↓reduceDIte]
      simp only [FRISmoothParams.domainSize, hcum1]
    rw [Nat.sub_mul, one_mul, ← hsplit, hdom0, hdom1]
  simp only [friSmoothJohnsonRoundBound, friSmoothJohnsonCommitBound, Nat.zero_add, h0]

/-- Every folding round's smooth Johnson budget `friSmoothJohnsonRoundBound params mJ i` is bounded
by the round-`0` uniform budget `friSmoothJohnsonCommitBound params mJ`. -/
theorem friSmoothJohnsonRoundBound_le_commitBound (params : FRISmoothParams F) (mJ : ℕ)
    (i : Fin params.m) :
    friSmoothJohnsonRoundBound params mJ i ≤ friSmoothJohnsonCommitBound params mJ := by
  refine Nat.div_le_div_right ?_
  exact Nat.mul_le_mul_right _
    (Nat.mul_le_mul_left _ (params.arity_sub_one_mul_domainSize_le_first i))

/-- Telescoping upper bound on the integer sum of `friSmoothJohnsonRoundBound` across all `m`
smooth folding rounds (bounded independently of `m` and per-round arities `l⁽ⁱ⁾`). -/
theorem sum_friSmoothJohnsonRoundBound_le (params : FRISmoothParams F) (mJ : ℕ) :
    (∑ i : Fin params.m, friSmoothJohnsonRoundBound params mJ i) ≤
      (1800 * (mJ + 1) ^ 6 * (2 ^ params.d - 2 ^ (params.d - params.totalLog)) *
        (2 ^ params.d) ^ 2) / params.dim 0 := by
  refine (sum_div_le_div_sum Finset.univ _ (params.one_le_dim 0)).trans_eq ?_
  congr 1
  calc (∑ i : Fin params.m,
        1800 * (mJ + 1) ^ 6 * ((params.arity i - 1) * params.domainSize (i.val + 1)) *
          (2 ^ params.d) ^ 2)
      = ∑ i : Fin params.m,
          ((params.arity i - 1) * params.domainSize (i.val + 1)) *
            (1800 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 2) := by
          refine Finset.sum_congr rfl fun _ _ => ?_
          ring
    _ = (∑ i : Fin params.m, (params.arity i - 1) * params.domainSize (i.val + 1)) *
          (1800 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 2) := (Finset.sum_mul _ _ _).symm
    _ = 1800 * (mJ + 1) ^ 6 * (2 ^ params.d - 2 ^ (params.d - params.totalLog)) *
          (2 ^ params.d) ^ 2 := by
          rw [params.sum_arity_sub_one_mul_domainSize]
          ring

/-- Closed-form telescoping Siegel commit-phase error across all `m` single-word smooth FRI folding
rounds in the Johnson regime:
`(1 - 1 / 2 ^ totalLog) * (1800 * (mJ + 1) ^ 6 * (2 ^ d) ^ 2 / ((dim 0 / 2 ^ d) * |F|))`
(bounded independently of `m` and per-round arities `l⁽ⁱ⁾`; uses this library's original explicit
Siegel constant). -/
@[expose] noncomputable def friSmoothJohnsonCommitError [Fintype F]
    (params : FRISmoothParams F) (mJ : ℕ) : ℝ :=
  (1 - (1 : ℝ) / (2 : ℝ) ^ params.totalLog) *
    (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
      (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ)))

/-- Telescoping sum of per-round smooth Johnson escape probabilities bounded by
`friSmoothJohnsonCommitError`. -/
theorem sum_friSmoothJohnsonRoundEscape_le [Fintype F] (params : FRISmoothParams F) (mJ : ℕ) :
    (∑ i : Fin params.m,
      (friSmoothJohnsonRoundBound params mJ i : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ≤
    ENNReal.ofReal (friSmoothJohnsonCommitError params mJ) := by
  let num : ℕ :=
    1800 * (mJ + 1) ^ 6 * (2 ^ params.d - 2 ^ (params.d - params.totalLog)) * (2 ^ params.d) ^ 2
  have hsum_nat :
      (∑ i : Fin params.m, friSmoothJohnsonRoundBound params mJ i) ≤ num / params.dim 0 :=
    sum_friSmoothJohnsonRoundBound_le params mJ
  have hk₀_pos : 0 < params.dim 0 := params.one_le_dim 0
  have hk₀R : (0 : ℝ) < (params.dim 0 : ℝ) := by exact_mod_cast hk₀_pos
  have hn₀R_ne : ((2 ^ params.d : ℝ)) ≠ 0 := by positivity
  have hFR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [sum_natCast_div_ennreal]
  refine (ENNReal.div_le_div_right (Nat.cast_le.mpr hsum_nat) _).trans ?_
  rw [natCast_div_eq_ofReal Fintype.card_pos]
  refine ENNReal.ofReal_le_ofReal ?_
  have hdiv_le : ((num / params.dim 0 : ℕ) : ℝ) ≤ (num : ℝ) / (params.dim 0 : ℝ) :=
    (le_div_iff₀ hk₀R).mpr (by exact_mod_cast Nat.div_mul_le_self num (params.dim 0))
  refine (div_le_div_of_nonneg_right hdiv_le hFR.le).trans_eq ?_
  have hnumR :
      (num : ℝ) =
        (1 - (1 : ℝ) / (2 : ℝ) ^ params.totalLog) *
          (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) * (2 ^ params.d : ℝ)) := by
    dsimp only [num]
    push_cast
    rw [cast_two_pow_sub_eq_smooth]
    ring
  rw [hnumR, friSmoothJohnsonCommitError]
  field_simp

/-- **Explicit-parameter Guruswami–Sudan per-round `WeightedCurveGapPerRound`** across all `m`
single-word smooth FRI folding rounds (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5, 6.2, and 7.2], with exact degree-`(l⁽ⁱ⁾ - 1)`
`Cslib.Code.ProximityGap.johnsonCurveBound` budgets). -/
theorem weightedCurveGapPerRound_of_johnson_discrete [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} (he : e < 2 ^ params.d)
    (mRound DRound : Fin params.m → ℕ)
    (hm : ∀ i : Fin params.m, 1 ≤ mRound i)
    (hk_le : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤
        params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1))
    (hinterp : ∀ i : Fin params.m,
      params.domainSize (i.val + 1) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)))
    (hroot : ∀ i : Fin params.m,
      DRound i <
        mRound i * (params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1))) :
    WeightedCurveGapPerRound params (2 ^ params.d - e - 1)
      (fun i => ProximityGap.johnsonCurveBound (params.domainSize (i.val + 1)) (mRound i)
        (params.dim (i.val + 1) - 1) (DRound i) (params.arity i - 1) (2 ^ params.d)) := by
  intro i W hW_le hW_sum u hno_corr Z hZ_good
  by_contra hgt
  let M : ℕ := 2 ^ params.cumLog (i.val + 1)
  let N : ℕ := params.domainSize (i.val + 1)
  let B_W : ℕ := 2 ^ params.d - e
  have hM_pos : 0 < M := Nat.pow_pos (by omega)
  have hMN : M * N = 2 ^ params.d := params.two_pow_cumLog_mul_domainSize i.isLt
  have ha : 1 ≤ params.arity i := le_trans (by omega) (params.two_le_arity i)
  let eqA : Fin ((params.arity i - 1) + 1) ≃ Fin (params.arity i) :=
    finCongr (Nat.sub_add_cancel ha)
  have hceil : (B_W + M - 1) / M = N - e / M := by
    dsimp only [B_W]
    rw [← hMN]
    exact ceil_div_sub_eq_sub_div hM_pos (by rw [hMN]; exact he.le)
  have hα_inj : Function.Injective (params.eval (i.val + 1)) :=
    cosetEval_injective params.hg params.hω
      ((params.cumLog_le_totalLog i.isLt).trans params.htotal)
  have hZ_gt :
      ProximityGap.johnsonCurveBound (Fintype.card (Fin N)) (mRound i)
        (params.dim (i.val + 1) - 1) (DRound i) (params.arity i - 1) (2 ^ params.d) < #Z := by
    rw [Fintype.card_fin]
    exact Nat.lt_of_not_ge hgt
  have hclose : ∀ z ∈ Z, ∃ c ∈ params.rsCode (i.val + 1),
      B_W ≤ ∑ j ∈ Finset.univ.filter
        (fun j => (∑ r : Fin ((params.arity i - 1) + 1), z ^ r.val • u (eqA r)) j = c j), W j := by
    intro z hz
    obtain ⟨c, hc_rs, hc_wt⟩ := hZ_good z hz
    refine ⟨c, hc_rs, ?_⟩
    rw [sum_fin_arity_sub_one_succ ha u z]
    dsimp only [B_W]
    omega
  obtain ⟨D', hD'_wt, v', hv', hD'_agree⟩ :=
    exists_weighted_correlatedAgreement_curve_johnson (W := W) (M := M) (W_tot := 2 ^ params.d)
      (B_W := B_W) hα_inj (params.one_le_dim (i.val + 1)) (hm i) hM_pos hW_le hW_sum
      (by rw [hceil]; exact hk_le i)
      (by rw [Fintype.card_fin]; exact hinterp i)
      (by rw [hceil]; exact hroot i)
      (fun r => u (eqA r)) Z hZ_gt hclose
  let v : Fin (params.arity i) → Fin N → F := fun r => v' (eqA.symm r)
  have hv : ∀ r, v r ∈ params.rsCode (i.val + 1) := fun r => hv' (eqA.symm r)
  have hsub :
      D' ⊆ Finset.univ.filter (fun j : Fin N => ∀ r : Fin (params.arity i), u r j = v r j) := by
    intro j hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ j, fun r => ?_⟩
    have h := hD'_agree j hj (eqA.symm r)
    simpa only [v, Equiv.apply_symm_apply] using h
  have hle_B : B_W ≤ 2 ^ params.d - e - 1 :=
    hD'_wt.trans ((Finset.sum_le_sum_of_subset hsub).trans (hno_corr v hv))
  dsimp only [B_W] at hle_B
  omega

/-- **Explicit-parameter Guruswami–Sudan uniform `WeightedCurveGapBound`** for all `m` single-word
smooth FRI folding rounds, derived as a monotonicity corollary of
`weightedCurveGapPerRound_of_johnson_discrete`. -/
theorem weightedCurveGapBound_of_johnson_discrete [DecidableEq F]
    (params : FRISmoothParams F) {e B_commit : ℕ} (he : e < 2 ^ params.d)
    (mRound DRound : Fin params.m → ℕ)
    (hm : ∀ i : Fin params.m, 1 ≤ mRound i)
    (hk_le : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤
        params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1))
    (hinterp : ∀ i : Fin params.m,
      params.domainSize (i.val + 1) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)))
    (hroot : ∀ i : Fin params.m,
      DRound i <
        mRound i * (params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1)))
    (hbound : ∀ i : Fin params.m,
      ProximityGap.johnsonCurveBound (params.domainSize (i.val + 1)) (mRound i)
        (params.dim (i.val + 1) - 1) (DRound i) (params.arity i - 1) (2 ^ params.d) ≤ B_commit) :
    WeightedCurveGapBound params (2 ^ params.d - e - 1) B_commit :=
  (weightedCurveGapPerRound_of_johnson_discrete params he mRound DRound hm hk_le hinterp hroot).mono
    hbound

/-- **Explicit-parameter Guruswami–Sudan step toward summed commit-phase soundness of single-word
`friSmoothIOP`**. -/
theorem friSmoothCommitGame_le_of_johnson_discrete [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} (he : e < 2 ^ params.d)
    (mRound DRound : Fin params.m → ℕ)
    (hm : ∀ i : Fin params.m, 1 ≤ mRound i)
    (hk_le : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤
        params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1))
    (hinterp : ∀ i : Fin params.m,
      params.domainSize (i.val + 1) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)))
    (hroot : ∀ i : Fin params.m,
      DRound i <
        mRound i * (params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1)))
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    friSmoothCommitGame params (2 ^ params.d - e - 1) stmt P true ≤
      ((∑ i : Fin params.m,
        ProximityGap.johnsonCurveBound (params.domainSize (i.val + 1)) (mRound i)
          (params.dim (i.val + 1) - 1) (DRound i) (params.arity i - 1) (2 ^ params.d) : ℕ) :
        ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  refine (friSmoothCommitGame_le_of_weightedCurveGapPerRound params
    (weightedCurveGapPerRound_of_johnson_discrete params he mRound DRound hm hk_le hinterp hroot)
    hfar P).trans_eq ?_
  exact sum_natCast_div_ennreal Finset.univ _ _

/-- **Explicit-parameter Guruswami–Sudan step toward summed interactive soundness of single-word
`friSmoothIOP`**. -/
theorem friSmoothIOP_interactiveGame_le_of_johnson_discrete [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} (he : e < 2 ^ params.d)
    (mRound DRound : Fin params.m → ℕ)
    (hm : ∀ i : Fin params.m, 1 ≤ mRound i)
    (hk_le : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤
        params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1))
    (hinterp : ∀ i : Fin params.m,
      params.domainSize (i.val + 1) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)))
    (hroot : ∀ i : Fin params.m,
      DRound i <
        mRound i * (params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1)))
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    iopInteractiveGame (friSmoothIOP params) stmt P true ≤
      ((∑ i : Fin params.m,
          ProximityGap.johnsonCurveBound (params.domainSize (i.val + 1)) (mRound i)
            (params.dim (i.val + 1) - 1) (DRound i) (params.arity i - 1) (2 ^ params.d) : ℕ) :
          ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  refine (friSmoothIOP_interactiveGame_le_of_weightedCurveGapPerRound params
    (weightedCurveGapPerRound_of_johnson_discrete params he mRound DRound hm hk_le hinterp hroot)
    hfar P).trans_eq ?_
  rw [friSmoothSumError, sum_natCast_div_ennreal]

/-- **Original explicit-constant per-round Johnson-bound `WeightedCurveGapPerRound`** across all `m`
single-word smooth FRI folding rounds up to `δ ≤ 1 - √ρ - √ρ / (2 * mJ)` (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5, 6.2, and 7.2], using this library's explicit
Siegel constants).

Reuses `Cslib.Code.ProximityGap.johnson_curve_params_bound` (at degree `r = params.arity i - 1 ≥ 1`)
and `Cslib.Code.ProximityGap.johnsonCurveBound_mul_le` at every round `i : Fin params.m`, retaining
the telescoping factor `(params.arity i - 1) * params.domainSize (i + 1)` in
`friSmoothJohnsonRoundBound params mJ i` so the sum over all `m` rounds stays independent of `m`
and the per-round arities `l⁽ⁱ⁾`. -/
theorem weightedCurveGapPerRound_of_johnson [DecidableEq F]
    (params : FRISmoothParams F) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ))) :
    WeightedCurveGapPerRound params (2 ^ params.d - e - 1)
      (friSmoothJohnsonRoundBound params mJ) := by
  set n₀ : ℕ := 2 ^ params.d
  set k₀ : ℕ := params.dim 0
  have hn₀_pos : 0 < n₀ := Nat.pow_pos (by omega)
  have hk₀_pos : 0 < k₀ := params.one_le_dim 0
  have hn₀R : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast hn₀_pos
  have hk₀R : (0 : ℝ) < (k₀ : ℝ) := by exact_mod_cast hk₀_pos
  have hsqρ_pos : 0 < Real.sqrt ((k₀ : ℝ) / (n₀ : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hmJR : (0 : ℝ) < (mJ : ℝ) := by exact_mod_cast hmJ
  have he_lt : e < n₀ := by
    have hfrac_lt : (e : ℝ) / (n₀ : ℝ) < 1 := by
      have hterm : 0 < Real.sqrt ((k₀ : ℝ) / (n₀ : ℝ)) / (2 * (mJ : ℝ)) := by positivity
      have he' : (e : ℝ) / (n₀ : ℝ) ≤
          1 - Real.sqrt ((k₀ : ℝ) / (n₀ : ℝ)) -
            Real.sqrt ((k₀ : ℝ) / (n₀ : ℝ)) / (2 * (mJ : ℝ)) := by
        simpa only [n₀, k₀, Nat.cast_pow, Nat.cast_ofNat] using he
      linarith
    have heR : (e : ℝ) < (n₀ : ℝ) := (div_lt_one hn₀R).mp hfrac_lt
    exact_mod_cast heR
  let mRound : Fin params.m → ℕ := fun _ => mJ + 1
  let DRound : Fin params.m → ℕ := fun i =>
    (mJ + 1) * ⌈(1 + 1 / (2 * (mJ : ℝ))) *
      Real.sqrt ((params.domainSize (i.val + 1) : ℝ) * (params.dim (i.val + 1) : ℝ))⌉₊ - 1
  have hround_rate : ∀ i : Fin params.m,
      ((params.dim (i.val + 1) : ℝ) / (params.domainSize (i.val + 1) : ℝ)) =
        (k₀ : ℝ) / (n₀ : ℝ) := by
    intro i
    have hMN : (2 ^ params.cumLog (i.val + 1) : ℝ) * (params.domainSize (i.val + 1) : ℝ) =
        (n₀ : ℝ) := by
      exact_mod_cast params.two_pow_cumLog_mul_domainSize i.isLt
    have hMk : (2 ^ params.cumLog (i.val + 1) : ℝ) * (params.dim (i.val + 1) : ℝ) =
        (k₀ : ℝ) := by
      exact_mod_cast params.two_pow_cumLog_mul_dim i.isLt
    have hM_ne : (2 ^ params.cumLog (i.val + 1) : ℝ) ≠ 0 := by positivity
    rw [← hMk, ← hMN, mul_div_mul_left _ _ hM_ne]
  have hround_he : ∀ i : Fin params.m,
      ((e / 2 ^ params.cumLog (i.val + 1) : ℕ) : ℝ) / (params.domainSize (i.val + 1) : ℝ) ≤
        1 - Real.sqrt ((params.dim (i.val + 1) : ℝ) / (params.domainSize (i.val + 1) : ℝ)) -
          Real.sqrt ((params.dim (i.val + 1) : ℝ) / (params.domainSize (i.val + 1) : ℝ)) /
            (2 * (mJ : ℝ)) := by
    intro i
    rw [hround_rate i]
    have hle_e :
        ((e / 2 ^ params.cumLog (i.val + 1) : ℕ) : ℝ) / (params.domainSize (i.val + 1) : ℝ) ≤
        (e : ℝ) / (n₀ : ℝ) := by
      have hMN : (2 ^ params.cumLog (i.val + 1) : ℝ) * (params.domainSize (i.val + 1) : ℝ) =
          (n₀ : ℝ) := by
        exact_mod_cast params.two_pow_cumLog_mul_domainSize i.isLt
      have hdiv_le :
          ((e / 2 ^ params.cumLog (i.val + 1) : ℕ) : ℝ) * (2 ^ params.cumLog (i.val + 1) : ℝ) ≤
            (e : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self e (2 ^ params.cumLog (i.val + 1))
      have hniR : (0 : ℝ) < (params.domainSize (i.val + 1) : ℝ) := by
        exact_mod_cast (Nat.pow_pos (by omega) : 0 < params.domainSize (i.val + 1))
      rw [div_le_div_iff₀ hniR hn₀R, ← hMN]
      nlinarith
    have he' : (e : ℝ) / (n₀ : ℝ) ≤
        1 - Real.sqrt ((k₀ : ℝ) / (n₀ : ℝ)) -
          Real.sqrt ((k₀ : ℝ) / (n₀ : ℝ)) / (2 * (mJ : ℝ)) := by
      simpa only [n₀, k₀, Nat.cast_pow, Nat.cast_ofNat] using he
    exact hle_e.trans he'
  have hparams : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤
        params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1) ∧
      params.domainSize (i.val + 1) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)) ∧
      DRound i <
        mRound i * (params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1)) ∧
      (ProximityGap.johnsonCurveBound (params.domainSize (i.val + 1)) (mRound i)
        (params.dim (i.val + 1) - 1) (DRound i) (params.arity i - 1)
        (params.domainSize (i.val + 1)) : ℝ) ≤
        1800 * ((params.arity i - 1 : ℕ) : ℝ) * ((mJ + 1 : ℝ) ^ 6) *
          ((params.domainSize (i.val + 1) : ℝ) ^ 2) /
          ((params.dim (i.val + 1) : ℝ) / (params.domainSize (i.val + 1) : ℝ)) := by
    intro i
    have hr : 1 ≤ params.arity i - 1 := by
      have := params.two_le_arity i
      omega
    exact ProximityGap.johnson_curve_params_bound
      (n := params.domainSize (i.val + 1)) (k := params.dim (i.val + 1))
      (e := e / 2 ^ params.cumLog (i.val + 1)) (m := mJ) (r := params.arity i - 1)
      (params.one_le_dim (i.val + 1))
      (params.dim_le_domainSize i.isLt)
      hmJ hr (hround_he i)
  refine (weightedCurveGapPerRound_of_johnson_discrete params he_lt mRound DRound
    (fun _ => by dsimp only [mRound]; omega)
    (fun i => (hparams i).1)
    (fun i => (hparams i).2.1)
    (fun i => (hparams i).2.2.1)).mono fun i => ?_
  set ni : ℕ := params.domainSize (i.val + 1)
  set ki : ℕ := params.dim (i.val + 1)
  set ri : ℕ := params.arity i - 1
  have hni_pos : 0 < ni := Nat.pow_pos (by omega)
  have hniR : (0 : ℝ) < (ni : ℝ) := by exact_mod_cast hni_pos
  have hni_le : ni ≤ n₀ :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le params.d _)
  have hscale_nat := ProximityGap.johnsonCurveBound_mul_le
    (n := ni) (m := mRound i) (d := ki - 1) (D := DRound i) (r := ri) (W_tot := n₀) hni_le
  have hscaleR :
      (ProximityGap.johnsonCurveBound ni (mRound i) (ki - 1) (DRound i) ri n₀ : ℝ) * (ni : ℝ) ≤
      (ProximityGap.johnsonCurveBound ni (mRound i) (ki - 1) (DRound i) ri ni : ℝ) * (n₀ : ℝ) := by
    exact_mod_cast hscale_nat
  have hjb_i :
      (ProximityGap.johnsonCurveBound ni (mRound i) (ki - 1) (DRound i) ri ni : ℝ) ≤
        1800 * (ri : ℝ) * ((mJ + 1 : ℝ) ^ 6) * ((ni : ℝ) ^ 2) / ((k₀ : ℝ) / (n₀ : ℝ)) := by
    have h := (hparams i).2.2.2
    rw [hround_rate i] at h
    exact h
  have hmul_R :
      (ProximityGap.johnsonCurveBound ni (mRound i) (ki - 1) (DRound i) ri n₀ : ℝ) * (k₀ : ℝ) ≤
        1800 * ((mJ + 1 : ℝ) ^ 6) * ((ri : ℝ) * (ni : ℝ)) * ((n₀ : ℝ) ^ 2) := by
    have h1 :
        (ProximityGap.johnsonCurveBound ni (mRound i) (ki - 1) (DRound i) ri n₀ : ℝ) * (ni : ℝ) ≤
          (1800 * (ri : ℝ) * ((mJ + 1 : ℝ) ^ 6) * ((ni : ℝ) ^ 2) / ((k₀ : ℝ) / (n₀ : ℝ))) *
            (n₀ : ℝ) :=
      hscaleR.trans (mul_le_mul_of_nonneg_right hjb_i hn₀R.le)
    have h2 :
        (1800 * (ri : ℝ) * ((mJ + 1 : ℝ) ^ 6) * ((ni : ℝ) ^ 2) / ((k₀ : ℝ) / (n₀ : ℝ))) *
            (n₀ : ℝ) * (k₀ : ℝ) =
        1800 * ((mJ + 1 : ℝ) ^ 6) * ((ri : ℝ) * (ni : ℝ)) * ((n₀ : ℝ) ^ 2) * (ni : ℝ) := by
      field_simp
    have h1k := mul_le_mul_of_nonneg_right h1 hk₀R.le
    rw [h2] at h1k
    exact le_of_mul_le_mul_right (by linarith) hniR
  have hmul_nat :
      ProximityGap.johnsonCurveBound ni (mRound i) (ki - 1) (DRound i) ri n₀ * k₀ ≤
        1800 * (mJ + 1) ^ 6 * (ri * ni) * n₀ ^ 2 := by
    exact_mod_cast hmul_R
  exact (Nat.le_div_iff_mul_le hk₀_pos).mpr hmul_nat

/-- **Original explicit-constant uniform Johnson-bound `WeightedCurveGapBound`** for all `m`
single-word smooth FRI folding rounds up to `δ ≤ 1 - √ρ - √ρ / (2 * mJ)`
(`friSmoothJohnsonCommitBound params mJ`, in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5, 6.2, and 7.2]), obtained as a monotonicity
corollary of `weightedCurveGapPerRound_of_johnson` and `friSmoothJohnsonRoundBound_le_commitBound`.
-/
theorem weightedCurveGapBound_of_johnson [DecidableEq F]
    (params : FRISmoothParams F) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ))) :
    WeightedCurveGapBound params (2 ^ params.d - e - 1)
      (friSmoothJohnsonCommitBound params mJ) :=
  (weightedCurveGapPerRound_of_johnson params hmJ he).mono
    (friSmoothJohnsonRoundBound_le_commitBound _ _)

/-- Conservative uniform per-round commit-phase exceptional-scalar budget for smooth FRI in the
`η`-gap Johnson regime (`(e : ℝ) / 2 ^ d ≤ 1 - √ρ - η`, `0 < η`):
`⌊115200 * (2 ^ d - 2 ^ (d - firstStepLog)) * (2 ^ d) ^ 2 / (dim 0 * η ^ 6)⌋₊` (using this
library's original explicit Siegel constant `1800 * 64 = 115200` and `η` directly rather than
`min(η, √ρ / 20)` in Eq. (1.3)). -/
@[expose] noncomputable def friSmoothJohnsonEtaCommitBound (params : FRISmoothParams F) (η : ℝ) :
    ℕ :=
  ⌊115200 * ((2 ^ params.d - 2 ^ (params.d - params.firstStepLog) : ℕ) : ℝ) *
      ((2 ^ params.d : ℝ) ^ 2) / ((params.dim 0 : ℝ) * (η ^ 6))⌋₊

/-- **Original explicit-constant `η`-gap uniform `WeightedCurveGapBound`** across all `m` smooth FRI
folding rounds up to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - η` (`0 < η`), derived from
`weightedCurveGapBound_of_johnson` and `ProximityGap.exists_multiplicity_of_eta` (using `η` directly
rather than `min(η, √ρ / 20)` in Eq. (1.3)). -/
theorem weightedCurveGapBound_of_johnson_eta [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η) :
    WeightedCurveGapBound params (2 ^ params.d - e - 1)
      (friSmoothJohnsonEtaCommitBound params η) := by
  have hk₀_pos : 0 < params.dim 0 := params.one_le_dim 0
  have hk₀_le : params.dim 0 ≤ 2 ^ params.d := by
    simpa only [FRISmoothParams.domainSize, FRISmoothParams.cumLog, friCumLog_zero, Nat.sub_zero]
      using params.dim_le_domainSize (Nat.zero_le params.m)
  obtain ⟨mJ, hmJ, he_mJ, hpow_mJ⟩ :=
    ProximityGap.exists_multiplicity_of_eta hk₀_pos hk₀_le hη
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using he)
  refine (weightedCurveGapBound_of_johnson params hmJ
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using he_mJ)).mono fun _ => ?_
  refine Nat.le_floor ?_
  have hk₀R : (0 : ℝ) < (params.dim 0 : ℝ) := by exact_mod_cast hk₀_pos
  set F0 : ℕ := 2 ^ params.d - 2 ^ (params.d - params.firstStepLog)
  have hdiv_le :
      ((friSmoothJohnsonCommitBound params mJ : ℕ) : ℝ) ≤
        (1800 * ((mJ + 1 : ℝ) ^ 6) * (F0 : ℝ) * ((2 ^ params.d : ℝ) ^ 2)) /
          (params.dim 0 : ℝ) := by
    refine (le_div_iff₀ hk₀R).mpr ?_
    exact_mod_cast Nat.div_mul_le_self
      (1800 * (mJ + 1) ^ 6 * F0 * (2 ^ params.d) ^ 2) (params.dim 0)
  calc ((friSmoothJohnsonCommitBound params mJ : ℕ) : ℝ)
      ≤ (1800 * ((mJ + 1 : ℝ) ^ 6) * (F0 : ℝ) * ((2 ^ params.d : ℝ) ^ 2)) /
          (params.dim 0 : ℝ) := hdiv_le
    _ ≤ (1800 * (64 / (η ^ 6)) * (F0 : ℝ) * ((2 ^ params.d : ℝ) ^ 2)) /
          (params.dim 0 : ℝ) := by gcongr
    _ = 115200 * (F0 : ℝ) * ((2 ^ params.d : ℝ) ^ 2) / ((params.dim 0 : ℝ) * (η ^ 6)) := by
        field_simp
        ring

/-- **Original explicit-constant Johnson summed commit-phase soundness of single-word
`friSmoothIOP`** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], using this library's
explicit telescoping Siegel commit error `friSmoothJohnsonCommitError params mJ`, bounded
independently of `m` and per-round arities `l⁽ⁱ⁾`). -/
theorem friSmoothCommitGame_le_of_johnson [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    friSmoothCommitGame params (2 ^ params.d - e - 1) stmt P true ≤
      ENNReal.ofReal (friSmoothJohnsonCommitError params mJ) :=
  (friSmoothCommitGame_le_of_weightedCurveGapPerRound params
    (weightedCurveGapPerRound_of_johnson params hmJ he) hfar P).trans
    (sum_friSmoothJohnsonRoundEscape_le params mJ)

/-- **Original explicit-constant Johnson summed interactive soundness of single-word
`friSmoothIOP`** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], using
`friSmoothJohnsonCommitError params mJ` plus query error `((2 ^ d - e - 1) / 2 ^ d) ^ q`, bounded
independently of `m` and per-round arities `l⁽ⁱ⁾`). -/
theorem friSmoothIOP_interactiveGame_le_of_johnson [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    iopInteractiveGame (friSmoothIOP params) stmt P true ≤
      ENNReal.ofReal (friSmoothJohnsonCommitError params mJ) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q :=
  (friSmoothIOP_interactiveGame_le_of_weightedCurveGapPerRound params
    (weightedCurveGapPerRound_of_johnson params hmJ he) hfar P).trans
    (add_le_add (sum_friSmoothJohnsonRoundEscape_le params mJ) le_rfl)

/-- **Original explicit-constant Johnson round-by-round soundness of single-word `friSmoothIOP`**
(in the setting of [BenSassonBentovHoreshRiabzev2018] and
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5, 6.2, and 7.2]). -/
theorem friSmoothIOP_rbrSound_of_johnson [Fintype F] [DecidableEq F] (params : FRISmoothParams F)
    {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ))) :
    IOPRoundByRoundSoundness (friSmoothIOP params) (params.proximityLang e)
      (friSmoothDoomed params (2 ^ params.d - e - 1))
      (friSmoothGoodStep params (2 ^ params.d - e - 1)) ∧
    ∀ stmt ∉ params.proximityLang e, ∀ pref π,
      friSmoothDoomed params (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params (2 ^ params.d - e - 1) stmt pref π c} ≤
      friSmoothRBRError params e (friSmoothJohnsonCommitBound params mJ) :=
  ⟨friSmoothIOP_rbrSound params e,
    friSmoothRBREscape_of_weightedCurveGap params (weightedCurveGapBound_of_johnson params hmJ he)⟩

/-- **Original explicit-constant Johnson adaptive two-channel smooth BCS-FRI ROM soundness**
([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]), composing `weightedCurveGapBound_of_johnson`
with `friSmoothBCS_romSoundness_bound_of_weightedCurveGap`. -/
theorem friSmoothBCS_romSoundness_bound_of_johnson [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friSmoothIOP params) encSym (params.proximityLang e) P) Q_MT) :
    bcsSoundnessGame (friSmoothIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSmoothRBRError params e (friSmoothJohnsonCommitBound params mJ) +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friSmoothBCS_romSoundness_bound_of_weightedCurveGap params
    (weightedCurveGapBound_of_johnson params hmJ he) hdec σ hFS hMT

/-- **Original explicit-constant Johnson adaptive two-channel smooth BCS-FRI ROM soundness with
separate prover/verifier Merkle budgets** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]). -/
theorem friSmoothBCS_romSoundness_bound_of_prover_verifier_of_johnson [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friSmoothIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSmoothRBRError params e (friSmoothJohnsonCommitBound params mJ) +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friSmoothBCS_romSoundness_bound_of_prover_verifier_of_weightedCurveGap params
    (weightedCurveGapBound_of_johnson params hmJ he) hdec σ hMT hFS hops

end SmoothJohnsonBound

/-! ### Binary 2-to-1 Unique-Decoding FRI, Summed IOP, & BCS-FRI Corollaries -/

section UniqueDecoding

variable {F : Type} [Field F]

/-- **Unconditional shrinking per-round unique-decoding `WeightedLineGapPerRound`** across all `m`
single-word binary FRI folding rounds (corollary of `weightedCurveGapPerRound_of_unique`). -/
theorem weightedLineGapPerRound_of_unique [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) :
    WeightedLineGapPerRound params (2 ^ params.d - e - 1)
      (fun i => 2 ^ (params.d - (i.val + 1))) := by
  rw [weightedLineGapPerRound_iff_weightedCurveGapPerRound]
  have huniq' : 2 * e + params.toSmooth.dim 0 ≤ 2 ^ params.toSmooth.d := by
    simpa only [params.toSmooth_dim (Nat.zero_le _)] using huniq
  refine (weightedCurveGapPerRound_of_unique params.toSmooth huniq').mono fun i => ?_
  simp only [params.toSmooth_arity i, Nat.reduceSub, one_mul, params.toSmooth_domainSize i.isLt,
    FRIParams.domainSize, le_rfl]

/-- **Unconditional uniform unique-decoding `WeightedLineGapBound`** for all `m` single-word FRI
folding rounds (`B_commit = 2 ^ (d - 1)`), obtained as a monotonicity corollary of
`weightedLineGapPerRound_of_unique`. -/
theorem weightedLineGapBound_of_unique [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) :
    WeightedLineGapBound params (2 ^ params.d - e - 1) (2 ^ (params.d - 1)) :=
  (weightedLineGapPerRound_of_unique params huniq).mono fun _ =>
    Nat.pow_le_pow_right (by omega)
      (Nat.sub_le_sub_left (Nat.succ_le_succ (Nat.zero_le _)) _)

/-- Closed-form geometric commit-phase error `(1 - 1 / 2 ^ m) * (2 ^ d / |F|)` across all `m`
single-word 2-to-1 FRI folding rounds in the unique-decoding regime (`< 2 ^ d / |F|`
independently of `m`). -/
@[expose] noncomputable def friUniqueCommitError [Fintype F] (params : FRIParams F) : ℝ :=
  (1 - (1 : ℝ) / (2 : ℝ) ^ params.m) * ((2 ^ params.d : ℝ) / (Fintype.card F : ℝ))

/-- Exact geometric sum of per-round unique-decoding folding escape budgets in `ℝ≥0∞` (corollary of
`sum_friSmoothUniqueRoundEscape_eq`). -/
theorem sum_friUniqueRoundEscape_eq [Fintype F] (params : FRIParams F) :
    (∑ i : Fin params.m,
      ((2 ^ (params.d - (i.val + 1)) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) =
    ENNReal.ofReal (friUniqueCommitError params) := by
  have h := sum_friSmoothUniqueRoundEscape_eq params.toSmooth
  simp only [params.toSmooth_arity, Nat.reduceSub, one_mul, friSmoothUniqueCommitError,
    params.toSmooth_totalLog] at h
  refine (Finset.sum_congr rfl fun i _ => ?_).trans h
  rw [params.toSmooth_domainSize i.isLt, FRIParams.domainSize]

/-- **Unconditional summed commit-phase soundness of single-word `friIOP` in the unique-decoding
regime** (corollary of `friSmoothCommitGame_le_of_unique`). -/
theorem friCommitGame_le_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    friCommitGame params (2 ^ params.d - e - 1) stmt P true ≤
      ((2 ^ params.d - 2 ^ (params.d - params.m) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [friCommitGame_eq_friSmoothCommitGame]
  have huniq' : 2 * e + params.toSmooth.dim 0 ≤ 2 ^ params.toSmooth.d := by
    simpa only [params.toSmooth_dim (Nat.zero_le _)] using huniq
  have hfar' : stmt ∉ params.toSmooth.proximityLang e := by
    rwa [params.toSmooth_proximityLang]
  simpa only [params.toSmooth_totalLog] using
    friSmoothCommitGame_le_of_unique params.toSmooth huniq' hfar' P

/-- **Unconditional summed interactive soundness of single-word `friIOP` in the unique-decoding
regime** (corollary of `friSmoothIOP_interactiveGame_le_of_unique`). -/
theorem friIOP_interactiveGame_le_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    iopInteractiveGame (friIOP params) stmt P true ≤
      ((2 ^ params.d - 2 ^ (params.d - params.m) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  rw [friIOP_eq_friSmoothIOP]
  have huniq' : 2 * e + params.toSmooth.dim 0 ≤ 2 ^ params.toSmooth.d := by
    simpa only [params.toSmooth_dim (Nat.zero_le _)] using huniq
  have hfar' : stmt ∉ params.toSmooth.proximityLang e := by
    rwa [params.toSmooth_proximityLang]
  simpa only [params.toSmooth_totalLog] using
    friSmoothIOP_interactiveGame_le_of_unique params.toSmooth huniq' hfar' P

/-- **Unconditional round-by-round soundness of single-word `friIOP` in the unique-decoding regime**
([BenSassonBentovHoreshRiabzev2018]; [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 4.1]). -/
theorem friIOP_rbrSound_of_unique [Fintype F] [DecidableEq F] (params : FRIParams F)
    {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) :
    IOPRoundByRoundSoundness (friIOP params) (params.proximityLang e)
      (friDoomed params (2 ^ params.d - e - 1))
      (friGoodStep params (2 ^ params.d - e - 1)) ∧
    ∀ stmt ∉ params.proximityLang e, ∀ pref π,
      friDoomed params (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params (2 ^ params.d - e - 1) stmt pref π c} ≤
      friRBRError params e (2 ^ (params.d - 1)) :=
  ⟨friIOP_rbrSound params e,
    friRBREscape_of_weightedLineGap params (weightedLineGapBound_of_unique params huniq)⟩

/-- **Unconditional adaptive BCS-FRI ROM soundness in the unique-decoding regime**
([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]), composing `weightedLineGapBound_of_unique`
(`B_commit = 2 ^ (d - 1)`) with `friBCS_romSoundness_bound_of_weightedLineGap`. -/
theorem friBCS_romSoundness_bound_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friIOP params) encSym (params.proximityLang e) P) Q_MT) :
    bcsSoundnessGame (friIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friRBRError params e (2 ^ (params.d - 1)) +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBCS_romSoundness_bound_of_weightedLineGap params
    (weightedLineGapBound_of_unique params huniq) hdec σ hFS hMT

/-- **Unconditional adaptive BCS-FRI ROM soundness with separate prover/verifier Merkle budgets in
the unique-decoding regime** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]). -/
theorem friBCS_romSoundness_bound_of_prover_verifier_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friRBRError params e (2 ^ (params.d - 1)) +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBCS_romSoundness_bound_of_prover_verifier_of_weightedLineGap params
    (weightedLineGapBound_of_unique params huniq) hdec σ hMT hFS hops

end UniqueDecoding

/-! ### Binary 2-to-1 Johnson-Bound FRI, Summed IOP, & BCS-FRI Corollaries -/

section JohnsonBound

variable {F : Type} [Field F]

/-- Per-round geometric Siegel-interpolation bad-scalar bound for single-word 2-to-1 FRI in the
Johnson regime with multiplicity slack `mJ` at folding round `i : Fin params.m`:
`(1800 * (mJ + 1) ^ 6 * 2 ^ (params.d - (i.val + 1)) * (2 ^ params.d) ^ 2) / params.dim 0`. -/
abbrev friJohnsonRoundBound (params : FRIParams F) (mJ : ℕ) (i : Fin params.m) : ℕ :=
  (1800 * (mJ + 1) ^ 6 * 2 ^ (params.d - (i.val + 1)) * (2 ^ params.d) ^ 2) / params.dim 0

/-- Conservative uniform per-round commit-phase exceptional-scalar bound for single-word FRI in the
Johnson regime with multiplicity slack `mJ`:
`(900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3) / params.dim 0`. -/
abbrev friJohnsonCommitBound (params : FRIParams F) (mJ : ℕ) : ℕ :=
  (900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3) / params.dim 0

private theorem friJohnsonRoundBound_eq_smooth (params : FRIParams F) (mJ : ℕ) (i : Fin params.m) :
    friJohnsonRoundBound params mJ i = friSmoothJohnsonRoundBound params.toSmooth mJ i := by
  simp only [friJohnsonRoundBound, friSmoothJohnsonRoundBound, params.toSmooth_arity i,
    Nat.reduceSub, one_mul, params.toSmooth_domainSize i.isLt, FRIParams.domainSize,
    params.toSmooth_dim (Nat.zero_le _)]

/-- At `params.toSmooth`, the smooth uniform Johnson commit budget is bounded above by the binary
`friJohnsonCommitBound`. -/
theorem friSmoothJohnsonCommitBound_toSmooth_le (params : FRIParams F) (mJ : ℕ) :
    friSmoothJohnsonCommitBound params.toSmooth mJ ≤ friJohnsonCommitBound params mJ := by
  rw [friSmoothJohnsonCommitBound, friJohnsonCommitBound, params.toSmooth_dim (Nat.zero_le _)]
  refine Nat.div_le_div_right ?_
  have h1 := two_mul_toSmooth_first_sub_le params
  calc 1800 * (mJ + 1) ^ 6 * (2 ^ params.d - 2 ^ (params.d - params.toSmooth.firstStepLog)) *
        (2 ^ params.d) ^ 2
      = 900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 2 *
          (2 * (2 ^ params.d - 2 ^ (params.d - params.toSmooth.firstStepLog))) := by ring
    _ ≤ 900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 2 * 2 ^ params.d := Nat.mul_le_mul_left _ h1
    _ = 900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3 := by ring

/-- At round `0`, `friJohnsonRoundBound` coincides exactly with `friJohnsonCommitBound`. -/
theorem friJohnsonRoundBound_zero (params : FRIParams F) (mJ : ℕ) (hm : 0 < params.m) :
    friJohnsonRoundBound params mJ ⟨0, hm⟩ = friJohnsonCommitBound params mJ := by
  rw [friJohnsonRoundBound_eq_smooth, friSmoothJohnsonRoundBound_zero params.toSmooth mJ hm]
  have hd : 0 < params.d := lt_of_lt_of_le hm params.hm
  have hsub := toSmooth_first_sub_eq_of_pos params hd
  have h0 : 2 * 2 ^ (params.d - 1) = 2 ^ params.d := by
    have : params.d = (params.d - 1) + 1 := by omega
    conv_rhs => rw [this, pow_succ']
  rw [friSmoothJohnsonCommitBound, friJohnsonCommitBound, params.toSmooth_dim (Nat.zero_le _), hsub]
  congr 1
  calc 1800 * (mJ + 1) ^ 6 * 2 ^ (params.d - 1) * (2 ^ params.d) ^ 2
      = 900 * (mJ + 1) ^ 6 * (2 * 2 ^ (params.d - 1)) * (2 ^ params.d) ^ 2 := by ring
    _ = 900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3 := by rw [h0]; ring

/-- Every folding round's geometric budget `friJohnsonRoundBound params mJ i` is bounded by the
round-0 uniform budget `friJohnsonCommitBound params mJ`. -/
theorem friJohnsonRoundBound_le_commitBound (params : FRIParams F) (mJ : ℕ) (i : Fin params.m) :
    friJohnsonRoundBound params mJ i ≤ friJohnsonCommitBound params mJ := by
  rw [friJohnsonRoundBound_eq_smooth]
  exact (friSmoothJohnsonRoundBound_le_commitBound params.toSmooth mJ i).trans
    (friSmoothJohnsonCommitBound_toSmooth_le params mJ)

/-- Geometric telescoping upper bound on the integer sum of `friJohnsonRoundBound` across all `m`
folding rounds (corollary of `sum_friSmoothJohnsonRoundBound_le`). -/
theorem sum_friJohnsonRoundBound_le (params : FRIParams F) (mJ : ℕ) :
    (∑ i : Fin params.m, friJohnsonRoundBound params mJ i) ≤
      (1800 * (mJ + 1) ^ 6 * (2 ^ params.d - 2 ^ (params.d - params.m)) * (2 ^ params.d) ^ 2) /
        params.dim 0 := by
  have h := sum_friSmoothJohnsonRoundBound_le params.toSmooth mJ
  simp only [params.toSmooth_totalLog, params.toSmooth_dim (Nat.zero_le _)] at h
  refine (Finset.sum_congr rfl fun i _ => friJohnsonRoundBound_eq_smooth params mJ i).trans_le h

/-- Closed-form geometric Siegel commit-phase error across all `m` single-word 2-to-1 FRI folding
rounds in the Johnson regime (`(1 - 1 / 2 ^ m) * 1800 * (mJ + 1) ^ 6 * (2 ^ d) ^ 2 / (ρ * |F|)`).
-/
@[expose] noncomputable def friJohnsonCommitError [Fintype F]
    (params : FRIParams F) (mJ : ℕ) : ℝ :=
  (1 - (1 : ℝ) / (2 : ℝ) ^ params.m) *
    (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
      (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ)))

/-- Geometric sum of per-round Johnson escape probabilities bounded by `friJohnsonCommitError`
(corollary of `sum_friSmoothJohnsonRoundEscape_le`). -/
theorem sum_friJohnsonRoundEscape_le [Fintype F] (params : FRIParams F) (mJ : ℕ) :
    (∑ i : Fin params.m,
      (friJohnsonRoundBound params mJ i : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ≤
    ENNReal.ofReal (friJohnsonCommitError params mJ) := by
  have h := sum_friSmoothJohnsonRoundEscape_le params.toSmooth mJ
  simp only [friSmoothJohnsonCommitError, params.toSmooth_totalLog,
    params.toSmooth_dim (Nat.zero_le _)] at h
  refine (Finset.sum_congr rfl fun i _ => ?_).trans_le h
  rw [friJohnsonRoundBound_eq_smooth]

/-- **Explicit-parameter Guruswami–Sudan per-round `WeightedLineGapPerRound`** across all `m`
single-word binary FRI folding rounds (corollary of `weightedCurveGapPerRound_of_johnson_discrete`).
-/
theorem weightedLineGapPerRound_of_johnson_discrete [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (he : e < 2 ^ params.d)
    (mRound DRound : Fin params.m → ℕ)
    (hm : ∀ i : Fin params.m, 1 ≤ mRound i)
    (hk_le : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤ 2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1))
    (hinterp : ∀ i : Fin params.m,
      2 ^ (params.d - (i.val + 1)) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)))
    (hroot : ∀ i : Fin params.m,
      DRound i < mRound i * (2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1))) :
    WeightedLineGapPerRound params (2 ^ params.d - e - 1)
      (fun i => ProximityGap.johnsonCurveBound (2 ^ (params.d - (i.val + 1))) (mRound i)
        (params.dim (i.val + 1) - 1) (DRound i) 1 (2 ^ params.d)) := by
  rw [weightedLineGapPerRound_iff_weightedCurveGapPerRound]
  have h := weightedCurveGapPerRound_of_johnson_discrete params.toSmooth he mRound DRound hm
    (fun i => by
      simpa only [params.toSmooth_dim i.isLt, params.toSmooth_domainSize i.isLt,
        FRIParams.domainSize, params.toSmooth_cumLog i.isLt] using hk_le i)
    (fun i => by
      simpa only [params.toSmooth_domainSize i.isLt, FRIParams.domainSize,
        params.toSmooth_dim i.isLt] using hinterp i)
    (fun i => by
      simpa only [params.toSmooth_domainSize i.isLt, FRIParams.domainSize,
        params.toSmooth_cumLog i.isLt] using hroot i)
  refine h.mono fun i => ?_
  simp only [params.toSmooth_domainSize i.isLt, FRIParams.domainSize, params.toSmooth_dim i.isLt,
    params.toSmooth_arity i, Nat.reduceSub, le_rfl]

/-- **Explicit-parameter Guruswami–Sudan uniform `WeightedLineGapBound`** for all `m` single-word
FRI folding rounds, derived as a monotonicity corollary of
`weightedLineGapPerRound_of_johnson_discrete`. -/
theorem weightedLineGapBound_of_johnson_discrete [DecidableEq F]
    (params : FRIParams F) {e B_commit : ℕ} (he : e < 2 ^ params.d)
    (mRound DRound : Fin params.m → ℕ)
    (hm : ∀ i : Fin params.m, 1 ≤ mRound i)
    (hk_le : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤ 2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1))
    (hinterp : ∀ i : Fin params.m,
      2 ^ (params.d - (i.val + 1)) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)))
    (hroot : ∀ i : Fin params.m,
      DRound i < mRound i * (2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1)))
    (hbound : ∀ i : Fin params.m,
      ProximityGap.johnsonCurveBound (2 ^ (params.d - (i.val + 1))) (mRound i)
        (params.dim (i.val + 1) - 1) (DRound i) 1 (2 ^ params.d) ≤ B_commit) :
    WeightedLineGapBound params (2 ^ params.d - e - 1) B_commit :=
  (weightedLineGapPerRound_of_johnson_discrete params he mRound DRound hm hk_le hinterp hroot).mono
    hbound

/-- **Explicit-parameter Guruswami–Sudan step toward summed commit-phase soundness of single-word
`friIOP`**. -/
theorem friCommitGame_le_of_johnson_discrete [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (he : e < 2 ^ params.d)
    (mRound DRound : Fin params.m → ℕ)
    (hm : ∀ i : Fin params.m, 1 ≤ mRound i)
    (hk_le : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤ 2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1))
    (hinterp : ∀ i : Fin params.m,
      2 ^ (params.d - (i.val + 1)) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)))
    (hroot : ∀ i : Fin params.m,
      DRound i < mRound i * (2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1)))
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    friCommitGame params (2 ^ params.d - e - 1) stmt P true ≤
      ((∑ i : Fin params.m,
        ProximityGap.johnsonCurveBound (2 ^ (params.d - (i.val + 1))) (mRound i)
          (params.dim (i.val + 1) - 1) (DRound i) 1 (2 ^ params.d) : ℕ) : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) := by
  refine (friCommitGame_le_of_weightedLineGapPerRound params
    (weightedLineGapPerRound_of_johnson_discrete params he mRound DRound hm hk_le hinterp hroot)
    hfar P).trans_eq ?_
  exact sum_natCast_div_ennreal Finset.univ _ _

/-- **Explicit-parameter Guruswami–Sudan step toward summed interactive soundness of single-word
`friIOP`**. -/
theorem friIOP_interactiveGame_le_of_johnson_discrete [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (he : e < 2 ^ params.d)
    (mRound DRound : Fin params.m → ℕ)
    (hm : ∀ i : Fin params.m, 1 ≤ mRound i)
    (hk_le : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤ 2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1))
    (hinterp : ∀ i : Fin params.m,
      2 ^ (params.d - (i.val + 1)) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)))
    (hroot : ∀ i : Fin params.m,
      DRound i < mRound i * (2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1)))
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    iopInteractiveGame (friIOP params) stmt P true ≤
      ((∑ i : Fin params.m,
          ProximityGap.johnsonCurveBound (2 ^ (params.d - (i.val + 1))) (mRound i)
            (params.dim (i.val + 1) - 1) (DRound i) 1 (2 ^ params.d) : ℕ) : ℝ≥0∞) /
          (Fintype.card F : ℝ≥0∞) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  refine (friIOP_interactiveGame_le_of_weightedLineGapPerRound params
    (weightedLineGapPerRound_of_johnson_discrete params he mRound DRound hm hk_le hinterp hroot)
    hfar P).trans_eq ?_
  rw [friSumError, friSmoothSumError, sum_natCast_div_ennreal]

/-- **Original explicit-constant per-round Johnson-bound `WeightedLineGapPerRound`** across all `m`
single-word binary FRI folding rounds up to `δ ≤ 1 - √ρ - √ρ / (2 * mJ)` (corollary of
`weightedCurveGapPerRound_of_johnson`). -/
theorem weightedLineGapPerRound_of_johnson [DecidableEq F]
    (params : FRIParams F) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ))) :
    WeightedLineGapPerRound params (2 ^ params.d - e - 1) (friJohnsonRoundBound params mJ) := by
  rw [weightedLineGapPerRound_iff_weightedCurveGapPerRound]
  have he' : (e : ℝ) / (2 ^ params.toSmooth.d : ℝ) ≤
      1 - Real.sqrt ((params.toSmooth.dim 0 : ℝ) / (2 ^ params.toSmooth.d : ℝ)) -
        Real.sqrt ((params.toSmooth.dim 0 : ℝ) / (2 ^ params.toSmooth.d : ℝ)) / (2 * (mJ : ℝ)) := by
    simpa only [params.toSmooth_dim (Nat.zero_le _)] using he
  refine (weightedCurveGapPerRound_of_johnson params.toSmooth hmJ he').mono fun i => ?_
  rw [friJohnsonRoundBound_eq_smooth]

/-- **Original explicit-constant uniform Johnson-bound `WeightedLineGapBound`** for all `m`
single-word FRI folding rounds up to `δ ≤ 1 - √ρ - √ρ / (2 * mJ)` (`friJohnsonCommitBound params
mJ`), obtained as a monotonicity corollary of `weightedLineGapPerRound_of_johnson` and
`friJohnsonRoundBound_le_commitBound`. -/
theorem weightedLineGapBound_of_johnson [DecidableEq F]
    (params : FRIParams F) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ))) :
    WeightedLineGapBound params (2 ^ params.d - e - 1) (friJohnsonCommitBound params mJ) :=
  (weightedLineGapPerRound_of_johnson params hmJ he).mono (friJohnsonRoundBound_le_commitBound _ _)

/-- Conservative uniform per-round commit-phase exceptional-scalar budget for 2-to-1 FRI in the
`η`-gap Johnson regime (`(e : ℝ) / 2 ^ d ≤ 1 - √ρ - η`, `0 < η`):
`⌊57600 * (2 ^ d) ^ 3 / (dim 0 * η ^ 6)⌋₊` (using this library's original explicit Siegel constant
`900 * 64 = 57600` and `η` directly rather than `min(η, √ρ / 20)` in Eq. (1.3)). -/
@[expose] noncomputable def friJohnsonEtaCommitBound (params : FRIParams F) (η : ℝ) : ℕ :=
  ⌊57600 * ((2 ^ params.d : ℝ) ^ 3) / ((params.dim 0 : ℝ) * (η ^ 6))⌋₊

/-- **Original explicit-constant `η`-gap uniform `WeightedLineGapBound`** across all `m` binary FRI
folding rounds up to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - η` (`0 < η`), corollary of
`weightedCurveGapBound_of_johnson_eta`. -/
theorem weightedLineGapBound_of_johnson_eta [DecidableEq F]
    (params : FRIParams F) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η) :
    WeightedLineGapBound params (2 ^ params.d - e - 1)
      (friJohnsonEtaCommitBound params η) := by
  rw [WeightedLineGapBound, weightedLineGapPerRound_iff_weightedCurveGapPerRound]
  have he' : (e : ℝ) / (2 ^ params.toSmooth.d : ℝ) ≤
      1 - Real.sqrt ((params.toSmooth.dim 0 : ℝ) / (2 ^ params.toSmooth.d : ℝ)) - η := by
    simpa only [params.toSmooth_dim (Nat.zero_le _)] using he
  refine (weightedCurveGapBound_of_johnson_eta params.toSmooth hη he').mono fun _ => ?_
  refine Nat.floor_mono ?_
  rw [params.toSmooth_dim (Nat.zero_le _)]
  have h1R : 2 * ((2 ^ params.d - 2 ^ (params.d - params.toSmooth.firstStepLog) : ℕ) : ℝ) ≤
      (2 ^ params.d : ℝ) := by exact_mod_cast two_mul_toSmooth_first_sub_le params
  have hk₀R : (0 : ℝ) < (params.dim 0 : ℝ) := by exact_mod_cast params.one_le_dim 0
  have hden : (0 : ℝ) ≤ (params.dim 0 : ℝ) * (η ^ 6) := by positivity
  refine div_le_div_of_nonneg_right ?_ hden
  calc 115200 * ((2 ^ params.d - 2 ^ (params.d - params.toSmooth.firstStepLog) : ℕ) : ℝ) *
        ((2 ^ params.d : ℝ) ^ 2)
      = 57600 * (2 * ((2 ^ params.d - 2 ^ (params.d - params.toSmooth.firstStepLog) : ℕ) : ℝ)) *
          ((2 ^ params.d : ℝ) ^ 2) := by ring
    _ ≤ 57600 * (2 ^ params.d : ℝ) * ((2 ^ params.d : ℝ) ^ 2) := by gcongr
    _ = 57600 * ((2 ^ params.d : ℝ) ^ 3) := by ring

/-- **Original explicit-constant Johnson summed commit-phase soundness of single-word `friIOP`**
(using `friJohnsonCommitError params mJ`, bounded independently of `m`). -/
theorem friCommitGame_le_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    friCommitGame params (2 ^ params.d - e - 1) stmt P true ≤
      ENNReal.ofReal (friJohnsonCommitError params mJ) :=
  (friCommitGame_le_of_weightedLineGapPerRound params
    (weightedLineGapPerRound_of_johnson params hmJ he) hfar P).trans
    (sum_friJohnsonRoundEscape_le params mJ)

/-- **Original explicit-constant Johnson summed interactive soundness of single-word `friIOP`**
(using `friJohnsonCommitError params mJ` plus query error `((2 ^ d - e - 1) / 2 ^ d) ^ q`). -/
theorem friIOP_interactiveGame_le_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    iopInteractiveGame (friIOP params) stmt P true ≤
      ENNReal.ofReal (friJohnsonCommitError params mJ) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q :=
  (friIOP_interactiveGame_le_of_weightedLineGapPerRound params
    (weightedLineGapPerRound_of_johnson params hmJ he) hfar P).trans
    (add_le_add (sum_friJohnsonRoundEscape_le params mJ) le_rfl)

/-- **Original explicit-constant Johnson round-by-round soundness of single-word `friIOP`**
(in the setting of [BenSassonBentovHoreshRiabzev2018] and
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.4, 5.1, and 7.2]). -/
theorem friIOP_rbrSound_of_johnson [Fintype F] [DecidableEq F] (params : FRIParams F)
    {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ))) :
    IOPRoundByRoundSoundness (friIOP params) (params.proximityLang e)
      (friDoomed params (2 ^ params.d - e - 1))
      (friGoodStep params (2 ^ params.d - e - 1)) ∧
    ∀ stmt ∉ params.proximityLang e, ∀ pref π,
      friDoomed params (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params (2 ^ params.d - e - 1) stmt pref π c} ≤
      friRBRError params e (friJohnsonCommitBound params mJ) :=
  ⟨friIOP_rbrSound params e,
    friRBREscape_of_weightedLineGap params (weightedLineGapBound_of_johnson params hmJ he)⟩

/-- **Original explicit-constant Johnson adaptive two-channel BCS-FRI ROM soundness**
([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]), composing `weightedLineGapBound_of_johnson`
with `friBCS_romSoundness_bound_of_weightedLineGap`. -/
theorem friBCS_romSoundness_bound_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friIOP params) encSym (params.proximityLang e) P) Q_MT) :
    bcsSoundnessGame (friIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friRBRError params e (friJohnsonCommitBound params mJ) +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBCS_romSoundness_bound_of_weightedLineGap params
    (weightedLineGapBound_of_johnson params hmJ he) hdec σ hFS hMT

/-- **Original explicit-constant Johnson adaptive two-channel BCS-FRI ROM soundness with separate
prover/verifier Merkle budgets** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]). -/
theorem friBCS_romSoundness_bound_of_prover_verifier_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friRBRError params e (friJohnsonCommitBound params mJ) +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBCS_romSoundness_bound_of_prover_verifier_of_weightedLineGap params
    (weightedLineGapBound_of_johnson params hmJ he) hdec σ hMT hFS hops

end JohnsonBound

end Cslib.Crypto.Protocols.FRI
