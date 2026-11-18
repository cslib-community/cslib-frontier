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
# Unconditional Unique-Decoding and Johnson-Bound FRI, Summed IOP, and BCS-FRI ROM Soundness

This module discharges the per-round and uniform line proximity-gap hypotheses of
`CslibFrontier.Crypto.Protocols.FRI.Soundness` unconditionally for the single-word
(`OracleTable d F`) 2-to-1 FRI IOP in both the unique-decoding regime and the Johnson-bound regime,
combining `Cslib.Code.exists_correlatedAgreement_unique`
([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 4.1]) and
`Cslib.Code.exists_weighted_correlatedAgreement_line_johnson`
([BenSassonCarmonIshaiKoppartySaraf2020, Theorems 5.1 and 7.2]) with
`Cslib.Crypto.Protocols.FRI.friIOP_rbrSound`, the per-round commit and summed interactive IOP
soundness providers (`friCommitGame_le_of_weightedLineGapPerRound`,
`friIOP_interactiveGame_le_of_weightedLineGapPerRound`), and the two-channel BCS random-oracle
soundness provider `Cslib.Crypto.Protocols.FRI.friBCS_romSoundness_bound_of_weightedLineGap` /
`Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound` ([BenSassonBentovHoreshRiabzev2018];
[BenSassonChiesaSpooner2016]; [ChiesaYogev2024]).

## Scope and relationship to the source theorems

* Lemma 8.2 (printed pp. 38–39, proved via the commit-phase bad-event sum in Section 8.2.1,
  printed pp. 41–43, p. 42) and Theorem 8.3 (printed p. 39, proved on printed p. 40 by applying
  Lemma 8.2) of the accepted *Journal of the ACM* (2023) manuscript
  ([BenSassonCarmonIshaiKoppartySaraf2020]) are interactive IOP soundness theorems for *batched*
  FRI establishing correlated agreement of the initial functions; BCS random-oracle soundness bounds
  are separate compositions.
* Folding in `friIOP` is binary (`l⁽ⁱ⁾ = 2`). Across the `m` folding rounds, the active coset size
  halves each round (`2 ^ (d - (i + 1))`), so both the shrinking unique-decoding budgets
  `2 ^ (d - (i + 1))` and the geometric Siegel-interpolation Johnson budgets
  `friJohnsonRoundBound params mJ i` sum over all `m` rounds without an `O(m)` union-bound factor
  (mirroring the geometric telescoping on printed p. 43 of [BenSassonCarmonIshaiKoppartySaraf2020]).
* In the Johnson regime, `friJohnsonRoundBound`, `friJohnsonCommitBound`,
  `friJohnsonEtaCommitBound`, and `friJohnsonCommitError` use this library's original explicit
  Siegel-interpolation constants for all `mJ ≥ 1` (`1800 * (mJ + 1) ^ 6 * …` and `57600 * … / η ^ 6`
  using `η` directly rather than `min(η, √ρ / 20)` in eq. 1.3), which are not uniformly smaller at
  small `mJ` than the constants displayed in JACM Lemma 8.2 / Theorem 8.3. Batched initial-function
  correlated agreement and exact correspondence with JACM Theorem 8.3's displayed error expression
  remain open on `#5968`.
* All uniform `WeightedLineGapBound` theorems (`weightedLineGapBound_of_unique`,
  `weightedLineGapBound_of_johnson_discrete`, `weightedLineGapBound_of_johnson`,
  `weightedLineGapBound_of_johnson_eta`) are derived as thin monotonicity corollaries of the
  per-round `WeightedLineGapPerRound` / `weightedLineGapBound_of_johnson` theorems.

## Main definitions

* `Cslib.Crypto.Protocols.FRI.friUniqueCommitError`: closed-form geometric unique-decoding
  commit-phase error `(1 - 1 / 2 ^ m) * (2 ^ d / |F|)` (`< 2 ^ d / |F|` independently of `m`).
* `Cslib.Crypto.Protocols.FRI.friJohnsonRoundBound`: per-round geometric Johnson bad-scalar budget
  `(1800 * (mJ + 1) ^ 6 * 2 ^ (params.d - (i.val + 1)) * (2 ^ params.d) ^ 2) / params.dim 0`
  (equal to `friJohnsonCommitBound params mJ` at `i = 0`, halving each round).
* `Cslib.Crypto.Protocols.FRI.friJohnsonCommitBound`: uniform commit-round bad-scalar budget
  `(900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3) / params.dim 0`.
* `Cslib.Crypto.Protocols.FRI.friJohnsonEtaCommitBound`: uniform `η`-gap commit-round bad-scalar
  budget `⌊57600 * (2 ^ params.d) ^ 3 / (params.dim 0 * η ^ 6)⌋₊`.
* `Cslib.Crypto.Protocols.FRI.friJohnsonCommitError`: closed-form geometric Siegel commit-phase
  error `(1 - 1 / 2 ^ m) * (1800 * (mJ + 1) ^ 6 * (2 ^ d) ^ 2 / ((dim 0 / 2 ^ d) * |F|))`
  (`< 1800 * (mJ + 1) ^ 6 * (2 ^ d) ^ 2 / (ρ * |F|)` independently of `m`).

## Main results

### Unique-decoding regime (`2 * e + params.dim 0 ≤ 2 ^ params.d`)
* `Cslib.Crypto.Protocols.FRI.weightedLineGapPerRound_of_unique` &
  `Cslib.Crypto.Protocols.FRI.weightedLineGapBound_of_unique`: unconditional per-round
  (`2 ^ (d - (i + 1))`) and uniform (`2 ^ (d - 1)`) weighted line proximity-gap bounds.
* `Cslib.Crypto.Protocols.FRI.friCommitGame_le_of_unique` &
  `Cslib.Crypto.Protocols.FRI.friIOP_interactiveGame_le_of_unique`: unconditional summed
  commit-phase and full interactive soundness bounds for single-word `friIOP`.
* `Cslib.Crypto.Protocols.FRI.friIOP_rbrSound_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friBCS_romSoundness_bound_of_unique`, &
  `Cslib.Crypto.Protocols.FRI.friBCS_romSoundness_bound_of_prover_verifier_of_unique`.

### Johnson-bound regime (`δ ≤ 1 - √ρ - √ρ / (2 * mJ)` and per-round discrete bounds)
* `Cslib.Crypto.Protocols.FRI.weightedLineGapPerRound_of_johnson_discrete` &
  `Cslib.Crypto.Protocols.FRI.weightedLineGapBound_of_johnson_discrete`: unconditional per-round
  and uniform discrete `johnsonCurveBound` discharges, plus
  `friCommitGame_le_of_johnson_discrete` and `friIOP_interactiveGame_le_of_johnson_discrete`.
* `Cslib.Crypto.Protocols.FRI.weightedLineGapPerRound_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.weightedLineGapBound_of_johnson`, &
  `Cslib.Crypto.Protocols.FRI.weightedLineGapBound_of_johnson_eta`: unconditional geometric
  per-round (`friJohnsonRoundBound`) and uniform (`friJohnsonCommitBound`,
  `friJohnsonEtaCommitBound`) Johnson and `η`-gap discharges.
* `Cslib.Crypto.Protocols.FRI.friCommitGame_le_of_johnson` &
  `Cslib.Crypto.Protocols.FRI.friIOP_interactiveGame_le_of_johnson`: unconditional summed
  commit-phase and full interactive soundness bounds for single-word `friIOP` up to the Johnson
  bound (eliminating any `O(m)` factor via `sum_friJohnsonRoundBound_le` /
  `sum_friJohnsonRoundEscape_le`).
* `Cslib.Crypto.Protocols.FRI.friIOP_rbrSound_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friBCS_romSoundness_bound_of_johnson`, &
  `Cslib.Crypto.Protocols.FRI.friBCS_romSoundness_bound_of_prover_verifier_of_johnson`.

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

private theorem cast_two_pow_sub_eq (params : FRIParams F) :
    (((2 ^ params.d - 2 ^ (params.d - params.m) : ℕ) : ℝ)) =
      (1 - (1 : ℝ) / (2 : ℝ) ^ params.m) * ((2 : ℝ) ^ params.d) := by
  have hle : 2 ^ (params.d - params.m) ≤ 2 ^ params.d :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  have hsplit : (2 : ℝ) ^ params.d = (2 : ℝ) ^ (params.d - params.m) * (2 : ℝ) ^ params.m := by
    rw [← pow_add, Nat.sub_add_cancel params.hm]
  have h2m_ne : ((2 : ℝ) ^ params.m) ≠ 0 := by positivity
  calc (((2 ^ params.d - 2 ^ (params.d - params.m) : ℕ) : ℝ))
      = (2 : ℝ) ^ params.d - (2 : ℝ) ^ (params.d - params.m) := by
          rw [Nat.cast_sub hle]
          push_cast
          rfl
    _ = (2 : ℝ) ^ (params.d - params.m) * (2 : ℝ) ^ params.m -
          (2 : ℝ) ^ (params.d - params.m) * (((2 : ℝ) ^ params.m) / ((2 : ℝ) ^ params.m)) := by
          rw [← hsplit, div_self h2m_ne, mul_one]
    _ = (1 - (1 : ℝ) / (2 : ℝ) ^ params.m) * ((2 : ℝ) ^ params.d) := by
          rw [hsplit]
          ring

end Helpers

/-! ### Unconditional Unique-Decoding FRI, Summed IOP, & BCS-FRI ROM Soundness -/

section UniqueDecoding

variable {F : Type} [Field F]

/-- **Unconditional shrinking per-round unique-decoding `WeightedLineGapPerRound`** across all `m`
single-word FRI folding rounds (instantiating [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 4.1]
at each round via `FRIParams.two_mul_div_add_dim_le`).

Discharges `UniqueLineGapHypothesis` directly from `Cslib.Code.exists_correlatedAgreement_unique`
over any field `F` of characteristic `≠ 2`, yielding per-round exceptional-scalar budget
`2 ^ (d - (i + 1))` (summing over all `m` rounds to `2 ^ d - 2 ^ (d - m) < 2 ^ d`) with zero
gap-assumption premise. -/
theorem weightedLineGapPerRound_of_unique [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) :
    WeightedLineGapPerRound params (2 ^ params.d - e - 1)
      (fun i => 2 ^ (params.d - (i.val + 1))) := by
  refine weightedLineGapPerRound_of_uniqueLineGap params huniq ?_
  intro i u₀ u₁ Z hZ_gt hZ_close
  have huniq_i :
      2 * (e / 2 ^ (i.val + 1)) + params.dim (i.val + 1) ≤
        Fintype.card (Fin (2 ^ (params.d - (i.val + 1)))) := by
    simpa only [Fintype.card_fin] using params.two_mul_div_add_dim_le huniq i
  have hα_inj : Function.Injective (params.eval (i.val + 1)) :=
    cosetEval_injective params.hg params.hω (Nat.le_trans i.isLt params.hm)
  obtain ⟨D', hD'_card, v₀, hv₀, v₁, hv₁, hD'_agree⟩ :=
    exists_correlatedAgreement_unique hα_inj huniq_i u₀ u₁ Z
      (by simpa only [Fintype.card_fin] using hZ_gt) hZ_close
  exact ⟨D', v₀, hv₀, v₁, hv₁, by simpa only [Fintype.card_fin] using hD'_card, hD'_agree⟩

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

/-- Exact geometric sum of per-round unique-decoding folding escape budgets in `ℝ≥0∞`. -/
theorem sum_friUniqueRoundEscape_eq [Fintype F] (params : FRIParams F) :
    (∑ i : Fin params.m,
      ((2 ^ (params.d - (i.val + 1)) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) =
    ENNReal.ofReal (friUniqueCommitError params) := by
  rw [sum_natCast_div_ennreal, params.sum_domainSize_succ,
    natCast_div_eq_ofReal Fintype.card_pos, cast_two_pow_sub_eq, mul_div_assoc,
    friUniqueCommitError]

/-- **Unconditional summed commit-phase soundness of single-word `friIOP` in the unique-decoding
regime**: for `stmt ∉ params.proximityLang e`, `friCommitGame` exceeds agreement `2 ^ d - e - 1`
with probability at most `(2 ^ d - 2 ^ (d - m)) / |F|` (`= ENNReal.ofReal (friUniqueCommitError
params)`). -/
theorem friCommitGame_le_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    friCommitGame params (2 ^ params.d - e - 1) stmt P true ≤
      ((2 ^ params.d - 2 ^ (params.d - params.m) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  refine (friCommitGame_le_of_weightedLineGapPerRound params
    (weightedLineGapPerRound_of_unique params huniq) hfar P).trans_eq ?_
  rw [sum_natCast_div_ennreal, params.sum_domainSize_succ]

/-- **Unconditional summed interactive soundness of single-word `friIOP` in the unique-decoding
regime**: for `stmt ∉ params.proximityLang e` and any adaptive prover `P`, the acceptance
probability is at most `(2 ^ d - 2 ^ (d - m)) / |F| + ((2 ^ d - e - 1) / 2 ^ d) ^ q`
(eliminating the `m * 2 ^ (d - 1)` union-bound blowup across folding rounds). -/
theorem friIOP_interactiveGame_le_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    iopInteractiveGame (friIOP params) stmt P true ≤
      ((2 ^ params.d - 2 ^ (params.d - params.m) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  refine (friIOP_interactiveGame_le_of_weightedLineGapPerRound params
    (weightedLineGapPerRound_of_unique params huniq) hfar P).trans_eq ?_
  rw [friSumError, sum_natCast_div_ennreal, params.sum_domainSize_succ]

/-- **Unconditional round-by-round soundness of single-word `friIOP` in the unique-decoding regime**
([BenSassonBentovHoreshRiabzev2018]; [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 4.1]).

Establishes both the `IOPRoundByRoundSoundness` invariant and the sharp per-round escape bound
`≤ friRBRError params e (2 ^ (params.d - 1))` for every unique-decoding radius
`2 * e + params.dim 0 ≤ 2 ^ params.d` over any finite field `F` of characteristic `≠ 2`, with zero
gap-assumption premise. -/
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
the unique-decoding regime** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]), composing
`weightedLineGapBound_of_unique` with
`friBCS_romSoundness_bound_of_prover_verifier_of_weightedLineGap`. -/
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

/-! ### Unconditional Johnson-Bound FRI, Summed IOP, & BCS-FRI ROM Soundness -/

section JohnsonBound

variable {F : Type} [Field F]

/-- Per-round geometric Siegel-interpolation bad-scalar bound for single-word 2-to-1 FRI in the
Johnson regime with multiplicity slack `mJ` at folding round `i : Fin params.m`:
`(1800 * (mJ + 1) ^ 6 * 2 ^ (params.d - (i.val + 1)) * (2 ^ params.d) ^ 2) / params.dim 0`
(using this library's original explicit Siegel constant `1800 * (mJ + 1) ^ 6`, halving each round,
and summing over all `m` rounds without an `O(m)` factor). -/
abbrev friJohnsonRoundBound (params : FRIParams F) (mJ : ℕ) (i : Fin params.m) : ℕ :=
  (1800 * (mJ + 1) ^ 6 * 2 ^ (params.d - (i.val + 1)) * (2 ^ params.d) ^ 2) / params.dim 0

/-- Conservative uniform per-round commit-phase exceptional-scalar bound for single-word FRI in the
Johnson regime with multiplicity slack `mJ`:
`(900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3) / params.dim 0`. -/
abbrev friJohnsonCommitBound (params : FRIParams F) (mJ : ℕ) : ℕ :=
  (900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3) / params.dim 0

/-- At round `0`, `friJohnsonRoundBound` coincides exactly with `friJohnsonCommitBound`. -/
theorem friJohnsonRoundBound_zero (params : FRIParams F) (mJ : ℕ) (hm : 0 < params.m) :
    friJohnsonRoundBound params mJ ⟨0, hm⟩ = friJohnsonCommitBound params mJ := by
  have h0 : 2 * 2 ^ (params.d - 1) = 2 ^ params.d := by
    simpa only [Nat.zero_add, pow_one] using params.fiber_mul_domainSize ⟨0, hm⟩
  have hnum :
      1800 * (mJ + 1) ^ 6 * 2 ^ (params.d - 1) * (2 ^ params.d) ^ 2 =
        900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3 := by
    calc 1800 * (mJ + 1) ^ 6 * 2 ^ (params.d - 1) * (2 ^ params.d) ^ 2
        = 900 * (mJ + 1) ^ 6 * (2 * 2 ^ (params.d - 1)) * (2 ^ params.d) ^ 2 := by ring
      _ = 900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3 := by rw [h0]; ring
  simp only [friJohnsonRoundBound, friJohnsonCommitBound, Nat.zero_add, hnum]

/-- Every folding round's geometric budget `friJohnsonRoundBound params mJ i` is bounded by the
round-0 uniform budget `friJohnsonCommitBound params mJ`. -/
theorem friJohnsonRoundBound_le_commitBound (params : FRIParams F) (mJ : ℕ) (i : Fin params.m) :
    friJohnsonRoundBound params mJ i ≤ friJohnsonCommitBound params mJ := by
  have h2ni_le : 2 * 2 ^ (params.d - (i.val + 1)) ≤ 2 ^ params.d := by
    have h2leM : 2 ≤ 2 ^ (i.val + 1) := by
      have : 2 ^ 1 ≤ 2 ^ (i.val + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      simpa only [pow_one] using this
    calc 2 * 2 ^ (params.d - (i.val + 1))
        ≤ 2 ^ (i.val + 1) * 2 ^ (params.d - (i.val + 1)) :=
          Nat.mul_le_mul_right _ h2leM
      _ = 2 ^ params.d := params.fiber_mul_domainSize i
  have hnum_le :
      1800 * (mJ + 1) ^ 6 * 2 ^ (params.d - (i.val + 1)) * (2 ^ params.d) ^ 2 ≤
        900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3 := by
    calc 1800 * (mJ + 1) ^ 6 * 2 ^ (params.d - (i.val + 1)) * (2 ^ params.d) ^ 2
        = 900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 2 * (2 * 2 ^ (params.d - (i.val + 1))) := by ring
      _ ≤ 900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 2 * 2 ^ params.d :=
          Nat.mul_le_mul_left _ h2ni_le
      _ = 900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3 := by ring
  exact Nat.div_le_div_right hnum_le

/-- Geometric telescoping upper bound on the integer sum of `friJohnsonRoundBound` across all `m`
folding rounds (bounded by `< (1800 * (mJ + 1) ^ 6 * (2 ^ d) ^ 3) / dim 0` independently of `m`). -/
theorem sum_friJohnsonRoundBound_le (params : FRIParams F) (mJ : ℕ) :
    (∑ i : Fin params.m, friJohnsonRoundBound params mJ i) ≤
      (1800 * (mJ + 1) ^ 6 * (2 ^ params.d - 2 ^ (params.d - params.m)) * (2 ^ params.d) ^ 2) /
        params.dim 0 := by
  refine (sum_div_le_div_sum Finset.univ _ (params.one_le_dim 0)).trans_eq ?_
  congr 1
  calc (∑ i : Fin params.m,
        1800 * (mJ + 1) ^ 6 * 2 ^ (params.d - (i.val + 1)) * (2 ^ params.d) ^ 2)
      = ∑ i : Fin params.m,
          2 ^ (params.d - (i.val + 1)) * (1800 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 2) := by
          refine Finset.sum_congr rfl fun _ _ => ?_
          ring
    _ = (∑ i : Fin params.m, 2 ^ (params.d - (i.val + 1))) *
          (1800 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 2) := (Finset.sum_mul _ _ _).symm
    _ = 1800 * (mJ + 1) ^ 6 * (2 ^ params.d - 2 ^ (params.d - params.m)) *
          (2 ^ params.d) ^ 2 := by
          rw [params.sum_domainSize_succ]
          ring

/-- Closed-form geometric Siegel commit-phase error across all `m` single-word 2-to-1 FRI folding
rounds in the Johnson regime (`(1 - 1 / 2 ^ m) * 1800 * (mJ + 1) ^ 6 * (2 ^ d) ^ 2 / (ρ * |F|)`,
bounded independently of `m`; uses this library's original explicit Siegel constant). -/
@[expose] noncomputable def friJohnsonCommitError [Fintype F]
    (params : FRIParams F) (mJ : ℕ) : ℝ :=
  (1 - (1 : ℝ) / (2 : ℝ) ^ params.m) *
    (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
      (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ)))

/-- Geometric sum of per-round Johnson escape probabilities bounded by `friJohnsonCommitError`. -/
theorem sum_friJohnsonRoundEscape_le [Fintype F] (params : FRIParams F) (mJ : ℕ) :
    (∑ i : Fin params.m,
      (friJohnsonRoundBound params mJ i : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ≤
    ENNReal.ofReal (friJohnsonCommitError params mJ) := by
  let num : ℕ :=
    1800 * (mJ + 1) ^ 6 * (2 ^ params.d - 2 ^ (params.d - params.m)) * (2 ^ params.d) ^ 2
  have hsum_nat : (∑ i : Fin params.m, friJohnsonRoundBound params mJ i) ≤ num / params.dim 0 :=
    sum_friJohnsonRoundBound_le params mJ
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
        (1 - (1 : ℝ) / (2 : ℝ) ^ params.m) *
          (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) * (2 ^ params.d : ℝ)) := by
    dsimp only [num]
    push_cast
    rw [cast_two_pow_sub_eq]
    ring
  rw [hnumR, friJohnsonCommitError]
  field_simp

/-- **Unconditional per-round discrete Johnson-bound `WeightedLineGapPerRound`** across all `m`
single-word FRI folding rounds (instantiating [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 5.1
and 7.2] per round with exact `Cslib.Code.ProximityGap.johnsonCurveBound` budgets). -/
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
  intro i W hW_le hW_sum u₀ u₁ hno_corr Z hZ_good
  by_contra hgt
  let M : ℕ := 2 ^ (i.val + 1)
  let N : ℕ := 2 ^ (params.d - (i.val + 1))
  let B_W : ℕ := 2 ^ params.d - e
  have hM_pos : 0 < M := Nat.pow_pos (by omega)
  have hMN : M * N = 2 ^ params.d := params.fiber_mul_domainSize i
  have hceil : (B_W + M - 1) / M = N - e / M := by
    dsimp only [B_W]
    rw [← hMN]
    exact ceil_div_sub_eq_sub_div hM_pos (by rw [hMN]; exact he.le)
  have hα_inj : Function.Injective (params.eval (i.val + 1)) :=
    cosetEval_injective params.hg params.hω (Nat.le_trans i.isLt params.hm)
  have hZ_gt :
      ProximityGap.johnsonCurveBound (Fintype.card (Fin N)) (mRound i)
        (params.dim (i.val + 1) - 1) (DRound i) 1 (2 ^ params.d) < #Z := by
    rw [Fintype.card_fin]
    exact Nat.lt_of_not_ge hgt
  have hclose : ∀ z ∈ Z, ∃ c ∈ params.rsCode (i.val + 1),
      B_W ≤ ∑ j ∈ Finset.univ.filter (fun j => (u₀ + z • u₁) j = c j), W j := by
    intro z hz
    obtain ⟨c, hc_rs, hc_wt⟩ := hZ_good z hz
    refine ⟨c, hc_rs, ?_⟩
    dsimp only [B_W]
    omega
  obtain ⟨D', hD'_wt, v₀, hv₀, v₁, hv₁, hD'_agree⟩ :=
    exists_weighted_correlatedAgreement_line_johnson (W := W) (M := M) (W_tot := 2 ^ params.d)
      (B_W := B_W) hα_inj (params.one_le_dim (i.val + 1)) (hm i) hM_pos hW_le hW_sum
      (by rw [hceil]; exact hk_le i)
      (by rw [Fintype.card_fin]; exact hinterp i)
      (by rw [hceil]; exact hroot i)
      u₀ u₁ Z hZ_gt hclose
  have hsub : D' ⊆ Finset.univ.filter (fun j : Fin N => u₀ j = v₀ j ∧ u₁ j = v₁ j) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hD'_agree j hj⟩
  have hle_B : B_W ≤ 2 ^ params.d - e - 1 :=
    hD'_wt.trans ((Finset.sum_le_sum_of_subset hsub).trans (hno_corr v₀ hv₀ v₁ hv₁))
  dsimp only [B_W] at hle_B
  omega

/-- **Unconditional discrete Johnson-bound `WeightedLineGapBound`** for all `m` single-word FRI
folding rounds, derived as a monotonicity corollary of
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

/-- **Unconditional summed commit-phase soundness of single-word `friIOP` with discrete
Guruswami–Sudan parameters**: sums exact per-round `johnsonCurveBound` budgets without inflating
later rounds to the round-0 bound. -/
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

/-- **Unconditional summed interactive soundness of single-word `friIOP` with discrete
Guruswami–Sudan parameters**: combines summed per-round `johnsonCurveBound` commit escape with the
query-round bound `((2 ^ d - e - 1) / 2 ^ d) ^ q`. -/
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
  rw [friSumError, sum_natCast_div_ennreal]

/-- **Unconditional geometric per-round Johnson-bound `WeightedLineGapPerRound`** across all `m`
single-word FRI folding rounds up to `δ ≤ 1 - √ρ - √ρ / (2 * mJ)` (instantiating
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.4, 5.1, and 7.2] per round with this library's
explicit Siegel constants).

Reuses `Cslib.Code.ProximityGap.johnson_line_params_bound` and
`Cslib.Code.ProximityGap.johnsonCurveBound_mul_le` at every round `i : Fin params.m`, retaining the
halving factor `2 ^ (d - (i + 1))` in `friJohnsonRoundBound params mJ i` so the sum over all `m`
rounds stays independent of `m`. -/
theorem weightedLineGapPerRound_of_johnson [DecidableEq F]
    (params : FRIParams F) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ))) :
    WeightedLineGapPerRound params (2 ^ params.d - e - 1) (friJohnsonRoundBound params mJ) := by
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
      Real.sqrt ((2 ^ (params.d - (i.val + 1)) : ℝ) * (params.dim (i.val + 1) : ℝ))⌉₊ - 1
  have hround_rate : ∀ i : Fin params.m,
      ((params.dim (i.val + 1) : ℝ) / (2 ^ (params.d - (i.val + 1)) : ℝ)) =
        (k₀ : ℝ) / (n₀ : ℝ) := by
    intro i
    have hMN : (2 ^ (i.val + 1) : ℝ) * (2 ^ (params.d - (i.val + 1)) : ℝ) = (n₀ : ℝ) := by
      exact_mod_cast params.fiber_mul_domainSize i
    have hMk : (2 ^ (i.val + 1) : ℝ) * (params.dim (i.val + 1) : ℝ) = (k₀ : ℝ) := by
      exact_mod_cast params.fiber_mul_dim i
    have hM_ne : (2 ^ (i.val + 1) : ℝ) ≠ 0 := by positivity
    rw [← hMk, ← hMN, mul_div_mul_left _ _ hM_ne]
  have hround_he : ∀ i : Fin params.m,
      ((e / 2 ^ (i.val + 1) : ℕ) : ℝ) / (2 ^ (params.d - (i.val + 1)) : ℝ) ≤
        1 - Real.sqrt ((params.dim (i.val + 1) : ℝ) / (2 ^ (params.d - (i.val + 1)) : ℝ)) -
          Real.sqrt ((params.dim (i.val + 1) : ℝ) / (2 ^ (params.d - (i.val + 1)) : ℝ)) /
            (2 * (mJ : ℝ)) := by
    intro i
    rw [hround_rate i]
    have hle_e : ((e / 2 ^ (i.val + 1) : ℕ) : ℝ) / (2 ^ (params.d - (i.val + 1)) : ℝ) ≤
        (e : ℝ) / (n₀ : ℝ) := by
      have hMN : (2 ^ (i.val + 1) : ℝ) * (2 ^ (params.d - (i.val + 1)) : ℝ) = (n₀ : ℝ) := by
        exact_mod_cast params.fiber_mul_domainSize i
      have hdiv_le : ((e / 2 ^ (i.val + 1) : ℕ) : ℝ) * (2 ^ (i.val + 1) : ℝ) ≤ (e : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self e (2 ^ (i.val + 1))
      have hniR : (0 : ℝ) < (2 ^ (params.d - (i.val + 1)) : ℝ) := by positivity
      rw [div_le_div_iff₀ hniR hn₀R, ← hMN]
      nlinarith
    have he' : (e : ℝ) / (n₀ : ℝ) ≤
        1 - Real.sqrt ((k₀ : ℝ) / (n₀ : ℝ)) -
          Real.sqrt ((k₀ : ℝ) / (n₀ : ℝ)) / (2 * (mJ : ℝ)) := by
      simpa only [n₀, k₀, Nat.cast_pow, Nat.cast_ofNat] using he
    exact hle_e.trans he'
  have hparams : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤ 2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1) ∧
      2 ^ (params.d - (i.val + 1)) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)) ∧
      DRound i < mRound i * (2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1)) ∧
      (ProximityGap.johnsonCurveBound (2 ^ (params.d - (i.val + 1))) (mRound i)
        (params.dim (i.val + 1) - 1) (DRound i) 1 (2 ^ (params.d - (i.val + 1))) : ℝ) ≤
        1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ (params.d - (i.val + 1)) : ℝ) ^ 2) /
          ((params.dim (i.val + 1) : ℝ) / (2 ^ (params.d - (i.val + 1)) : ℝ)) := by
    intro i
    have hpack := ProximityGap.johnson_line_params_bound
      (n := 2 ^ (params.d - (i.val + 1))) (k := params.dim (i.val + 1))
      (e := e / 2 ^ (i.val + 1)) (m := mJ)
      (params.one_le_dim (i.val + 1))
      (params.dim_le_domainSize i.isLt)
      hmJ
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hround_he i)
    simpa only [mRound, DRound, Nat.cast_pow, Nat.cast_ofNat] using hpack
  refine (weightedLineGapPerRound_of_johnson_discrete params he_lt mRound DRound
    (fun _ => by dsimp only [mRound]; omega)
    (fun i => (hparams i).1)
    (fun i => (hparams i).2.1)
    (fun i => (hparams i).2.2.1)).mono fun i => ?_
  set ni : ℕ := 2 ^ (params.d - (i.val + 1))
  set ki : ℕ := params.dim (i.val + 1)
  have hni_pos : 0 < ni := Nat.pow_pos (by omega)
  have hniR : (0 : ℝ) < (ni : ℝ) := by exact_mod_cast hni_pos
  have hni_le : ni ≤ n₀ :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le params.d (i.val + 1))
  have hscale_nat := ProximityGap.johnsonCurveBound_mul_le
    (n := ni) (m := mRound i) (d := ki - 1) (D := DRound i) (r := 1) (W_tot := n₀) hni_le
  have hscaleR :
      (ProximityGap.johnsonCurveBound ni (mRound i) (ki - 1) (DRound i) 1 n₀ : ℝ) * (ni : ℝ) ≤
      (ProximityGap.johnsonCurveBound ni (mRound i) (ki - 1) (DRound i) 1 ni : ℝ) * (n₀ : ℝ) := by
    exact_mod_cast hscale_nat
  have hjb_i :
      (ProximityGap.johnsonCurveBound ni (mRound i) (ki - 1) (DRound i) 1 ni : ℝ) ≤
        1800 * ((mJ + 1 : ℝ) ^ 6) * ((ni : ℝ) ^ 2) / ((k₀ : ℝ) / (n₀ : ℝ)) := by
    have h := (hparams i).2.2.2
    rw [hround_rate i] at h
    simpa only [ni, ki, Nat.cast_pow, Nat.cast_ofNat] using h
  have hmul_R :
      (ProximityGap.johnsonCurveBound ni (mRound i) (ki - 1) (DRound i) 1 n₀ : ℝ) * (k₀ : ℝ) ≤
        1800 * ((mJ + 1 : ℝ) ^ 6) * (ni : ℝ) * ((n₀ : ℝ) ^ 2) := by
    have h1 :
        (ProximityGap.johnsonCurveBound ni (mRound i) (ki - 1) (DRound i) 1 n₀ : ℝ) * (ni : ℝ) ≤
          (1800 * ((mJ + 1 : ℝ) ^ 6) * ((ni : ℝ) ^ 2) / ((k₀ : ℝ) / (n₀ : ℝ))) * (n₀ : ℝ) :=
      hscaleR.trans (mul_le_mul_of_nonneg_right hjb_i hn₀R.le)
    have h2 :
        (1800 * ((mJ + 1 : ℝ) ^ 6) * ((ni : ℝ) ^ 2) / ((k₀ : ℝ) / (n₀ : ℝ))) * (n₀ : ℝ) *
          (k₀ : ℝ) =
        1800 * ((mJ + 1 : ℝ) ^ 6) * (ni : ℝ) * ((n₀ : ℝ) ^ 2) * (ni : ℝ) := by
      field_simp
    have h1k := mul_le_mul_of_nonneg_right h1 hk₀R.le
    rw [h2] at h1k
    exact le_of_mul_le_mul_right (by linarith) hniR
  have hmul_nat :
      ProximityGap.johnsonCurveBound ni (mRound i) (ki - 1) (DRound i) 1 n₀ * k₀ ≤
        1800 * (mJ + 1) ^ 6 * ni * n₀ ^ 2 := by
    exact_mod_cast hmul_R
  exact (Nat.le_div_iff_mul_le hk₀_pos).mpr hmul_nat

/-- **Unconditional closed-form uniform Johnson-bound `WeightedLineGapBound`** for all `m`
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

/-- **Original explicit-constant `η`-gap uniform `WeightedLineGapBound`** across all `m` FRI
folding rounds up to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - η` (`0 < η`), derived from
`weightedLineGapBound_of_johnson` and `ProximityGap.exists_multiplicity_of_eta` (using `η` directly
rather than `min(η, √ρ / 20)` in Eq. (1.3)). -/
theorem weightedLineGapBound_of_johnson_eta [DecidableEq F]
    (params : FRIParams F) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η) :
    WeightedLineGapBound params (2 ^ params.d - e - 1)
      (friJohnsonEtaCommitBound params η) := by
  have hk₀_pos : 0 < params.dim 0 := params.one_le_dim 0
  have hk₀_le : params.dim 0 ≤ 2 ^ params.d := by
    simpa only [Nat.sub_zero] using params.dim_le_domainSize (Nat.zero_le params.m)
  obtain ⟨mJ, hmJ, he_mJ, hpow_mJ⟩ :=
    ProximityGap.exists_multiplicity_of_eta hk₀_pos hk₀_le hη
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using he)
  refine (weightedLineGapBound_of_johnson params hmJ
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using he_mJ)).mono fun _ => ?_
  refine Nat.le_floor ?_
  have hk₀R : (0 : ℝ) < (params.dim 0 : ℝ) := by exact_mod_cast hk₀_pos
  have hdiv_le :
      ((friJohnsonCommitBound params mJ : ℕ) : ℝ) ≤
        (900 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 3)) / (params.dim 0 : ℝ) := by
    refine (le_div_iff₀ hk₀R).mpr ?_
    exact_mod_cast Nat.div_mul_le_self (900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3) (params.dim 0)
  calc ((friJohnsonCommitBound params mJ : ℕ) : ℝ)
      ≤ (900 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 3)) / (params.dim 0 : ℝ) := hdiv_le
    _ ≤ (900 * (64 / (η ^ 6)) * ((2 ^ params.d : ℝ) ^ 3)) / (params.dim 0 : ℝ) := by gcongr
    _ = 57600 * ((2 ^ params.d : ℝ) ^ 3) / ((params.dim 0 : ℝ) * (η ^ 6)) := by
        field_simp
        ring

/-- **Unconditional summed commit-phase soundness of single-word `friIOP` up to the Johnson bound**
(using this library's explicit geometric Siegel commit error `friJohnsonCommitError params mJ`,
bounded independently of `m` with zero gap-assumption premise). -/
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

/-- **Unconditional summed interactive soundness of single-word `friIOP` up to the Johnson bound**
(using this library's explicit geometric Siegel commit error `friJohnsonCommitError params mJ`
plus query error `((2 ^ d - e - 1) / 2 ^ d) ^ q`, bounded independently of `m` with zero
gap-assumption premise; batched initial-function correlated agreement and JACM Theorem 8.3's exact
displayed constants remain separate). -/
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

/-- **Unconditional round-by-round soundness of single-word `friIOP` up to the Johnson bound**
([BenSassonBentovHoreshRiabzev2018]; [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.4, 5.1,
and 7.2]).

Establishes both the `IOPRoundByRoundSoundness` invariant and the uniform per-round escape bound
`≤ friRBRError params e (friJohnsonCommitBound params mJ)` for the single-word FRI IOP at every
distance threshold `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - √ρ / (2 * mJ)` over any finite field `F` of
characteristic `≠ 2`, with zero gap-assumption premise. (Batched initial-function correlated
agreement and the exact quantitative error expression of JACM Theorem 8.3 remain open.) -/
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

/-- **Unconditional adaptive BCS-FRI ROM soundness up to the Johnson bound**
([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]), composing `weightedLineGapBound_of_johnson`
with the BCS random-oracle provider `friBCS_romSoundness_bound_of_weightedLineGap` /
`Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound` for the single-word FRI IOP up to
`δ ≤ 1 - √ρ - √ρ / (2 * mJ)`. -/
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

/-- **Unconditional adaptive BCS-FRI ROM soundness with separate prover/verifier Merkle budgets up
to the Johnson bound** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]), composing
`weightedLineGapBound_of_johnson` with
`friBCS_romSoundness_bound_of_prover_verifier_of_weightedLineGap`. -/
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
