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
# Unconditional Unique-Decoding and Johnson-Bound FRI and BCS-FRI ROM Soundness

This module closes the proximity-gap hypothesis of
`CslibFrontier.Crypto.Protocols.FRI.Soundness` unconditionally in both the unique-decoding regime
and the Johnson-bound regime, combining `Cslib.Code.exists_correlatedAgreement_unique`
([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 4.1]) and
`Cslib.Code.exists_weighted_correlatedAgreement_line_johnson`
([BenSassonCarmonIshaiKoppartySaraf2020, Theorems 5.1 and 7.2]) with
`Cslib.Crypto.Protocols.FRI.friIOP_rbrSound`,
`Cslib.Crypto.Protocols.FRI.friRBREscape_of_weightedLineGap`, and
`Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound` ([BenSassonBentovHoreshRiabzev2018];
[BenSassonCarmonIshaiKoppartySaraf2020, Section 8]; [BenSassonChiesaSpooner2016];
[ChiesaYogev2024]).

## Main definitions

* `Cslib.Crypto.Protocols.FRI.friJohnsonCommitBound`: uniform commit-round exceptional-scalar
  budget `(900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3) / params.dim 0` across all `m` FRI folding
  rounds in the Johnson regime with multiplicity slack `mJ`.

## Main results

### Unique-decoding regime (`2 * e + params.dim 0 ≤ 2 ^ params.d`)
* `Cslib.Crypto.Protocols.FRI.weightedLineGapBound_of_unique`: unconditional
  `WeightedLineGapBound` with sharp per-round exceptional-scalar budget `2 ^ (d - 1)`.
* `Cslib.Crypto.Protocols.FRI.friIOP_rbrSound_of_unique`: complete unconditional round-by-round
  soundness (invariant and per-round escape bound `≤ friRBRError params e (2 ^ (params.d - 1))`)
  for `friIOP params` in the unique-decoding regime.
* `Cslib.Crypto.Protocols.FRI.friBCS_romSoundness_bound_of_unique` &
  `Cslib.Crypto.Protocols.FRI.friBCS_romSoundness_bound_of_prover_verifier_of_unique`:
  unconditional adaptive two-channel BCS-FRI ROM soundness bounds in the unique-decoding regime.

### Johnson-bound regime (`δ ≤ 1 - √ρ - √ρ / (2 * mJ)` and tight per-round discrete bounds)
* `Cslib.Crypto.Protocols.FRI.weightedLineGapBound_of_johnson_discrete`: unconditional
  `WeightedLineGapBound` parameterized directly by per-round Guruswami–Sudan parameters
  `(mRound i, DRound i)` and exact `Cslib.Code.ProximityGap.johnsonCurveBound` budgets.
* `Cslib.Crypto.Protocols.FRI.weightedLineGapBound_of_johnson`: closed-form unconditional
  `WeightedLineGapBound` up to the Johnson bound `1 - √ρ - √ρ / (2 * mJ)` with uniform commit
  budget `friJohnsonCommitBound params mJ`.
* `Cslib.Crypto.Protocols.FRI.friIOP_rbrSound_of_johnson`: complete unconditional round-by-round
  soundness (invariant and per-round escape bound `≤ friRBRError params e (friJohnsonCommitBound
  params mJ)`) for `friIOP params` up to the Johnson bound.
* `Cslib.Crypto.Protocols.FRI.friBCS_romSoundness_bound_of_johnson` &
  `Cslib.Crypto.Protocols.FRI.friBCS_romSoundness_bound_of_prover_verifier_of_johnson`:
  unconditional adaptive two-channel BCS-FRI ROM soundness bounds up to the Johnson bound.

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

/-- Fiber-size product identity `2 ^ (i + 1) * 2 ^ (d - (i + 1)) = 2 ^ d` for `i < m`. -/
private theorem fri_fiber_mul_domainSize (params : FRIParams F) (i : Fin params.m) :
    2 ^ (i.val + 1) * 2 ^ (params.d - (i.val + 1)) = 2 ^ params.d := by
  have hle : i.val + 1 ≤ params.d := Nat.le_trans i.isLt params.hm
  rw [← pow_add, Nat.add_sub_of_le hle]

/-- Round-dimension scaling identity `2 ^ (i + 1) * params.dim (i + 1) = params.dim 0`. -/
private theorem fri_fiber_mul_dim (params : FRIParams F) (i : Fin params.m) :
    2 ^ (i.val + 1) * params.dim (i.val + 1) = params.dim 0 := by
  have hle : i.val + 1 ≤ params.m := i.isLt
  simp only [FRIParams.dim, Nat.sub_zero]
  calc 2 ^ (i.val + 1) * (params.kFinal * 2 ^ (params.m - (i.val + 1)))
      = params.kFinal * (2 ^ (i.val + 1) * 2 ^ (params.m - (i.val + 1))) := by ring
    _ = params.kFinal * 2 ^ params.m := by rw [← pow_add, Nat.add_sub_of_le hle]

/-- Each active round dimension is at least `1`. -/
private theorem fri_one_le_dim (params : FRIParams F) (r : ℕ) : 1 ≤ params.dim r := by
  simp only [FRIParams.dim]
  exact Nat.mul_pos params.hkPos (Nat.pow_pos (by omega))

/-- Each active round dimension fits inside its active coset size (`r ≤ m`). -/
private theorem fri_dim_le_domainSize (params : FRIParams F) {r : ℕ} (hr : r ≤ params.m) :
    params.dim r ≤ 2 ^ (params.d - r) := by
  have hle : params.m ≤ params.d := params.hm
  have hsub : (params.d - params.m) + (params.m - r) = params.d - r := by omega
  calc params.dim r
      = params.kFinal * 2 ^ (params.m - r) := rfl
    _ ≤ 2 ^ (params.d - params.m) * 2 ^ (params.m - r) :=
        Nat.mul_le_mul_right _ params.hkLe
    _ = 2 ^ (params.d - r) := by rw [← pow_add, hsub]

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

end Helpers

/-! ### Unconditional Unique-Decoding FRI & BCS-FRI ROM Soundness -/

section UniqueDecoding

variable {F : Type} [Field F]

/-- **Unconditional unique-decoding `WeightedLineGapBound`** for all `m` FRI folding rounds
([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 4.1 & Section 7]).

Discharges `UniqueLineGapHypothesis` directly from `Cslib.Code.exists_correlatedAgreement_unique`
over an arbitrary field `F` of characteristic `≠ 2`, yielding the sharp per-round exceptional-scalar
bound `2 ^ (d - 1)` with zero gap-assumption premise. -/
theorem weightedLineGapBound_of_unique [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) :
    WeightedLineGapBound params (2 ^ params.d - e - 1) (2 ^ (params.d - 1)) := by
  refine weightedLineGapBound_of_uniqueLineGap params huniq ?_
  intro i u₀ u₁ Z hZ_gt hZ_close
  let M : ℕ := 2 ^ (i.val + 1)
  let N : ℕ := 2 ^ (params.d - (i.val + 1))
  have hM_pos : 0 < M := Nat.pow_pos (by omega)
  have hMN : M * N = 2 ^ params.d := fri_fiber_mul_domainSize params i
  have hdim_mul : M * params.dim (i.val + 1) = params.dim 0 := fri_fiber_mul_dim params i
  have huniq_i : 2 * (e / M) + params.dim (i.val + 1) ≤ Fintype.card (Fin N) := by
    rw [Fintype.card_fin]
    have hmul : M * (2 * (e / M) + params.dim (i.val + 1)) ≤ M * N := by
      calc M * (2 * (e / M) + params.dim (i.val + 1))
          = 2 * (M * (e / M)) + M * params.dim (i.val + 1) := by ring
        _ ≤ 2 * e + params.dim 0 := by
            rw [hdim_mul]
            exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.mul_div_le e M)) _
        _ ≤ 2 ^ params.d := huniq
        _ = M * N := hMN.symm
    exact Nat.le_of_mul_le_mul_left hmul hM_pos
  have hα_inj : Function.Injective (params.eval (i.val + 1)) :=
    cosetEval_injective params.hg params.hω (Nat.le_trans i.isLt params.hm)
  obtain ⟨D', hD'_card, v₀, hv₀, v₁, hv₁, hD'_agree⟩ :=
    exists_correlatedAgreement_unique hα_inj huniq_i u₀ u₁ Z
      (by simpa only [Fintype.card_fin] using hZ_gt) hZ_close
  exact ⟨D', v₀, hv₀, v₁, hv₁, by simpa only [Fintype.card_fin] using hD'_card, hD'_agree⟩

/-- **Unconditional round-by-round soundness of `friIOP` in the unique-decoding regime**
([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 4.1 & Section 8]).

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
([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 4.1 & Section 8];
[BenSassonChiesaSpooner2016]).

Directly combines `weightedLineGapBound_of_unique` (`B_commit = 2 ^ (d - 1)`) with
`friBCS_romSoundness_bound_of_weightedLineGap`, requiring no external proximity-gap premise. -/
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
the unique-decoding regime** ([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 4.1 & Section 8];
[BenSassonChiesaSpooner2016]). -/
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
        ((t_MT + params.queryCount * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.queryCount * (L_path + 1)) +
              (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBCS_romSoundness_bound_of_prover_verifier_of_weightedLineGap params
    (weightedLineGapBound_of_unique params huniq) hdec σ hMT hFS hops

end UniqueDecoding

/-! ### Unconditional Johnson-Bound FRI & BCS-FRI ROM Soundness -/

section JohnsonBound

variable {F : Type} [Field F]

/-- Uniform per-round commit-phase exceptional-scalar bound for FRI in the Johnson regime with
multiplicity slack `mJ`: `(900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3) / params.dim 0`. -/
abbrev friJohnsonCommitBound (params : FRIParams F) (mJ : ℕ) : ℕ :=
  (900 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3) / params.dim 0

/-- **Unconditional discrete Johnson-bound `WeightedLineGapBound`** for all `m` FRI folding rounds
([BenSassonCarmonIshaiKoppartySaraf2020, Theorems 5.1, 7.2, and Section 8]).

Given explicit per-round Guruswami–Sudan interpolation parameters `(mRound i, DRound i)` satisfying
the interpolation and root-divisibility inequalities at each folding round `i`, discharges
`WeightedLineGapBound params (2 ^ params.d - e - 1) B_commit` directly from
`Cslib.Code.exists_weighted_correlatedAgreement_line_johnson` with exact
`Cslib.Code.ProximityGap.johnsonCurveBound` budgets and zero gap-assumption premise. -/
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
    WeightedLineGapBound params (2 ^ params.d - e - 1) B_commit := by
  intro i W hW_le hW_sum u₀ u₁ hno_corr Z hZ_good
  by_contra hgt
  let M : ℕ := 2 ^ (i.val + 1)
  let N : ℕ := 2 ^ (params.d - (i.val + 1))
  let B_W : ℕ := 2 ^ params.d - e
  have hM_pos : 0 < M := Nat.pow_pos (by omega)
  have hMN : M * N = 2 ^ params.d := fri_fiber_mul_domainSize params i
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
    exact lt_of_le_of_lt (hbound i) (Nat.lt_of_not_ge hgt)
  have hclose : ∀ z ∈ Z, ∃ c ∈ params.rsCode (i.val + 1),
      B_W ≤ ∑ j ∈ Finset.univ.filter (fun j => (u₀ + z • u₁) j = c j), W j := by
    intro z hz
    obtain ⟨c, hc_rs, hc_wt⟩ := hZ_good z hz
    refine ⟨c, hc_rs, ?_⟩
    dsimp only [B_W]
    omega
  obtain ⟨D', hD'_wt, v₀, hv₀, v₁, hv₁, hD'_agree⟩ :=
    exists_weighted_correlatedAgreement_line_johnson (W := W) (M := M) (W_tot := 2 ^ params.d)
      (B_W := B_W) hα_inj (fri_one_le_dim params (i.val + 1)) (hm i) hM_pos hW_le hW_sum
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

/-- **Unconditional closed-form Johnson-bound `WeightedLineGapBound`** for all `m` FRI folding
rounds up to `δ ≤ 1 - √ρ - √ρ / (2 * mJ)` ([BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.4,
5.1, 7.2, and Section 8]).

Reuses `Cslib.Code.ProximityGap.johnson_line_params_bound` and
`Cslib.Code.ProximityGap.johnsonCurveBound_mul_le` at every round `i : Fin params.m` (exploiting
round-invariance of the code rate `ρ = params.dim 0 / 2 ^ d` and `2 * 2 ^ (d - (i + 1)) ≤ 2 ^ d`)
to establish `WeightedLineGapBound` with the uniform budget `friJohnsonCommitBound params mJ` and
zero gap-assumption premise. -/
theorem weightedLineGapBound_of_johnson [DecidableEq F]
    (params : FRIParams F) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ))) :
    WeightedLineGapBound params (2 ^ params.d - e - 1) (friJohnsonCommitBound params mJ) := by
  set n₀ : ℕ := 2 ^ params.d
  set k₀ : ℕ := params.dim 0
  have hn₀_pos : 0 < n₀ := Nat.pow_pos (by omega)
  have hk₀_pos : 0 < k₀ := fri_one_le_dim params 0
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
      exact_mod_cast fri_fiber_mul_domainSize params i
    have hMk : (2 ^ (i.val + 1) : ℝ) * (params.dim (i.val + 1) : ℝ) = (k₀ : ℝ) := by
      exact_mod_cast fri_fiber_mul_dim params i
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
        exact_mod_cast fri_fiber_mul_domainSize params i
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
      (fri_one_le_dim params (i.val + 1))
      (fri_dim_le_domainSize params i.isLt)
      hmJ
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hround_he i)
    simpa only [mRound, DRound, Nat.cast_pow, Nat.cast_ofNat] using hpack
  refine weightedLineGapBound_of_johnson_discrete params he_lt mRound DRound
    (fun _ => by dsimp only [mRound]; omega)
    (fun i => (hparams i).1)
    (fun i => (hparams i).2.1)
    (fun i => (hparams i).2.2.1)
    (fun i => ?_)
  set ni : ℕ := 2 ^ (params.d - (i.val + 1))
  set ki : ℕ := params.dim (i.val + 1)
  have hni_pos : 0 < ni := Nat.pow_pos (by omega)
  have hniR : (0 : ℝ) < (ni : ℝ) := by exact_mod_cast hni_pos
  have h2ni_le : 2 * ni ≤ n₀ := by
    have h2leM : 2 ≤ 2 ^ (i.val + 1) := by
      have : 2 ^ 1 ≤ 2 ^ (i.val + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      simpa only [pow_one] using this
    calc 2 * ni ≤ 2 ^ (i.val + 1) * ni := Nat.mul_le_mul_right ni h2leM
      _ = n₀ := fri_fiber_mul_domainSize params i
  have hni_le : ni ≤ n₀ := by omega
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
        900 * ((mJ + 1 : ℝ) ^ 6) * ((n₀ : ℝ) ^ 3) := by
    have h1 :
        (ProximityGap.johnsonCurveBound ni (mRound i) (ki - 1) (DRound i) 1 n₀ : ℝ) * (ni : ℝ) ≤
          (1800 * ((mJ + 1 : ℝ) ^ 6) * ((ni : ℝ) ^ 2) / ((k₀ : ℝ) / (n₀ : ℝ))) * (n₀ : ℝ) :=
      hscaleR.trans (mul_le_mul_of_nonneg_right hjb_i hn₀R.le)
    have h2 :
        (1800 * ((mJ + 1 : ℝ) ^ 6) * ((ni : ℝ) ^ 2) / ((k₀ : ℝ) / (n₀ : ℝ))) * (n₀ : ℝ) *
          (k₀ : ℝ) =
        1800 * ((mJ + 1 : ℝ) ^ 6) * ((ni : ℝ) ^ 2) * ((n₀ : ℝ) ^ 2) := by
      field_simp
    have h3 :
        (ProximityGap.johnsonCurveBound ni (mRound i) (ki - 1) (DRound i) 1 n₀ : ℝ) * (k₀ : ℝ) *
          (ni : ℝ) ≤
        900 * ((mJ + 1 : ℝ) ^ 6) * ((n₀ : ℝ) ^ 3) * (ni : ℝ) := by
      have h2niR : 2 * (ni : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast h2ni_le
      have h1k := mul_le_mul_of_nonneg_right h1 hk₀R.le
      rw [h2] at h1k
      have hstep :
          1800 * ((mJ + 1 : ℝ) ^ 6) * ((ni : ℝ) ^ 2) * ((n₀ : ℝ) ^ 2) ≤
            900 * ((mJ + 1 : ℝ) ^ 6) * ((n₀ : ℝ) ^ 3) * (ni : ℝ) := by
        have hcoeff_nn : 0 ≤ 900 * ((mJ + 1 : ℝ) ^ 6) * (ni : ℝ) * ((n₀ : ℝ) ^ 2) := by
          positivity
        calc 1800 * ((mJ + 1 : ℝ) ^ 6) * ((ni : ℝ) ^ 2) * ((n₀ : ℝ) ^ 2)
            = 900 * ((mJ + 1 : ℝ) ^ 6) * (ni : ℝ) * ((n₀ : ℝ) ^ 2) * (2 * (ni : ℝ)) := by ring
          _ ≤ 900 * ((mJ + 1 : ℝ) ^ 6) * (ni : ℝ) * ((n₀ : ℝ) ^ 2) * (n₀ : ℝ) :=
              mul_le_mul_of_nonneg_left h2niR hcoeff_nn
          _ = 900 * ((mJ + 1 : ℝ) ^ 6) * ((n₀ : ℝ) ^ 3) * (ni : ℝ) := by ring
      linarith
    exact le_of_mul_le_mul_right h3 hniR
  have hmul_nat :
      ProximityGap.johnsonCurveBound ni (mRound i) (ki - 1) (DRound i) 1 n₀ * k₀ ≤
        900 * (mJ + 1) ^ 6 * n₀ ^ 3 := by
    exact_mod_cast hmul_R
  exact (Nat.le_div_iff_mul_le hk₀_pos).mpr hmul_nat

/-- **Unconditional round-by-round soundness of `friIOP` up to the Johnson bound**
([BenSassonCarmonIshaiKoppartySaraf2020, Section 8]).

Establishes both the `IOPRoundByRoundSoundness` invariant and the uniform per-round escape bound
`≤ friRBRError params e (friJohnsonCommitBound params mJ)` for every distance threshold
`(e : ℝ) / 2 ^ d ≤ 1 - √ρ - √ρ / (2 * mJ)` over any finite field `F` of characteristic `≠ 2`,
with zero gap-assumption premise. -/
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
([BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.4, 5.1, 7.2, and Section 8];
[BenSassonChiesaSpooner2016]; [ChiesaYogev2024]).

Composes `friIOP_rbrSound_of_johnson` with `Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound`,
yielding an unconditional non-interactive random-oracle soundness bound for Reed–Solomon proximity
up to `δ ≤ 1 - √ρ - √ρ / (2 * mJ)` with zero gap-assumption premise. -/
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
to the Johnson bound** ([BenSassonCarmonIshaiKoppartySaraf2020, Section 8];
[BenSassonChiesaSpooner2016]). -/
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
        ((t_MT + params.queryCount * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.queryCount * (L_path + 1)) +
              (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBCS_romSoundness_bound_of_prover_verifier_of_weightedLineGap params
    (weightedLineGapBound_of_johnson params hmJ he) hdec σ hMT hFS hops

end JohnsonBound

end Cslib.Crypto.Protocols.FRI
