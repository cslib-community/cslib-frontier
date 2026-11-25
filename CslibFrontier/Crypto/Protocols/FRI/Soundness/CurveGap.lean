/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.BCS.Interactive
public import CslibFrontier.Crypto.Protocols.FRI.Soundness.Transcript
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Foundations.Data.Hamming

/-!
# Smooth FRI Doomed Predicates, Error Budgets, Curve-Gap Contracts, and Unique-Decoding Upgrade

Defines the smooth round-by-round doomed/good-step predicates (`friSmoothCommitDoomed`,
`friSmoothDoomed`, `friSmoothGoodStep`), error budget expressions (`friSmoothRoundEscape`,
`friSmoothSumError`, `friSmoothSupRBRError`, `friSmoothRBRError`), interactive commit-phase game
(`friSmoothCommitGame`), polymorphic per-round degree-`(l⁽ⁱ⁾ - 1)` curve proximity-gap and escape
contracts (`WeightedCurveGapPerRound`, `WeightedCurveGapBound`, `WeightedCurveEscapePerRound`,
`UniqueCurveGapHypothesis`), and the unique-decoding curve-gap upgrade theorems
(`weightedCurveGapPerRound_of_uniqueCurveGap`, `weightedCurveGapBound_of_uniqueCurveGap`).
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Cslib.Code
open Cslib.OracleComp
open Cslib.Crypto.Protocols.BCS
open Cslib.Probability

/-! ### Smooth Round-by-Round Predicates, Error Budgets, and Commit Game -/

section SmoothSoundnessDefs

variable {F : Type} [Field F]

/-- Smooth commit-round doomed predicate at round `i ≤ m`: no codeword in `params.rsCode i` achieves
`friSmoothPreWeight`-weighted agreement `> B` with `friSmoothTargetWord`. -/
@[expose] def friSmoothCommitDoomed [DecidableEq F] (params : FRISmoothParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) : Prop :=
  ∀ c ∈ params.rsCode i,
    (∑ j ∈ Finset.univ.filter (fun j => friSmoothTargetWord params stmt pref i hi j = c j),
      friSmoothPreWeight params stmt pref i hi j) ≤ B

/-- **Smooth FRI round-by-round doomed-state predicate**:
* For prefixes of length `i ≤ m`, `friSmoothCommitDoomed` holds at round `i`.
* For complete transcripts of length `m + 1`, at least one of the `q` queried starting positions
  fails `friSmoothTranscriptSingleAccepts`.
* For unreachable lengths `> m + 1`, holds trivially (`True`). -/
@[expose] def friSmoothDoomed [DecidableEq F] (params : FRISmoothParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) : Prop :=
  if h : pref.length ≤ params.m then
    friSmoothCommitDoomed params B stmt pref pref.length h
  else if pref.length = params.m + 1 then
    ∃ a : Fin params.q,
      ¬ friSmoothTranscriptSingleAccepts params stmt pref (prefQueryIdxs pref params.m a)
  else
    True

/-- **Smooth FRI round-by-round good-step predicate**: for `pref.length ≤ m`, extending `pref` by
`(π, c)` preserves `friSmoothDoomed`; for unreachable lengths `> m`, holds trivially (`True`) so the
escape event `{c | ¬ friSmoothGoodStep ... c}` is empty. -/
@[expose] def friSmoothGoodStep [DecidableEq F] (params : FRISmoothParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (π : OracleTable params.d F) (c : FRIChal F params.d params.q) : Prop :=
  if pref.length ≤ params.m then
    friSmoothDoomed params B stmt (pref ++ [(π, c)])
  else
    True


/-- Per-round escape budget vector for single-word `(m + 1)`-round `friSmoothIOP`: `ε_commit i` in
folding rounds `0 ≤ i < m`, and `((2 ^ d - e - 1) / 2 ^ d) ^ q` in the final query round `m`. -/
@[expose] noncomputable def friSmoothRoundEscape (params : FRISmoothParams F) (e : ℕ)
    (ε_commit : Fin params.m → ℝ≥0∞) (j : Fin (params.m + 1)) : ℝ≥0∞ :=
  if hj : j.val < params.m then
    ε_commit ⟨j.val, hj⟩
  else
    (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q

/-- Summed interactive smooth FRI soundness error
`(∑ i : Fin m, ε_commit i) + ((2 ^ d - e - 1) / 2 ^ d) ^ q`. -/
@[expose] noncomputable def friSmoothSumError (params : FRISmoothParams F) (e : ℕ)
    (ε_commit : Fin params.m → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ i : Fin params.m, ε_commit i) +
    (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q

/-- The sum of `friSmoothRoundEscape` over all `m + 1` rounds equals `friSmoothSumError`. -/
theorem sum_friSmoothRoundEscape_eq_friSmoothSumError (params : FRISmoothParams F) (e : ℕ)
    (ε_commit : Fin params.m → ℝ≥0∞) :
    (∑ j : Fin (params.m + 1), friSmoothRoundEscape params e ε_commit j) =
      friSmoothSumError params e ε_commit := by
  rw [Fin.sum_univ_castSucc, friSmoothSumError]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [friSmoothRoundEscape, Fin.val_castSucc, i.isLt, ↓reduceDIte, Fin.eta]
  · simp only [friSmoothRoundEscape, Fin.val_last, lt_irrefl, ↓reduceDIte]

/-- Uniform per-round escape error `sup_j (friSmoothRoundEscape params e ε_commit j)` across all
`m + 1` rounds of `friSmoothIOP`. -/
@[expose] noncomputable def friSmoothSupRBRError (params : FRISmoothParams F) (e : ℕ)
    (ε_commit : Fin params.m → ℝ≥0∞) : ℝ≥0∞ :=
  Finset.univ.sup (friSmoothRoundEscape params e ε_commit)

/-- Uniform per-round escape error for smooth FRI: the maximum of the commit-round error
`B_commit / |F|` and the batched query-round error `((2 ^ d - e - 1) / 2 ^ d) ^ q`. -/
@[expose] noncomputable def friSmoothRBRError [Fintype F] (params : FRISmoothParams F)
    (e B_commit : ℕ) : ℝ≥0∞ :=
  max ((B_commit : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
    ((((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q)

/-- For a uniform commit-round error `B_commit / |F|`, `friSmoothSupRBRError` is bounded above by
`friSmoothRBRError`. -/
theorem friSmoothSupRBRError_const_le_friSmoothRBRError [Fintype F] (params : FRISmoothParams F)
    (e B_commit : ℕ) :
    friSmoothSupRBRError params e (fun _ => (B_commit : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ≤
      friSmoothRBRError params e B_commit := by
  refine Finset.sup_le fun j _ => ?_
  by_cases hj : j.val < params.m
  · simp only [friSmoothRoundEscape, hj, ↓reduceDIte]
    exact le_max_left _ _
  · simp only [friSmoothRoundEscape, hj, ↓reduceDIte]
    exact le_max_right _ _


/-- Single-word smooth FRI commit-phase game: runs `m` interactive smooth folding rounds and samples
the final committed oracle `πFinal ← P pref`, returning `true` iff strictly more than `B` starting
points in `Fin (2 ^ d)` pass `friSmoothFinalPasses`. -/
@[expose] noncomputable def friSmoothCommitGame [Fintype F] (params : FRISmoothParams F)
    (B : ℕ) (stmt : OracleTable params.d F)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) : PMF Bool :=
  (iopRunRounds P params.m []).bind fun pref =>
    (P pref).map fun πFinal =>
      letI : DecidablePred (fun s => friSmoothFinalPasses params stmt pref πFinal s) :=
        Classical.decPred _
      decide (B < (Finset.univ.filter fun s => friSmoothFinalPasses params stmt pref πFinal s).card)


end SmoothSoundnessDefs

/-! ### Weighted Curve Gap / Escape Contracts -/

section SmoothCurveGapContracts

variable {F : Type} [Field F]

/-- **Polymorphic per-round weighted degree-`(l⁽ⁱ⁾ - 1)` curve proximity-gap contract** across all
`m` smooth FRI folding rounds at agreement threshold `B` and per-round exceptional-scalar budgets
`B_commit : Fin params.m → ℕ`. -/
@[expose] def WeightedCurveGapPerRound [DecidableEq F] (params : FRISmoothParams F)
    (B : ℕ) (B_commit : Fin params.m → ℕ) : Prop :=
  ∀ (i : Fin params.m) (W : Fin (params.domainSize (i.val + 1)) → ℕ),
    (∀ j, W j ≤ 2 ^ params.cumLog (i.val + 1)) →
    (∑ j, W j ≤ 2 ^ params.d) →
    ∀ (u : Fin (params.arity i) → Fin (params.domainSize (i.val + 1)) → F),
      (∀ v : Fin (params.arity i) → Fin (params.domainSize (i.val + 1)) → F,
        (∀ r, v r ∈ params.rsCode (i.val + 1)) →
        (∑ j ∈ Finset.univ.filter (fun j => ∀ r : Fin (params.arity i), u r j = v r j), W j) ≤
          B) →
      ∀ Z : Finset F,
        (∀ z ∈ Z, ∃ v ∈ params.rsCode (i.val + 1),
          B < ∑ j ∈ Finset.univ.filter
            (fun j => (∑ r : Fin (params.arity i), z ^ r.val • u r) j = v j), W j) →
        Z.card ≤ B_commit i

/-- Pointwise monotonicity of `WeightedCurveGapPerRound` in the per-round scalar budget. -/
theorem WeightedCurveGapPerRound.mono [DecidableEq F] {params : FRISmoothParams F} {B : ℕ}
    {B₁ B₂ : Fin params.m → ℕ} (hgap : WeightedCurveGapPerRound params B B₁)
    (hle : ∀ i : Fin params.m, B₁ i ≤ B₂ i) :
    WeightedCurveGapPerRound params B B₂ :=
  fun i W hW_le hW_sum u hno Z hZ =>
    (hgap i W hW_le hW_sum u hno Z hZ).trans (hle i)

/-- **Polymorphic uniform weighted curve proximity-gap contract** for all `m` smooth FRI folding
rounds at agreement threshold `B` and uniform bad-scalar budget `B_commit` (definitionally equal to
`WeightedCurveGapPerRound params B (fun _ => B_commit)`). -/
@[expose] def WeightedCurveGapBound [DecidableEq F] (params : FRISmoothParams F)
    (B B_commit : ℕ) : Prop :=
  WeightedCurveGapPerRound params B (fun _ => B_commit)

/-- **Polymorphic per-round weighted curve escape-probability contract** across all `m` smooth FRI
folding rounds at agreement threshold `B` and per-round escape probability budgets
`ε_commit : Fin params.m → ℝ≥0∞` (matching [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 7.2]
with degree-`(l⁽ⁱ⁾ - 1)` curves). -/
@[expose] def WeightedCurveEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (B : ℕ) (ε_commit : Fin params.m → ℝ≥0∞) : Prop :=
  ∀ (i : Fin params.m) (W : Fin (params.domainSize (i.val + 1)) → ℕ),
    (∀ j, W j ≤ 2 ^ params.cumLog (i.val + 1)) →
    (∑ j, W j ≤ 2 ^ params.d) →
    ∀ (u : Fin (params.arity i) → Fin (params.domainSize (i.val + 1)) → F),
      (∀ v : Fin (params.arity i) → Fin (params.domainSize (i.val + 1)) → F,
        (∀ r, v r ∈ params.rsCode (i.val + 1)) →
        (∑ j ∈ Finset.univ.filter (fun j => ∀ r : Fin (params.arity i), u r j = v r j), W j) ≤
          B) →
      (PMF.uniformOfFintype F).toOuterMeasure
        {z : F | ∃ v ∈ params.rsCode (i.val + 1),
          B < ∑ j ∈ Finset.univ.filter
            (fun j => (∑ r : Fin (params.arity i), z ^ r.val • u r) j = v j), W j} ≤
        ε_commit i

/-- Pointwise monotonicity of `WeightedCurveEscapePerRound` in the per-round escape budget. -/
theorem WeightedCurveEscapePerRound.mono [Fintype F] [DecidableEq F]
    {params : FRISmoothParams F} {B : ℕ} {ε₁ ε₂ : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params B ε₁)
    (hle : ∀ i : Fin params.m, ε₁ i ≤ ε₂ i) :
    WeightedCurveEscapePerRound params B ε₂ :=
  fun i W hW_le hW_sum u hno => (hesc i W hW_le hW_sum u hno).trans (hle i)

/-- Every integer per-round bad-scalar bound `WeightedCurveGapPerRound params B B_commit` induces a
per-round escape-probability bound `ε_commit i = B_commit i / |F|`. -/
theorem weightedCurveEscapePerRound_of_gapPerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {B : ℕ} {B_commit : Fin params.m → ℕ}
    (hgap : WeightedCurveGapPerRound params B B_commit) :
    WeightedCurveEscapePerRound params B
      (fun i => (B_commit i : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) := by
  intro i W hW_le hW_sum u hno_corr
  classical
  rw [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype, ← div_eq_mul_inv]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr
    (hgap i W hW_le hW_sum u hno_corr _ fun z hz => (Finset.mem_filter.mp hz).2)) _


end SmoothCurveGapContracts

/-! ### Smooth Unique-Decoding Curve-Gap Upgrade -/

section SmoothUniqueDecodingUpgrade

variable {F : Type} [Field F]

/-- Unweighted degree-`(l⁽ⁱ⁾ - 1)` curve proximity-gap hypothesis across all `m` smooth FRI folding
rounds at unique-decoding radii `e / 2 ^ cumLog (i + 1)` (matching
[BenSassonCarmonIshaiKoppartySaraf2020, Theorem 6.1]). -/
@[expose] def UniqueCurveGapHypothesis [DecidableEq F] (params : FRISmoothParams F) (e : ℕ) :
    Prop :=
  ∀ (i : Fin params.m)
    (u : Fin (params.arity i) → Fin (params.domainSize (i.val + 1)) → F) (Z : Finset F),
    (params.arity i - 1) * params.domainSize (i.val + 1) < Z.card →
    (∀ z ∈ Z, ∃ v ∈ params.rsCode (i.val + 1),
      hammingDist (∑ r : Fin (params.arity i), z ^ r.val • u r) v ≤
        e / 2 ^ params.cumLog (i.val + 1)) →
    ∃ D' : Finset (Fin (params.domainSize (i.val + 1))),
      ∃ v : Fin (params.arity i) → Fin (params.domainSize (i.val + 1)) → F,
        (∀ r, v r ∈ params.rsCode (i.val + 1)) ∧
        params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1) ≤ D'.card ∧
        ∀ j ∈ D', ∀ r : Fin (params.arity i), u r j = v r j

omit [Field F] in
private theorem hammingDist_le_div_of_weighted_agree [DecidableEq F] {N M total e : ℕ}
    (hM : 0 < M) (hMN : M * N = total) (he : e < total) {W : Fin N → ℕ} (hW : ∀ j, W j ≤ M)
    {x y : Fin N → F} (hwt : total - e - 1 < ∑ j ∈ Finset.univ.filter (fun j => x j = y j), W j) :
    hammingDist x y ≤ e / M := by
  let S := Finset.univ.filter fun j : Fin N => x j = y j
  have hsum : (∑ j ∈ S, W j) ≤ M * S.card :=
    (Finset.sum_le_sum fun j _ => hW j).trans_eq (by rw [Finset.sum_const, smul_eq_mul, mul_comm])
  have hpart : S.card + hammingDist x y = N := by
    simpa only [S, Fintype.card_fin] using card_filter_eq_add_hammingDist x y
  have hmul : M * S.card + M * hammingDist x y = total := by rw [← mul_add, hpart, hMN]
  refine (Nat.le_div_iff_mul_le hM).mpr ?_
  rw [mul_comm]
  change total - e - 1 < ∑ j ∈ S, W j at hwt
  omega

/-- **Conditional step (shrinking per-round smooth unique-decoding weighted upgrade)**: inside the
unique-decoding regime `2 * e + params.dim 0 ≤ 2 ^ d`, assuming `UniqueCurveGapHypothesis params e`
yields `WeightedCurveGapPerRound` via `Folding.lean`'s `weighted_agree_of_curve_many` with
telescoping budget `fun i => (params.arity i - 1) * params.domainSize (i.val + 1)` (whose sum over
all `m` rounds is `2 ^ d - 2 ^ (d - totalLog) < 2 ^ d`). This does not itself prove the unweighted
curve proximity-gap theorem. -/
theorem weightedCurveGapPerRound_of_uniqueCurveGap [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    (hgap : UniqueCurveGapHypothesis params e) :
    WeightedCurveGapPerRound params (2 ^ params.d - e - 1)
      (fun i => (params.arity i - 1) * params.domainSize (i.val + 1)) := by
  intro i W hW_le _ u hno_corr Z hZ_good
  have hM_pos : 0 < 2 ^ params.cumLog (i.val + 1) := Nat.pow_pos (by omega)
  have hMN := params.two_pow_cumLog_mul_domainSize i.isLt
  have he_lt : e < 2 ^ params.d := by have := params.one_le_dim 0; omega
  by_contra hgt
  have hZ_gt : (params.arity i - 1) * params.domainSize (i.val + 1) < Z.card :=
    Nat.lt_of_not_ge hgt
  obtain ⟨D', v, hv_rs, hD'_card, hD'_agree⟩ := hgap i u Z hZ_gt fun z hz =>
    let ⟨w, hw, hwt⟩ := hZ_good z hz
    ⟨w, hw, hammingDist_le_div_of_weighted_agree hM_pos hMN he_lt hW_le hwt⟩
  have hgood_curve (z : F) (hz : z ∈ Z) :
      2 ^ params.d - e - 1 < ∑ j ∈ Finset.univ.filter (fun j =>
        (∑ r : Fin (params.arity i), z ^ r.val * u r j) =
          ∑ r : Fin (params.arity i), z ^ r.val * v r j), W j := by
    obtain ⟨w, hw_rs, hw_wt⟩ := hZ_good z hz
    have hcurve_rs : (∑ r : Fin (params.arity i), z ^ r.val • v r) ∈ params.rsCode (i.val + 1) :=
      Submodule.sum_mem _ fun r _ => (params.rsCode (i.val + 1)).smul_mem _ (hv_rs r)
    have hsub : D' ⊆ Finset.univ.filter (fun j =>
        (∑ r : Fin (params.arity i), z ^ r.val • u r) j =
          (∑ r : Fin (params.arity i), z ^ r.val • v r) j) := fun j hj => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      exact Finset.sum_congr rfl fun r _ => by rw [hD'_agree j hj r]
    have hpart := card_filter_eq_add_hammingDist
      (∑ r : Fin (params.arity i), z ^ r.val • u r) (∑ r : Fin (params.arity i), z ^ r.val • v r)
    rw [Fintype.card_fin] at hpart
    have hcard := Finset.card_le_card hsub
    have hweq := eq_of_hammingDist_le_reedSolomon
      (cosetEval_injective params.hg params.hω (params.cumLog_le_d i.isLt))
      (by simpa only [Fintype.card_fin] using params.two_mul_div_add_dim_le huniq i)
      hw_rs hcurve_rs (hammingDist_le_div_of_weighted_agree hM_pos hMN he_lt hW_le hw_wt)
      (by omega)
    rw [hweq] at hw_wt
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hw_wt
  have hZ_filt : (params.arity i - 1) * (Finset.univ.filter fun j => 0 < W j).card < Z.card :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ <| by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_filter_le (Finset.univ : Finset (Fin (params.domainSize (i.val + 1)))) _) hZ_gt
  exact not_lt_of_ge (hno_corr v hv_rs) <| weighted_agree_of_curve_many
    (show 1 ≤ params.arity i from le_trans (by omega) (params.two_le_arity i))
    W u v Z _ hZ_filt hgood_curve

/-- **Conditional step (uniform smooth unique-decoding weighted upgrade)**: inside the
unique-decoding regime `2 * e + params.dim 0 ≤ 2 ^ d`, assuming `UniqueCurveGapHypothesis params e`
yields uniform `WeightedCurveGapBound` with round-`0` budget `2 ^ d - 2 ^ (d - firstStepLog)` via
`FRISmoothParams.arity_sub_one_mul_domainSize_le_first`. -/
theorem weightedCurveGapBound_of_uniqueCurveGap [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    (hgap : UniqueCurveGapHypothesis params e) :
    WeightedCurveGapBound params (2 ^ params.d - e - 1)
      (2 ^ params.d - 2 ^ (params.d - params.firstStepLog)) :=
  (weightedCurveGapPerRound_of_uniqueCurveGap params huniq hgap).mono
    params.arity_sub_one_mul_domainSize_le_first

end SmoothUniqueDecodingUpgrade

end Cslib.Crypto.Protocols.FRI
