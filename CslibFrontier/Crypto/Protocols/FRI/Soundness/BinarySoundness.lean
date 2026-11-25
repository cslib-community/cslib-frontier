/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.Soundness.BinaryBridge
public import CslibFrontier.Crypto.Protocols.FRI.Soundness.SmoothInteractive

/-!
# Binary 2-to-1 FRI Round-by-Round Soundness, Escape Bounds, and Interactive Game Corollaries

Derives unconditional round-by-round soundness (`friIOP_rbrSound`), query-round escape, conditional
commit-round escape, summed interactive IOP soundness, and parameter scaling identities for binary
2-to-1 `FRIParams` as corollaries of the smooth `FRISmoothParams` theorems via `params.toSmooth`.
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Cslib.Code
open Cslib.OracleComp
open Cslib.Crypto.Protocols.BCS
open Cslib.Probability

section BinarySoundnessCorollaries

variable {F : Type} [Field F]

private theorem setOf_not_friGoodStep_eq [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (π : OracleTable params.d F) :
    {c | ¬ friGoodStep params B stmt pref π c} =
      {c | ¬ friSmoothGoodStep params.toSmooth B stmt pref π c} := by
  ext c
  simp only [Set.mem_ofPred_eq, friGoodStep_iff_friSmoothGoodStep]

/-- **Unconditional round-by-round soundness invariant for binary `friIOP`** (corollary of
`friSmoothIOP_rbrSound`). -/
theorem friIOP_rbrSound [DecidableEq F] (params : FRIParams F) (e : ℕ) :
    IOPRoundByRoundSoundness (friIOP params) (params.proximityLang e)
      (friDoomed params (2 ^ params.d - e - 1))
      (friGoodStep params (2 ^ params.d - e - 1)) where
  init_doomed stmt hnot :=
    (friDoomed_iff_friSmoothDoomed params _ stmt []).mpr
      ((friSmoothIOP_rbrSound params.toSmooth e).init_doomed stmt
        (by simpa only [FRIParams.toSmooth_proximityLang] using hnot))
  step_doomed stmt pref π c hdoomed hgood :=
    (friDoomed_iff_friSmoothDoomed params _ stmt _).mpr
      ((friSmoothIOP_rbrSound params.toSmooth e).step_doomed stmt pref π c
        ((friDoomed_iff_friSmoothDoomed params _ stmt pref).mp hdoomed)
        ((friGoodStep_iff_friSmoothGoodStep params _ stmt pref π c).mp hgood))
  reject_of_doomed stmt oracles chals hdoomed := by
    rw [friIOP_eq_friSmoothIOP]
    exact (friSmoothIOP_rbrSound params.toSmooth e).reject_of_doomed stmt oracles chals
      ((friDoomed_iff_friSmoothDoomed params _ stmt _).mp hdoomed)

/-- When `pref.length = m` and `pref` is doomed at threshold `B`, at most `B` starting points in
`Fin (2 ^ d)` pass `friFinalPasses` against any final oracle `π`. -/
theorem card_filter_friFinalPasses_le_of_friDoomed [DecidableEq F] (params : FRIParams F)
    {B : ℕ} {stmt : OracleTable params.d F}
    {pref : List (OracleTable params.d F × FRIChal F params.d params.q)}
    (hlen : pref.length = params.m) (π : OracleTable params.d F)
    (hdoomed : friDoomed params B stmt pref) :
    (Finset.univ.filter fun s => friFinalPasses params stmt pref π s).card ≤ B := by
  rw [Finset.filter_congr fun s _ => friFinalPasses_iff_friSmoothFinalPasses params stmt pref π s]
  exact card_filter_friSmoothFinalPasses_le_of_friSmoothDoomed params.toSmooth hlen π
    ((friDoomed_iff_friSmoothDoomed params B stmt pref).mp hdoomed)

/-- **Unconditional binary query-round escape bound** (corollary of
`friSmoothQueryRound_escape_le`). -/
theorem friQueryRound_escape_le [Fintype F] [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hlen : pref.length = params.m) (π : OracleTable params.d F)
    (hdoomed : friDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params B stmt pref π c} ≤
      ((B : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  rw [setOf_not_friGoodStep_eq]
  exact friSmoothQueryRound_escape_le params.toSmooth B stmt pref hlen π
    ((friDoomed_iff_friSmoothDoomed params B stmt pref).mp hdoomed)

/-- Every integer per-round bad-scalar bound `WeightedLineGapPerRound params B B_commit` induces a
per-round escape-probability bound `ε_commit i = B_commit i / |F|`. -/
theorem weightedLineEscapePerRound_of_gapPerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {B : ℕ} {B_commit : Fin params.m → ℕ}
    (hgap : WeightedLineGapPerRound params B B_commit) :
    WeightedLineEscapePerRound params B
      (fun i => (B_commit i : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  (weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params B _).mpr
    (weightedCurveEscapePerRound_of_gapPerRound params.toSmooth
      ((weightedLineGapPerRound_iff_weightedCurveGapPerRound params B B_commit).mp hgap))

/-- **Conditional step (binary commit-round escape bound assuming `WeightedLineEscapePerRound`)**
(corollary of `friSmoothCommitRound_escape_le_of_weightedCurveEscapePerRound`). -/
theorem friCommitRound_escape_le_of_weightedLineEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {B : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedLineEscapePerRound params B ε_commit)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (hdoomed : friDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params B stmt pref π c} ≤
      ε_commit ⟨pref.length, hpm⟩ := by
  rw [setOf_not_friGoodStep_eq]
  exact friSmoothCommitRound_escape_le_of_weightedCurveEscapePerRound params.toSmooth
    ((weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params B ε_commit).mp hesc)
    stmt pref hpm π ((friDoomed_iff_friSmoothDoomed params B stmt pref).mp hdoomed)

/-- **Conditional step (binary commit-round escape bound assuming `WeightedLineGapPerRound`)**. -/
theorem friCommitRound_escape_le_of_weightedLineGapPerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {B : ℕ} {B_commit : Fin params.m → ℕ}
    (hgap : WeightedLineGapPerRound params B B_commit)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (hdoomed : friDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params B stmt pref π c} ≤
      (B_commit ⟨pref.length, hpm⟩ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  friCommitRound_escape_le_of_weightedLineEscapePerRound params
    (weightedLineEscapePerRound_of_gapPerRound params hgap) stmt pref hpm π hdoomed

/-- **Conditional step (binary commit-round escape bound assuming `WeightedLineGapBound`)**. -/
theorem friCommitRound_escape_le_of_weightedLineGap [Fintype F] [DecidableEq F]
    (params : FRIParams F) {B B_commit : ℕ}
    (hgap : WeightedLineGapBound params B B_commit)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (hdoomed : friDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params B stmt pref π c} ≤
      (B_commit : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  friCommitRound_escape_le_of_weightedLineGapPerRound params hgap stmt pref hpm π hdoomed

/-- The sum of `friRoundEscape` over all `m + 1` rounds equals `friSumError`. -/
theorem sum_friRoundEscape_eq_friSumError (params : FRIParams F) (e : ℕ)
    (ε_commit : Fin params.m → ℝ≥0∞) :
    (∑ j : Fin (params.m + 1), friRoundEscape params e ε_commit j) =
      friSumError params e ε_commit :=
  sum_friSmoothRoundEscape_eq_friSmoothSumError params.toSmooth e ε_commit

/-- For a uniform commit-round error `B_commit / |F|`, `friSupRBRError` is bounded above by
`friRBRError`. -/
theorem friSupRBRError_const_le_friRBRError [Fintype F] (params : FRIParams F)
    (e B_commit : ℕ) :
    friSupRBRError params e (fun _ => (B_commit : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ≤
      friRBRError params e B_commit :=
  friSmoothSupRBRError_const_le_friSmoothRBRError params.toSmooth e B_commit

/-- **Conditional step (indexed binary per-round escape bound assuming
`WeightedLineEscapePerRound`)**. -/
theorem friPerRoundEscape_of_weightedLineEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedLineEscapePerRound params (2 ^ params.d - e - 1) ε_commit) :
    ∀ stmt ∉ params.proximityLang e, ∀ (j : Fin (params.m + 1)) pref π,
      pref.length = j.val →
      friDoomed params (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params (2 ^ params.d - e - 1) stmt pref π c} ≤
      friRoundEscape params e ε_commit j := by
  intro stmt hfar j pref π hlen hdoomed
  rw [setOf_not_friGoodStep_eq]
  exact friSmoothPerRoundEscape_of_weightedCurveEscapePerRound params.toSmooth
    ((weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params _ ε_commit).mp hesc)
    stmt (by simpa only [FRIParams.toSmooth_proximityLang] using hfar) j pref π hlen
    ((friDoomed_iff_friSmoothDoomed params _ stmt pref).mp hdoomed)

/-- **Conditional step (all-prefix binary `sup` RBR escape bound assuming
`WeightedLineEscapePerRound`)**. -/
theorem friRBREscape_of_weightedLineEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedLineEscapePerRound params (2 ^ params.d - e - 1) ε_commit) :
    ∀ stmt ∉ params.proximityLang e, ∀ pref π,
      friDoomed params (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params (2 ^ params.d - e - 1) stmt pref π c} ≤
      friSupRBRError params e ε_commit := by
  intro stmt hfar pref π hdoomed
  rw [setOf_not_friGoodStep_eq]
  exact friSmoothRBREscape_of_weightedCurveEscapePerRound params.toSmooth
    ((weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params _ ε_commit).mp hesc)
    stmt (by simpa only [FRIParams.toSmooth_proximityLang] using hfar) pref π
    ((friDoomed_iff_friSmoothDoomed params _ stmt pref).mp hdoomed)

/-- **Conditional step (uniform binary round-by-round escape bound assuming
`WeightedLineGapBound`)**. -/
theorem friRBREscape_of_weightedLineGap [Fintype F] [DecidableEq F] (params : FRIParams F)
    {e B_commit : ℕ}
    (hgap : WeightedLineGapBound params (2 ^ params.d - e - 1) B_commit) :
    ∀ stmt ∉ params.proximityLang e, ∀ pref π,
      friDoomed params (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friGoodStep params (2 ^ params.d - e - 1) stmt pref π c} ≤
      friRBRError params e B_commit :=
  fun stmt hfar pref π hdoomed =>
    (friRBREscape_of_weightedLineEscapePerRound params
      (weightedLineEscapePerRound_of_gapPerRound params hgap) stmt hfar pref π hdoomed).trans
      (friSupRBRError_const_le_friRBRError params e B_commit)

/-- **Conditional step (single-word binary FRI commit-phase union bound assuming
`WeightedLineEscapePerRound`)**. -/
theorem friCommitGame_le_of_weightedLineEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedLineEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    friCommitGame params (2 ^ params.d - e - 1) stmt P true ≤ ∑ i : Fin params.m, ε_commit i := by
  rw [friCommitGame_eq_friSmoothCommitGame]
  exact friSmoothCommitGame_le_of_weightedCurveEscapePerRound params.toSmooth
    ((weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params _ ε_commit).mp hesc)
    (by simpa only [FRIParams.toSmooth_proximityLang] using hfar) P

/-- **Conditional step (single-word binary FRI commit-phase union bound assuming
`WeightedLineGapPerRound`)**. -/
theorem friCommitGame_le_of_weightedLineGapPerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} {B_commit : Fin params.m → ℕ}
    (hgap : WeightedLineGapPerRound params (2 ^ params.d - e - 1) B_commit)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    friCommitGame params (2 ^ params.d - e - 1) stmt P true ≤
      ∑ i : Fin params.m, (B_commit i : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  friCommitGame_le_of_weightedLineEscapePerRound params
    (weightedLineEscapePerRound_of_gapPerRound params hgap) hfar P

/-- **Conditional step (summed interactive soundness for single-word `friIOP` assuming
`WeightedLineEscapePerRound`)**. -/
theorem friIOP_interactiveGame_le_of_weightedLineEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedLineEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    iopInteractiveGame (friIOP params) stmt P true ≤ friSumError params e ε_commit := by
  rw [friIOP_eq_friSmoothIOP]
  exact friSmoothIOP_interactiveGame_le_of_weightedCurveEscapePerRound params.toSmooth
    ((weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params _ ε_commit).mp hesc)
    (by simpa only [FRIParams.toSmooth_proximityLang] using hfar) P

/-- **Conditional step (summed interactive soundness for single-word `friIOP` assuming
`WeightedLineGapPerRound`)**. -/
theorem friIOP_interactiveGame_le_of_weightedLineGapPerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} {B_commit : Fin params.m → ℕ}
    (hgap : WeightedLineGapPerRound params (2 ^ params.d - e - 1) B_commit)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    iopInteractiveGame (friIOP params) stmt P true ≤
      friSumError params e (fun i => (B_commit i : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  friIOP_interactiveGame_le_of_weightedLineEscapePerRound params
    (weightedLineEscapePerRound_of_gapPerRound params hgap) hfar P

/-! #### Binary Parameter Helpers & Unique-Decoding Line-Gap Upgrade -/

/-- Fiber-size product identity `2 ^ (i + 1) * 2 ^ (d - (i + 1)) = 2 ^ d` for a folding round
`i : Fin params.m`. -/
theorem FRIParams.fiber_mul_domainSize (params : FRIParams F) (i : Fin params.m) :
    2 ^ (i.val + 1) * 2 ^ (params.d - (i.val + 1)) = 2 ^ params.d := by
  simpa only [params.toSmooth_cumLog i.isLt, params.toSmooth_domainSize i.isLt] using
    params.toSmooth.two_pow_cumLog_mul_domainSize i.isLt

/-- Round-dimension scaling identity `2 ^ (i + 1) * params.dim (i + 1) = params.dim 0` for a
folding round `i : Fin params.m`. -/
theorem FRIParams.fiber_mul_dim (params : FRIParams F) (i : Fin params.m) :
    2 ^ (i.val + 1) * params.dim (i.val + 1) = params.dim 0 := by
  simpa only [params.toSmooth_cumLog i.isLt, params.toSmooth_dim i.isLt,
    params.toSmooth_dim (Nat.zero_le params.m)] using
    params.toSmooth.two_pow_cumLog_mul_dim i.isLt

/-- Every round Reed–Solomon dimension `params.dim r` is at least `1`. -/
theorem FRIParams.one_le_dim (params : FRIParams F) (r : ℕ) : 1 ≤ params.dim r := by
  simp only [FRIParams.dim]
  exact Nat.mul_pos params.hkPos (Nat.pow_pos (by omega))

/-- Each active round dimension fits inside its active coset size (`r ≤ m`). -/
theorem FRIParams.dim_le_domainSize (params : FRIParams F) {r : ℕ} (hr : r ≤ params.m) :
    params.dim r ≤ 2 ^ (params.d - r) := by
  simpa only [params.toSmooth_dim hr, params.toSmooth_domainSize hr] using
    params.toSmooth.dim_le_domainSize hr

/-- Exact geometric sum of active folded coset sizes across all `m` binary FRI folding rounds:
`∑ i : Fin params.m, 2 ^ (params.d - (i.val + 1)) = 2 ^ params.d - 2 ^ (params.d - params.m)`. -/
theorem FRIParams.sum_domainSize_succ (params : FRIParams F) :
    (∑ i : Fin params.m, 2 ^ (params.d - (i.val + 1))) =
      2 ^ params.d - 2 ^ (params.d - params.m) := by
  have h := params.toSmooth.sum_arity_sub_one_mul_domainSize
  rw [params.toSmooth_totalLog] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [FRISmoothParams.arity, pow_one, Nat.reduceSub, one_mul,
    params.toSmooth_domainSize i.isLt]

/-- Transport the initial unique-decoding bound `2 * e + params.dim 0 ≤ 2 ^ params.d` to the
scaled round-`(i + 1)` unique-decoding bound. -/
theorem FRIParams.two_mul_div_add_dim_le (params : FRIParams F) {e : ℕ}
    (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) (i : Fin params.m) :
    2 * (e / 2 ^ (i.val + 1)) + params.dim (i.val + 1) ≤ 2 ^ (params.d - (i.val + 1)) := by
  have huniq' : 2 * e + params.toSmooth.dim 0 ≤ 2 ^ params.toSmooth.d := by
    simpa only [params.toSmooth_dim (Nat.zero_le params.m)] using huniq
  simpa only [params.toSmooth_cumLog i.isLt, params.toSmooth_dim i.isLt,
    params.toSmooth_domainSize i.isLt] using
    params.toSmooth.two_mul_div_add_dim_le huniq' i


end BinarySoundnessCorollaries

end Cslib.Crypto.Protocols.FRI
