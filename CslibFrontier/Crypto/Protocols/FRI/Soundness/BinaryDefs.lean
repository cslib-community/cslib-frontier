/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.Soundness.CurveGap

/-!
# Binary 2-to-1 FRI Transcript State, Round-by-Round Predicates, and Line-Gap Contracts

Defines the binary 2-to-1 `FRIParams` specialization's transcript target words, fiber weights,
acceptance predicates, doomed/good-step predicates, line proximity-gap and escape contracts
(`WeightedLineGapPerRound`, `WeightedLineGapBound`, `WeightedLineEscapePerRound`,
`UniqueLineGapHypothesis`), error abbreviations, and commit-phase game `friCommitGame`.
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Cslib.Code
open Cslib.OracleComp
open Cslib.Crypto.Protocols.BCS
open Cslib.Probability

section BinaryDefs

variable {F : Type} [Field F]

/-- Expected round-`i` word along a binary transcript prefix `pref`: `stmt` at round `0`, and the
2-to-1 coset folding of `prefOracle pref i` at `prefFoldScalar pref i` for round `i + 1`. -/
@[expose] def friTargetWord (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    (i : ℕ) → i ≤ params.m → Fin (2 ^ (params.d - i)) → F
  | 0, _ => restrictOracle (i := 0) stmt
  | i + 1, hi =>
    have hjd : i < params.d := lt_of_lt_of_le (Nat.lt_of_succ_le hi) params.hm
    fold2 (params.g ^ (2 ^ i)) (params.ω ^ (2 ^ i))
      (fun idx : Fin (2 * 2 ^ (params.d - (i + 1))) =>
        restrictOracle (i := i) (prefOracle pref i) (reindexDouble hjd idx))
      (prefFoldScalar pref i)

/-- Pre-filter integer fiber weight `W̃_i : Fin (2 ^ (d - i)) → ℕ` along a binary transcript prefix
`pref`, prior to applying the round-`i` oracle consistency check `π_i = friTargetWord ... i`. -/
@[expose] def friPreWeight [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    (i : ℕ) → i ≤ params.m → Fin (2 ^ (params.d - i)) → ℕ
  | 0, _ => fun _ => 1
  | i + 1, hi =>
    have hjd : i < params.d := lt_of_lt_of_le (Nat.lt_of_succ_le hi) params.hm
    let prevTarget := friTargetWord params stmt pref i (Nat.le_of_succ_le hi)
    let prevWeight := friPreWeight params stmt pref i (Nat.le_of_succ_le hi)
    let prevOracle := restrictOracle (i := i) (prefOracle pref i)
    let filt : Fin (2 ^ (params.d - i)) → ℕ :=
      fun y => if prevOracle y = prevTarget y then prevWeight y else 0
    fun j =>
      filt (reindexDouble hjd ⟨j.val, by omega⟩) +
        filt (reindexDouble hjd ⟨j.val + 2 ^ (params.d - (i + 1)), by omega⟩)

/-- Filtered round-`i` weight for an explicit prover oracle `π` in binary FRI. -/
@[expose] def friOracleFilterWeight [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (π : OracleTable params.d F)
    (j : Fin (2 ^ (params.d - i))) : ℕ :=
  if restrictOracle (i := i) π j = friTargetWord params stmt pref i hi j then
    friPreWeight params stmt pref i hi j
  else 0

/-- Pushed round-`(i + 1)` weight induced by an explicit prover oracle `π` at round `i` in binary
FRI. -/
@[expose] def friNextWeight [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i < params.m) (π : OracleTable params.d F)
    (j : Fin (2 ^ (params.d - (i + 1)))) : ℕ :=
  have hjd : i < params.d := lt_of_lt_of_le hi params.hm
  friOracleFilterWeight params stmt pref i hi.le π (reindexDouble hjd ⟨j.val, by omega⟩) +
    friOracleFilterWeight params stmt pref i hi.le π
      (reindexDouble hjd ⟨j.val + 2 ^ (params.d - (i + 1)), by omega⟩)

/-- Prefix acceptance predicate for a starting index `s : Fin (2 ^ d)` through folding rounds
`0, ..., i - 1` along a binary transcript `pref`. -/
@[expose] def friPrefixPasses (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (s : Fin (2 ^ params.d)) : Prop :=
  prefOracle pref 0 s = stmt s ∧
  ∀ k : Fin params.m, k.val < i →
    fold2Fiber
      (prefOracle pref k.val (friRoundPosIdx params k s))
      (prefOracle pref k.val (friRoundNegIdx params k s))
      (params.eval k.val (friRoundPosFin params k s))
      (prefFoldScalar pref k.val) =
    prefOracle pref (k.val + 1) (friRoundPosIdx params k s)

/-- Full single-query acceptance predicate evaluated on a binary transcript list `pref` at starting
index `s : Fin (2 ^ d)`. -/
@[expose] def friTranscriptSingleAccepts (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (s : Fin (2 ^ params.d)) : Prop :=
  friPrefixPasses params stmt pref params.m s ∧
    prefOracle pref params.m (friFinalIdx params s) =
      friFinalCodeword params (prefOracle pref params.m) (friFinalFin params s)

/-- Final-round acceptance predicate for a length-`m` binary prefix `pref` and final oracle
`πFinal`. -/
@[expose] def friFinalPasses (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (πFinal : OracleTable params.d F) (s : Fin (2 ^ params.d)) : Prop :=
  (if params.m = 0 then πFinal s else prefOracle pref 0 s) = stmt s ∧
  (∀ k : Fin params.m,
    fold2Fiber
      (prefOracle pref k.val (friRoundPosIdx params k s))
      (prefOracle pref k.val (friRoundNegIdx params k s))
      (params.eval k.val (friRoundPosFin params k s))
      (prefFoldScalar pref k.val) =
    (if k.val + 1 = params.m then πFinal else prefOracle pref (k.val + 1))
      (friRoundPosIdx params k s)) ∧
  πFinal (friFinalIdx params s) = friFinalCodeword params πFinal (friFinalFin params s)

/-- Decidability of the binary prefix-acceptance predicate `friPrefixPasses`. -/
instance instDecidableFriPrefixPasses [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (s : Fin (2 ^ params.d)) :
    Decidable (friPrefixPasses params stmt pref i s) := by
  unfold friPrefixPasses
  infer_instance

/-- Decidability of the final-round binary acceptance predicate `friFinalPasses`. -/
instance instDecidableFriFinalPasses [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (πFinal : OracleTable params.d F) (s : Fin (2 ^ params.d)) :
    Decidable (friFinalPasses params stmt pref πFinal s) := by
  unfold friFinalPasses
  infer_instance

/-- Binary commit-round doomed predicate at round `i ≤ m`. -/
@[expose] def friCommitDoomed [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) : Prop :=
  ∀ c ∈ params.rsCode i,
    (∑ j ∈ Finset.univ.filter (fun j => friTargetWord params stmt pref i hi j = c j),
      friPreWeight params stmt pref i hi j) ≤ B

/-- **Binary FRI round-by-round doomed-state predicate**. -/
@[expose] def friDoomed [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) : Prop :=
  if h : pref.length ≤ params.m then
    friCommitDoomed params B stmt pref pref.length h
  else if pref.length = params.m + 1 then
    ∃ a : Fin params.q,
      ¬ friTranscriptSingleAccepts params stmt pref (prefFinalQueryIdxs params pref a)
  else
    True

/-- **Binary FRI round-by-round good-step predicate**. -/
@[expose] def friGoodStep [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (π : OracleTable params.d F) (c : FRIChal F params.d params.q) : Prop :=
  if pref.length ≤ params.m then
    friDoomed params B stmt (pref ++ [(π, c)])
  else
    True

/-- **Polymorphic per-round weighted line proximity-gap contract** across all `m` binary FRI
folding rounds at agreement threshold `B` and per-round exceptional-scalar budgets
`B_commit : Fin params.m → ℕ`. -/
@[expose] def WeightedLineGapPerRound [DecidableEq F] (params : FRIParams F)
    (B : ℕ) (B_commit : Fin params.m → ℕ) : Prop :=
  ∀ (i : Fin params.m) (W : Fin (2 ^ (params.d - (i.val + 1))) → ℕ),
    (∀ j, W j ≤ 2 ^ (i.val + 1)) →
    (∑ j, W j ≤ 2 ^ params.d) →
    ∀ (u₀ u₁ : Fin (2 ^ (params.d - (i.val + 1))) → F),
      (∀ v₀ ∈ params.rsCode (i.val + 1), ∀ v₁ ∈ params.rsCode (i.val + 1),
        (∑ j ∈ Finset.univ.filter (fun j => u₀ j = v₀ j ∧ u₁ j = v₁ j), W j) ≤ B) →
      ∀ Z : Finset F,
        (∀ z ∈ Z, ∃ v ∈ params.rsCode (i.val + 1),
          B < ∑ j ∈ Finset.univ.filter (fun j => (u₀ + z • u₁) j = v j), W j) →
        Z.card ≤ B_commit i

/-- Pointwise monotonicity of `WeightedLineGapPerRound` in the per-round scalar budget. -/
theorem WeightedLineGapPerRound.mono [DecidableEq F] {params : FRIParams F} {B : ℕ}
    {B₁ B₂ : Fin params.m → ℕ} (hgap : WeightedLineGapPerRound params B B₁)
    (hle : ∀ i : Fin params.m, B₁ i ≤ B₂ i) :
    WeightedLineGapPerRound params B B₂ :=
  fun i W hW_le hW_sum u₀ u₁ hno Z hZ =>
    (hgap i W hW_le hW_sum u₀ u₁ hno Z hZ).trans (hle i)

/-- **Polymorphic uniform weighted line proximity-gap contract** for all `m` binary FRI folding
rounds at agreement threshold `B` and uniform bad-scalar budget `B_commit`. -/
@[expose] def WeightedLineGapBound [DecidableEq F] (params : FRIParams F)
    (B B_commit : ℕ) : Prop :=
  WeightedLineGapPerRound params B (fun _ => B_commit)

/-- **Polymorphic per-round weighted line escape-probability contract** across all `m` binary FRI
folding rounds at agreement threshold `B` and per-round escape probability budgets
`ε_commit : Fin params.m → ℝ≥0∞`. -/
@[expose] def WeightedLineEscapePerRound [Fintype F] [DecidableEq F] (params : FRIParams F)
    (B : ℕ) (ε_commit : Fin params.m → ℝ≥0∞) : Prop :=
  ∀ (i : Fin params.m) (W : Fin (2 ^ (params.d - (i.val + 1))) → ℕ),
    (∀ j, W j ≤ 2 ^ (i.val + 1)) →
    (∑ j, W j ≤ 2 ^ params.d) →
    ∀ (u₀ u₁ : Fin (2 ^ (params.d - (i.val + 1))) → F),
      (∀ v₀ ∈ params.rsCode (i.val + 1), ∀ v₁ ∈ params.rsCode (i.val + 1),
        (∑ j ∈ Finset.univ.filter (fun j => u₀ j = v₀ j ∧ u₁ j = v₁ j), W j) ≤ B) →
      (PMF.uniformOfFintype F).toOuterMeasure
        {z : F | ∃ v ∈ params.rsCode (i.val + 1),
          B < ∑ j ∈ Finset.univ.filter (fun j => (u₀ + z • u₁) j = v j), W j} ≤
        ε_commit i

/-- Pointwise monotonicity of `WeightedLineEscapePerRound` in the per-round escape budget. -/
theorem WeightedLineEscapePerRound.mono [Fintype F] [DecidableEq F] {params : FRIParams F}
    {B : ℕ} {ε₁ ε₂ : Fin params.m → ℝ≥0∞} (hesc : WeightedLineEscapePerRound params B ε₁)
    (hle : ∀ i : Fin params.m, ε₁ i ≤ ε₂ i) :
    WeightedLineEscapePerRound params B ε₂ :=
  fun i W hW_le hW_sum u₀ u₁ hno => (hesc i W hW_le hW_sum u₀ u₁ hno).trans (hle i)

/-- Per-round escape budget vector for single-word `(m + 1)`-round `friIOP`. -/
noncomputable abbrev friRoundEscape (params : FRIParams F) (e : ℕ)
    (ε_commit : Fin params.m → ℝ≥0∞) (j : Fin (params.m + 1)) : ℝ≥0∞ :=
  friSmoothRoundEscape params.toSmooth e ε_commit j

/-- Summed interactive binary FRI soundness error
`(∑ i : Fin m, ε_commit i) + ((2 ^ d - e - 1) / 2 ^ d) ^ q`. -/
noncomputable abbrev friSumError (params : FRIParams F) (e : ℕ)
    (ε_commit : Fin params.m → ℝ≥0∞) : ℝ≥0∞ :=
  friSmoothSumError params.toSmooth e ε_commit

/-- Uniform per-round escape error `sup_j (friRoundEscape params e ε_commit j)`. -/
noncomputable abbrev friSupRBRError (params : FRIParams F) (e : ℕ)
    (ε_commit : Fin params.m → ℝ≥0∞) : ℝ≥0∞ :=
  friSmoothSupRBRError params.toSmooth e ε_commit

/-- Uniform per-round escape error for binary FRI. -/
noncomputable abbrev friRBRError [Fintype F] (params : FRIParams F)
    (e B_commit : ℕ) : ℝ≥0∞ :=
  friSmoothRBRError params.toSmooth e B_commit

/-- Single-word binary FRI commit-phase game. -/
@[expose] noncomputable def friCommitGame [Fintype F] (params : FRIParams F)
    (B : ℕ) (stmt : OracleTable params.d F)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) : PMF Bool :=
  (iopRunRounds P params.m []).bind fun pref =>
    (P pref).map fun πFinal =>
      letI : DecidablePred (fun s => friFinalPasses params stmt pref πFinal s) :=
        Classical.decPred _
      decide (B < (Finset.univ.filter fun s => friFinalPasses params stmt pref πFinal s).card)

/-- Unweighted line proximity-gap hypothesis across all `m` binary FRI folding rounds at
unique-decoding radii `e / 2 ^ (i + 1)` (matching [BenSassonCarmonIshaiKoppartySaraf2020,
Theorem 4.1]). -/
@[expose] def UniqueLineGapHypothesis [DecidableEq F] (params : FRIParams F) (e : ℕ) : Prop :=
  ∀ (i : Fin params.m) (u₀ u₁ : Fin (2 ^ (params.d - (i.val + 1))) → F) (Z : Finset F),
    2 ^ (params.d - (i.val + 1)) < Z.card →
    (∀ z ∈ Z, ∃ v ∈ params.rsCode (i.val + 1),
      hammingDist (u₀ + z • u₁) v ≤ e / 2 ^ (i.val + 1)) →
    ∃ D' : Finset (Fin (2 ^ (params.d - (i.val + 1)))),
      ∃ v₀ ∈ params.rsCode (i.val + 1), ∃ v₁ ∈ params.rsCode (i.val + 1),
        2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1) ≤ D'.card ∧
        ∀ j ∈ D', u₀ j = v₀ j ∧ u₁ j = v₁ j

end BinaryDefs

end Cslib.Crypto.Protocols.FRI
