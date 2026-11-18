/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.BatchProtocol
public import CslibFrontier.Crypto.Protocols.FRI.Soundness
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve
import CslibFrontier.Foundations.Data.Code.ProximityGap.Unique
import CslibFrontier.Foundations.Data.Hamming
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Batched FRI Round-0 Soundness, Affine Correlated Agreement, and BCS Composition

This module proves unconditional round-by-round soundness
(`Cslib.Crypto.Protocols.BCS.IOPRoundByRoundSoundness` — initialization on false tuples,
preservation on good transitions, and terminal rejection), marginal challenge projections, and
unconditional round-`0` unweighted affine-word escape upper bounds for the `(params.m + 2)`-round
batched FRI IOP `Cslib.Crypto.Protocols.FRI.friBatchIOP`
([BenSassonCarmonIshaiKoppartySaraf2020], accepted *Journal of the ACM* 2023 manuscript,
Section 8.2 on printed pp. 36–40 and Section 8.2.1 on printed pp. 41–43), together with conditional
whole-protocol uniform escape and two-channel BCS random-oracle composition steps
([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]).

## Summary of the round-by-round invariant and round-0 probability bounds

1. **Round-by-round invariant (`friBatchDoomed`, `friBatchGoodStep`, `friBatchIOP_rbrSound`).**
   `friBatchIOP_rbrSound` establishes initialization on any false tuple
   `stmt ∉ params.batchProximityLang t e` (`init_doomed`), preservation of `friBatchDoomed` on good
   round transitions (`step_doomed`), and terminal verifier rejection (`iopVerify = false`) of any
   complete doomed transcript (`reject_of_doomed`). In this Lean ordering, the uniform round-`0`
   batching challenge `x = c₀.batchCoeffs : Fin t → F` selects the affine word `stmt.eval x` first,
   and an adaptive prover can choose its next oracle (`f⁽⁰⁾`, round `1`) after seeing `c₀`. After
   round `0` (`(_, c₀) :: rest`), `friBatchDoomed` delegates to single-word `friDoomed` on
   `stmt.eval c₀.batchCoeffs` and `friBatchTailTranscript rest`, absorbing any discrepancy between
   the reported oracle `f⁽⁰⁾` and `stmt.eval x` via `sum_agree_friOracleFilterWeight_le`.
2. **Marginal challenge projections and 1-line tail reuse.**
   Via `FRIBatchChal.equivProd`, uniform sampling on `FRIBatchChal F d q t` projects to uniform
   `Fin t → F` under `batchCoeffs` (`toOuterMeasure_uniform_friBatchChal_batchCoeffs`) and to
   uniform `FRIChal F d q` under `toFRIChal` (`toOuterMeasure_uniform_friBatchChal_toFRIChal`),
   reducing every non-empty prefix escape probability (`toOuterMeasure_not_friBatchGoodStep_cons`),
   query-round escape (`friBatchQueryRound_escape_le`), and folding-round escape
   (`friBatchCommitRound_escape_le_of_weightedLineGap`) directly to
   `CslibFrontier/Crypto/Protocols/FRI/Soundness.lean` with zero duplicated folding or query proofs.
3. **Round-0 probability upper bounds from affine correlated agreement, and whole-protocol steps.**
   The unique-decoding (`batchRound0GapBound_of_unique`, `batchRound0Escape_of_unique`), discrete
   Johnson (`batchRound0GapBound_of_johnson_discrete`, `batchRound0Escape_of_johnson_discrete`), and
   closed-form Johnson / `η`-gap (`batchRound0GapBound_of_johnson`, `batchRound0Escape_of_johnson`,
   `batchRound0Escape_of_johnson_eta`) results supply round-`0` probability upper bounds (with exact
   denominator `|F|` and no list-size premise) on the chance that the affine word `stmt.eval x` is
   within Hamming distance `e` of `params.initialCode` for a false tuple under their respective
   parameter conditions. At batch size `t = 0`, the false word `stmt.eval x = stmt.base` is
   independent of the challenge and its actual round-`0` escape probability is `0` (while the
   `t`-uniform theorems still supply valid upper bounds). Whole-protocol bounds in Section 4
   (`friBatchRBREscape_of_escape`, `friBatchBCS_romSoundness_bound_of_escape`,
   `friBatchBCS_romSoundness_bound_of_prover_verifier_of_escape`) still require escape estimates
   (`WeightedLineGapBound`) for the remaining `m` folding rounds alongside the query-round bound.

## Scope and relationship to the source theorems

* **Round-`0` event vs. Section 8.2.1 Eq. (8.8) (printed pp. 41–42):** In
  [BenSassonCarmonIshaiKoppartySaraf2020], Section 8.2.1 defines the round-`0` bad event `E⁽⁰⁾`
  using `μ⁽⁰⁾`-**weighted agreement of the reported oracle** `f⁽⁰⁾`, where `μ⁽⁰⁾(s) = 1` only where
  `f⁽⁰⁾(s)` matches the affine evaluation `stmt.eval x s` and `0` otherwise. High weighted agreement
  of `f⁽⁰⁾` therefore implies high unweighted agreement of the affine word `stmt.eval x`, whereas a
  prover that reports a value different from `stmt.eval x` everywhere makes `μ⁽⁰⁾ ≡ 0` and shows why
  the reverse implication can fail. The cutoffs differ as well: for `n = 2 ^ d` and
  `B = n - e - 1`, Lean's round-`0` event (`BatchRound0GapBound`, `BatchRound0Escape`,
  `¬ friBatchGoodStep ... [] π c`) tests unweighted agreement strictly above `B / n`, whereas the
  paper's `E⁽⁰⁾` uses the cutoff `max(α, √ρ · (1 + 1 / (2 * m)))` (for example, with
  `n = 16, k = 4, e = 7, α = 1 / 2, m = 3`, Lean's cutoff `8 / 16` admits nine agreeing positions
  while the paper's cutoff `7 / 12` starts at ten). Consequently, for a tuple with common agreement
  at most `B / n` (`stmt ∉ params.batchProximityLang t e`), **the Lean round-`0` event contains the
  paper's event `E⁽⁰⁾` whenever the paper's cutoff `max(α, √ρ · (1 + 1 / (2 * m)))` is at least
  `B / n`**.
* **Explicit Siegel constants and direct `η`:** The closed-form round-`0` upper bounds
  (`friBatchJohnsonRound0Bound`, `1800 * (mJ + 1) ^ 6 * (2 ^ d) ^ 2 / (ρ * |F|)`, and
  `115200 * (2 ^ d) ^ 2 / (ρ * η ^ 6 * |F|)`) are this library's original explicit Siegel finite
  bounds from `CslibFrontier/Foundations/Data/Code/ProximityGap/Curve.lean`, not the paper's
  displayed `(m + 1 / 2) ^ 7 / (3 * ρ ^ (3 / 2))` expression (not uniformly smaller at small `mJ`,
  and Eq. (1.3) uses `min(η, √ρ / 20)` whereas `batchRound0Escape_of_johnson_eta` uses `η`
  directly).
* **Whole-protocol summed IOP soundness:** Full summed interactive batched FRI soundness (in the
  setting of JACM Lemma 8.2 on pp. 38–39, proved via the commit-phase bad-event sum in
  Section 8.2.1 on pp. 41–43, and Theorem 8.3 on p. 39, proved from Lemma 8.2 on p. 40) and
  unconditional closed-form batched FRI / BCS ROM instantiations remain tracked in `#5968`.

## Main definitions

* `Cslib.Crypto.Protocols.FRI.friBatchTailTranscript`,
  `Cslib.Crypto.Protocols.FRI.friBatchDoomed`,
  `Cslib.Crypto.Protocols.FRI.friBatchGoodStep`: transcript-tail projection and round-by-round
  doomed / good-step predicates for `friBatchIOP`.
* `Cslib.Crypto.Protocols.FRI.BatchRound0GapBound`,
  `Cslib.Crypto.Protocols.FRI.BatchRound0Escape`,
  `Cslib.Crypto.Protocols.FRI.friBatchJohnsonRound0Bound`: integer and `ℝ≥0∞` round-`0` unweighted
  affine-word escape contracts and explicit-constant Johnson round-`0` budget.
* `Cslib.Crypto.Protocols.FRI.friBatchRBRError`: uniform per-round escape error combining round-`0`
  batching escape `ε_batch` with `friRBRError`.

## Main results

* `Cslib.Crypto.Protocols.FRI.friBatchIOP_rbrSound`: unconditional `IOPRoundByRoundSoundness`
  (initialization, preservation on good transitions, and terminal rejection) for
  `friBatchIOP params t` with respect to `params.batchProximityLang t e`.
* `Cslib.Crypto.Protocols.FRI.uniformOfFintype_friBatchChal_map_batchCoeffs`,
  `Cslib.Crypto.Protocols.FRI.uniformOfFintype_friBatchChal_map_toFRIChal`,
  `Cslib.Crypto.Protocols.FRI.toOuterMeasure_uniform_friBatchChal_batchCoeffs`,
  `Cslib.Crypto.Protocols.FRI.toOuterMeasure_uniform_friBatchChal_toFRIChal`,
  `Cslib.Crypto.Protocols.FRI.toOuterMeasure_not_friBatchGoodStep_cons`,
  `Cslib.Crypto.Protocols.FRI.friBatchQueryRound_escape_le`,
  `Cslib.Crypto.Protocols.FRI.friBatchCommitRound_escape_le_of_weightedLineGap`: marginal challenge
  laws and 1-line tail escape reductions.
* `Cslib.Crypto.Protocols.FRI.batchRound0Escape_of_gapBound`,
  `Cslib.Crypto.Protocols.FRI.friBatchRound0_escape_le_of_escape`: integer-to-`ℝ≥0∞` round-`0`
  budget lift and conditional round-`0` escape step from `BatchRound0Escape`.
* `Cslib.Crypto.Protocols.FRI.batchRound0GapBound_of_unique`,
  `Cslib.Crypto.Protocols.FRI.batchRound0Escape_of_unique`,
  `Cslib.Crypto.Protocols.FRI.batchRound0GapBound_of_johnson_discrete`,
  `Cslib.Crypto.Protocols.FRI.batchRound0Escape_of_johnson_discrete`,
  `Cslib.Crypto.Protocols.FRI.batchRound0GapBound_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.batchRound0Escape_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.batchRound0Escape_of_johnson_eta`: unconditional round-`0` batching
  discharges across the unique-decoding, discrete Johnson, closed-form Johnson, and `η`-gap
  regimes.
* `Cslib.Crypto.Protocols.FRI.friBatchRBREscape_of_escape`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_romSoundness_bound_of_escape`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_romSoundness_bound_of_prover_verifier_of_escape`:
  conditional uniform per-round escape and adaptive two-channel BCS ROM composition steps.

## References

* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, *Proximity Gaps for Reed–Solomon
  Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
* [E. Ben-Sasson, I. Bentov, Y. Horesh, M. Riabzev, *Fast Reed–Solomon Interactive Oracle Proofs
  of Proximity*][BenSassonBentovHoreshRiabzev2018]
* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024]
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Finset Cslib.Code Cslib.OracleComp Cslib.Crypto.Protocols.BCS Cslib.Probability

/-! ### Section 1: Batched Round-by-Round Invariant Factored Through `friDoomed` -/

section RoundByRoundInvariant

variable {F : Type} [Field F]

/-- Project a batched FRI transcript tail to the corresponding single-word `friIOP` transcript tail
by applying `FRIBatchChal.toFRIChal` to each round challenge. -/
@[expose] def friBatchTailTranscript {d q t : ℕ}
    (rest : List (OracleTable d F × FRIBatchChal F d q t)) :
    List (OracleTable d F × FRIChal F d q) :=
  rest.map fun (π, c) => (π, c.toFRIChal)

omit [Field F] in
@[simp]
theorem friBatchTailTranscript_nil {d q t : ℕ} :
    friBatchTailTranscript ([] : List (OracleTable d F × FRIBatchChal F d q t)) = [] :=
  rfl

omit [Field F] in
@[simp]
theorem friBatchTailTranscript_cons {d q t : ℕ}
    (π : OracleTable d F) (c : FRIBatchChal F d q t)
    (rest : List (OracleTable d F × FRIBatchChal F d q t)) :
    friBatchTailTranscript ((π, c) :: rest) = (π, c.toFRIChal) :: friBatchTailTranscript rest :=
  rfl

omit [Field F] in
@[simp]
theorem friBatchTailTranscript_append {d q t : ℕ}
    (rest₁ rest₂ : List (OracleTable d F × FRIBatchChal F d q t)) :
    friBatchTailTranscript (rest₁ ++ rest₂) =
      friBatchTailTranscript rest₁ ++ friBatchTailTranscript rest₂ :=
  List.map_append

omit [Field F] in
@[simp]
theorem length_friBatchTailTranscript {d q t : ℕ}
    (rest : List (OracleTable d F × FRIBatchChal F d q t)) :
    (friBatchTailTranscript rest).length = rest.length :=
  List.length_map _

/-- **Batched FRI round-by-round doomed-state predicate** at agreement upper bound `B : ℕ`:
* On the empty prefix `[]` (prior to sampling the round-`0` batching vector), every shared
  agreement set `D' ⊆ Fin (2 ^ d)` on which `(stmt.base, stmt.terms)` matches codewords in
  `params.initialCode` has cardinality at most `B`.
* On any non-empty prefix `(_, c₀) :: rest`, delegates directly to single-word `friDoomed` on the
  affine evaluation `stmt.eval c₀.batchCoeffs` and projected tail `friBatchTailTranscript rest`. -/
@[expose] def friBatchDoomed [DecidableEq F] (params : FRIParams F) (t B : ℕ)
    (stmt : FRIBatchStmt F params.d t) :
    List (OracleTable params.d F × FRIBatchChal F params.d params.q t) → Prop
  | [] =>
    ∀ (D' : Finset (Fin (2 ^ params.d))) (v₀ : OracleTable params.d F),
      v₀ ∈ params.initialCode →
      ∀ v : Fin t → OracleTable params.d F,
        (∀ j, v j ∈ params.initialCode) →
        (∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s) →
        D'.card ≤ B
  | (_, c₀) :: rest =>
    friDoomed params B (stmt.eval c₀.batchCoeffs) (friBatchTailTranscript rest)

/-- For `e < 2 ^ d`, the empty prefix is doomed at `B = 2 ^ d - e - 1` if and only if
`stmt ∉ params.batchProximityLang t e`. -/
theorem friBatchDoomed_nil_iff_not_mem_batchProximityLang [DecidableEq F] (params : FRIParams F)
    (t : ℕ) (stmt : FRIBatchStmt F params.d t) {e : ℕ} (he : e < 2 ^ params.d) :
    friBatchDoomed params t (2 ^ params.d - e - 1) stmt [] ↔
      stmt ∉ params.batchProximityLang t e := by
  simp only [friBatchDoomed, FRIParams.batchProximityLang, Set.mem_ofPred_eq]
  constructor
  · rintro hdoom ⟨D', hge, v₀, hv₀, v, hv, hagree⟩
    have hle := hdoom D' v₀ hv₀ v hv hagree
    omega
  · intro hnot D' v₀ hv₀ v hv hagree
    by_contra hgt
    exact hnot ⟨D', by omega, v₀, hv₀, v, hv, hagree⟩

/-- **Batched FRI round-by-round good-step predicate**: for active rounds
`pref.length ≤ params.m + 1`, extending `pref` by `(π, c)` preserves `friBatchDoomed`; for
unreachable lengths `params.m + 2 ≤ pref.length`, holds trivially (`True`) so the escape event
`{c | ¬ friBatchGoodStep ... c}` is empty. -/
@[expose] def friBatchGoodStep [DecidableEq F] (params : FRIParams F) (t B : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (pref : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    (π : OracleTable params.d F) (c : FRIBatchChal F params.d params.q t) : Prop :=
  if pref.length ≤ params.m + 1 then
    friBatchDoomed params t B stmt (pref ++ [(π, c)])
  else
    True

/-- On the empty prefix `[]`, `friBatchGoodStep` holds at challenge `c` if and only if no codeword
`c' ∈ params.initialCode` agrees with `stmt.eval c.batchCoeffs` on more than `B` coordinates. -/
theorem friBatchGoodStep_nil_iff [DecidableEq F] (params : FRIParams F) (t B : ℕ)
    (stmt : FRIBatchStmt F params.d t) (π : OracleTable params.d F)
    (c : FRIBatchChal F params.d params.q t) :
    friBatchGoodStep params t B stmt [] π c ↔
      ∀ c' ∈ params.initialCode,
        (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
          stmt.eval c.batchCoeffs s = c' s).card ≤ B := by
  simp only [friBatchGoodStep, List.length_nil, Nat.zero_le, ↓reduceIte, List.nil_append,
    friBatchDoomed, friBatchTailTranscript_nil, friDoomed, ↓reduceDIte, friCommitDoomed,
    friTargetWord, friPreWeight, restrictOracle, Nat.sub_zero, Fin.eta, Finset.sum_const,
    smul_eq_mul, mul_one, FRIParams.initialCode]
  rfl

/-- On any non-empty prefix `(π₀, c₀) :: rest`, `friBatchGoodStep` reduces unconditionally to
single-word `friGoodStep` on `stmt.eval c₀.batchCoeffs` and `friBatchTailTranscript rest`. -/
@[simp]
theorem friBatchGoodStep_cons [DecidableEq F] (params : FRIParams F) (t B : ℕ)
    (stmt : FRIBatchStmt F params.d t) (π₀ : OracleTable params.d F)
    (c₀ : FRIBatchChal F params.d params.q t)
    (rest : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    (π : OracleTable params.d F) (c : FRIBatchChal F params.d params.q t) :
    friBatchGoodStep params t B stmt ((π₀, c₀) :: rest) π c ↔
      friGoodStep params B (stmt.eval c₀.batchCoeffs)
        (friBatchTailTranscript rest) π c.toFRIChal := by
  by_cases hlen : rest.length ≤ params.m
  · have hcons : ((π₀, c₀) :: rest).length ≤ params.m + 1 := by
      simp only [List.length_cons]
      omega
    have htail : (friBatchTailTranscript rest).length ≤ params.m := by
      rwa [length_friBatchTailTranscript]
    simp only [friBatchGoodStep, hcons, ↓reduceIte, List.cons_append, friBatchDoomed,
      friBatchTailTranscript_append, friBatchTailTranscript_cons, friBatchTailTranscript_nil,
      friGoodStep, htail]
  · have hcons : ¬ ((π₀, c₀) :: rest).length ≤ params.m + 1 := by
      simp only [List.length_cons]
      omega
    have htail : ¬ (friBatchTailTranscript rest).length ≤ params.m := by
      rwa [length_friBatchTailTranscript]
    simp only [friBatchGoodStep, hcons, ↓reduceIte, friGoodStep, htail]

/-- **Unconditional round-by-round soundness invariant for `friBatchIOP`**: for every batch size
`t : ℕ` and distance threshold `e : ℕ`, `friBatchIOP params t` satisfies `IOPRoundByRoundSoundness`
with respect to `params.batchProximityLang t e`, `friBatchDoomed params t (2 ^ params.d - e - 1)`,
and `friBatchGoodStep params t (2 ^ params.d - e - 1)`. -/
theorem friBatchIOP_rbrSound [DecidableEq F] (params : FRIParams F) (t e : ℕ) :
    IOPRoundByRoundSoundness (friBatchIOP params t) (params.batchProximityLang t e)
      (friBatchDoomed params t (2 ^ params.d - e - 1))
      (friBatchGoodStep params t (2 ^ params.d - e - 1)) where
  init_doomed stmt hnot :=
    (friBatchDoomed_nil_iff_not_mem_batchProximityLang params t stmt
      (params.lt_two_pow_of_not_mem_batchProximityLang hnot)).mpr hnot
  step_doomed stmt pref π c _ hgood := by
    by_cases h : pref.length ≤ params.m + 1
    · simpa only [friBatchGoodStep, h, ↓reduceIte] using hgood
    · cases pref with
      | nil => exact absurd (Nat.zero_le _) h
      | cons head rest =>
        simp only [List.length_cons] at h
        have hgt : ¬ (friBatchTailTranscript (rest ++ [(π, c)])).length ≤ params.m := by
          simp only [length_friBatchTailTranscript, List.length_append, List.length_singleton]
          omega
        have hne : (friBatchTailTranscript (rest ++ [(π, c)])).length ≠ params.m + 1 := by
          simp only [length_friBatchTailTranscript, List.length_append, List.length_singleton]
          omega
        simp only [List.cons_append, friBatchDoomed, friDoomed, hgt, ↓reduceDIte, hne, ↓reduceIte]
  reject_of_doomed stmt oracles chals hdoomed := by
    rw [iopVerify_friBatchIOP_eq_iopVerify_friIOP]
    rw [List.ofFn_succ] at hdoomed
    simp only [friBatchDoomed] at hdoomed
    have htail :
        friBatchTailTranscript
            (List.ofFn fun j : Fin (params.m + 1) => (oracles j.succ, chals j.succ)) =
          List.ofFn fun j : Fin (params.m + 1) => (oracles j.succ, friTailChals chals j) := by
      simp only [friBatchTailTranscript, List.map_ofFn]
      rfl
    rw [htail] at hdoomed
    exact (friIOP_rbrSound params e).reject_of_doomed (stmt.eval (chals 0).batchCoeffs)
      (fun j => oracles j.succ) (friTailChals chals) hdoomed

end RoundByRoundInvariant

/-! ### Section 2: Marginal Challenge Projections and 1-Line Tail Escape Lifts -/

section MarginalProjectionsAndTailEscape

/-- Projecting a uniform `FRIBatchChal F d q t` onto `batchCoeffs` yields the uniform distribution
on `Fin t → F`. -/
theorem uniformOfFintype_friBatchChal_map_batchCoeffs {F : Type} [Fintype F] [Nonempty F]
    (d q t : ℕ) :
    (PMF.uniformOfFintype (FRIBatchChal F d q t)).map FRIBatchChal.batchCoeffs =
      PMF.uniformOfFintype (Fin t → F) := by
  have hcomp : (FRIBatchChal.batchCoeffs : FRIBatchChal F d q t → Fin t → F) =
      Prod.fst ∘ FRIBatchChal.equivProd F d q t :=
    rfl
  rw [hcomp, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv (FRIBatchChal.equivProd F d q t),
    PMF.uniformOfFintype_prod_map_fst]

/-- Projecting a uniform `FRIBatchChal F d q t` onto `toFRIChal` yields the uniform distribution
on `FRIChal F d q`. -/
theorem uniformOfFintype_friBatchChal_map_toFRIChal {F : Type} [Fintype F] [Nonempty F]
    (d q t : ℕ) :
    (PMF.uniformOfFintype (FRIBatchChal F d q t)).map FRIBatchChal.toFRIChal =
      PMF.uniformOfFintype (FRIChal F d q) := by
  have hcomp : (FRIBatchChal.toFRIChal : FRIBatchChal F d q t → FRIChal F d q) =
      Prod.snd ∘ FRIBatchChal.equivProd F d q t :=
    rfl
  rw [hcomp, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv (FRIBatchChal.equivProd F d q t),
    PMF.uniformOfFintype_prod_map_snd]

/-- Outer-measure marginal identity for `FRIBatchChal.batchCoeffs` under the uniform distribution.
-/
theorem toOuterMeasure_uniform_friBatchChal_batchCoeffs {F : Type} [Fintype F] [Nonempty F]
    {d q t : ℕ} (S : Set (Fin t → F)) :
    (PMF.uniformOfFintype (FRIBatchChal F d q t)).toOuterMeasure
        {c | c.batchCoeffs ∈ S} =
      (PMF.uniformOfFintype (Fin t → F)).toOuterMeasure S := by
  rw [← uniformOfFintype_friBatchChal_map_batchCoeffs (F := F) d q t, PMF.toOuterMeasure_map_apply]
  rfl

/-- Outer-measure marginal identity for `FRIBatchChal.toFRIChal` under the uniform distribution. -/
theorem toOuterMeasure_uniform_friBatchChal_toFRIChal {F : Type} [Fintype F] [Nonempty F]
    {d q t : ℕ} (S : Set (FRIChal F d q)) :
    (PMF.uniformOfFintype (FRIBatchChal F d q t)).toOuterMeasure
        {c | c.toFRIChal ∈ S} =
      (PMF.uniformOfFintype (FRIChal F d q)).toOuterMeasure S := by
  rw [← uniformOfFintype_friBatchChal_map_toFRIChal (F := F) d q t, PMF.toOuterMeasure_map_apply]
  rfl

variable {F : Type} [Field F]

/-- Exact reduction of any non-empty prefix escape probability in `friBatchIOP`
(`pref = (π₀, c₀) :: rest`) to the corresponding single-word `friIOP` escape probability on
`stmt.eval c₀.batchCoeffs` and `friBatchTailTranscript rest`. -/
theorem toOuterMeasure_not_friBatchGoodStep_cons [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t B : ℕ) (stmt : FRIBatchStmt F params.d t)
    (π₀ : OracleTable params.d F) (c₀ : FRIBatchChal F params.d params.q t)
    (rest : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    (π : OracleTable params.d F) :
    (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
        {c | ¬ friBatchGoodStep params t B stmt ((π₀, c₀) :: rest) π c} =
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c' | ¬ friGoodStep params B (stmt.eval c₀.batchCoeffs)
          (friBatchTailTranscript rest) π c'} := by
  simp only [friBatchGoodStep_cons]
  exact toOuterMeasure_uniform_friBatchChal_toFRIChal
    {c' | ¬ friGoodStep params B (stmt.eval c₀.batchCoeffs) (friBatchTailTranscript rest) π c'}

/-- **Unconditional query-round escape bound for `friBatchIOP`**: when `pref.length = params.m + 1`
and `pref` is doomed at threshold `B`, the probability over a uniform `FRIBatchChal` that all `q`
query repetitions pass is at most `(B / 2 ^ d) ^ q`. -/
theorem friBatchQueryRound_escape_le [Fintype F] [DecidableEq F] (params : FRIParams F) (t B : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (pref : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    (hlen : pref.length = params.m + 1) (π : OracleTable params.d F)
    (hdoomed : friBatchDoomed params t B stmt pref) :
    (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
        {c | ¬ friBatchGoodStep params t B stmt pref π c} ≤
      ((B : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  cases pref with
  | nil => simp at hlen
  | cons head rest =>
    rw [toOuterMeasure_not_friBatchGoodStep_cons]
    have htail_len : (friBatchTailTranscript rest).length = params.m := by
      simp only [List.length_cons] at hlen
      rw [length_friBatchTailTranscript]
      omega
    exact friQueryRound_escape_le params B (stmt.eval head.2.batchCoeffs)
      (friBatchTailTranscript rest) htail_len π hdoomed

/-- **Conditional step (batched folding-round escape bound assuming `WeightedLineGapBound`)**: for
any folding round (`1 ≤ pref.length` and `pref.length ≤ params.m`) that is doomed at threshold `B`,
the escape probability over a uniform `FRIBatchChal` is at most `B_commit / |F|`. This does not
discharge `WeightedLineGapBound` itself. -/
theorem friBatchCommitRound_escape_le_of_weightedLineGap [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {B B_commit : ℕ}
    (hgap : WeightedLineGapBound params B B_commit)
    (stmt : FRIBatchStmt F params.d t)
    (pref : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    (hpos : 1 ≤ pref.length) (hle : pref.length ≤ params.m) (π : OracleTable params.d F)
    (hdoomed : friBatchDoomed params t B stmt pref) :
    (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
        {c | ¬ friBatchGoodStep params t B stmt pref π c} ≤
      (B_commit : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  cases pref with
  | nil => simp at hpos
  | cons head rest =>
    rw [toOuterMeasure_not_friBatchGoodStep_cons]
    have htail_lt : (friBatchTailTranscript rest).length < params.m := by
      simp only [List.length_cons] at hle
      rw [length_friBatchTailTranscript]
      omega
    exact friCommitRound_escape_le_of_weightedLineGap params hgap (stmt.eval head.2.batchCoeffs)
      (friBatchTailTranscript rest) htail_lt π hdoomed

end MarginalProjectionsAndTailEscape

/-! ### Section 3: Round-0 Unweighted Affine-Word Escape Contracts and Discharges -/

section Round0ContractsAndDischarges

variable {F : Type} [Field F]

/-- **Polymorphic integer round-0 batching proximity-gap contract**: for every false tuple
`stmt ∉ params.batchProximityLang t e`, any set `T` of batching vectors `x : Fin t → F` whose
affine evaluation `stmt.eval x` achieves unweighted agreement `> 2 ^ d - e - 1` (strictly above
`B / n` for `n = 2 ^ d` and `B = n - e - 1`) with `params.initialCode` satisfies
`|F| * #T ≤ B_batch * |F| ^ t` (containing the `μ⁽⁰⁾`-weighted oracle event `E⁽⁰⁾` of
[BenSassonCarmonIshaiKoppartySaraf2020], Section 8.2.1, printed pp. 41–42, Eq. (8.8), whenever the
paper's cutoff is at least `B / n`). -/
@[expose] def BatchRound0GapBound [Fintype F] [DecidableEq F] (params : FRIParams F)
    (t e B_batch : ℕ) : Prop :=
  ∀ stmt ∉ params.batchProximityLang t e, ∀ T : Finset (Fin t → F),
    (∀ x ∈ T, ∃ c ∈ params.initialCode,
      2 ^ params.d - e - 1 <
        (Finset.univ.filter fun s : Fin (2 ^ params.d) => stmt.eval x s = c s).card) →
    Fintype.card F * T.card ≤ B_batch * Fintype.card F ^ t

theorem BatchRound0GapBound.mono [Fintype F] [DecidableEq F] {params : FRIParams F}
    {t e B₁ B₂ : ℕ} (h : BatchRound0GapBound params t e B₁) (hle : B₁ ≤ B₂) :
    BatchRound0GapBound params t e B₂ :=
  fun stmt hnot T hT => (h stmt hnot T hT).trans (Nat.mul_le_mul_right _ hle)

/-- **Polymorphic `ℝ≥0∞` round-0 batching escape contract**: for every false tuple
`stmt ∉ params.batchProximityLang t e`, a uniformly sampled batching vector `x : Fin t → F` lands at
unweighted agreement `> 2 ^ d - e - 1` (strictly above `B / n` for `n = 2 ^ d` and `B = n - e - 1`)
with `params.initialCode` with probability at most `ε_batch`. Accepts real-valued error densities
directly without integer-floor rounding (and contains the `μ⁽⁰⁾`-weighted oracle event `E⁽⁰⁾` of
[BenSassonCarmonIshaiKoppartySaraf2020], Section 8.2.1, printed pp. 41–42, Eq. (8.8), whenever the
paper's cutoff is at least `B / n`). -/
@[expose] def BatchRound0Escape [Fintype F] [DecidableEq F] (params : FRIParams F)
    (t e : ℕ) (ε_batch : ℝ≥0∞) : Prop :=
  ∀ stmt ∉ params.batchProximityLang t e,
    (PMF.uniformOfFintype (Fin t → F)).toOuterMeasure
      {x : Fin t → F | ∃ c ∈ params.initialCode,
        2 ^ params.d - e - 1 <
          (Finset.univ.filter fun s : Fin (2 ^ params.d) => stmt.eval x s = c s).card} ≤ ε_batch

theorem BatchRound0Escape.mono [Fintype F] [DecidableEq F] {params : FRIParams F}
    {t e : ℕ} {ε₁ ε₂ : ℝ≥0∞} (h : BatchRound0Escape params t e ε₁) (hle : ε₁ ≤ ε₂) :
    BatchRound0Escape params t e ε₂ :=
  fun stmt hnot => (h stmt hnot).trans hle

/-- Convert an integer `BatchRound0GapBound` budget `B_batch` into `BatchRound0Escape` with escape
bound `(B_batch : ℝ≥0∞) / |F|`. -/
theorem batchRound0Escape_of_gapBound [Fintype F] [DecidableEq F] (params : FRIParams F)
    {t e B_batch : ℕ} (hgap : BatchRound0GapBound params t e B_batch) :
    BatchRound0Escape params t e ((B_batch : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) := by
  classical
  intro stmt hnot
  set P : (Fin t → F) → Prop := fun x =>
    ∃ c ∈ params.initialCode,
      2 ^ params.d - e - 1 <
        (Finset.univ.filter fun s : Fin (2 ^ params.d) => stmt.eval x s = c s).card
  have hcard_bound :
      Fintype.card F * (Finset.univ.filter P).card ≤
        B_batch * Fintype.card (Fin t → F) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    exact hgap stmt hnot (Finset.univ.filter P) fun _ hx => (Finset.mem_filter.mp hx).2
  exact PMF.toOuterMeasure_uniformOfFintype_le_div (α := Fin t → F) (P := P) Fintype.card_pos
    hcard_bound

/-- **Conditional step (round-0 batching escape bound assuming `BatchRound0Escape`)**: for any
false tuple `stmt ∉ params.batchProximityLang t e` and any round-`0` announcement table `π`, the
probability over a uniform `FRIBatchChal` that round `0` escapes `friBatchDoomed` is at most
`ε_batch`. Discharging `BatchRound0Escape` is left to the caller. -/
theorem friBatchRound0_escape_le_of_escape [Fintype F] [DecidableEq F] (params : FRIParams F)
    (t : ℕ) {e : ℕ} {ε_batch : ℝ≥0∞} (hescape : BatchRound0Escape params t e ε_batch)
    {stmt : FRIBatchStmt F params.d t} (hnot : stmt ∉ params.batchProximityLang t e)
    (π : OracleTable params.d F) :
    (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
        {c | ¬ friBatchGoodStep params t (2 ^ params.d - e - 1) stmt [] π c} ≤ ε_batch := by
  have hset :
      {c : FRIBatchChal F params.d params.q t |
        ¬ friBatchGoodStep params t (2 ^ params.d - e - 1) stmt [] π c} =
      {c : FRIBatchChal F params.d params.q t |
        c.batchCoeffs ∈ {x : Fin t → F | ∃ c' ∈ params.initialCode,
          2 ^ params.d - e - 1 <
            (Finset.univ.filter fun s : Fin (2 ^ params.d) => stmt.eval x s = c' s).card}} := by
    ext c
    simp only [Set.mem_ofPred_eq, friBatchGoodStep_nil_iff, not_forall, not_le, exists_prop]
  rw [hset, toOuterMeasure_uniform_friBatchChal_batchCoeffs]
  exact hescape stmt hnot

omit [Field F] in
/-- Private helper: for `e < 2 ^ d`, agreement `> 2 ^ d - e - 1` is equivalent to Hamming distance
`≤ e`. -/
private theorem lt_card_filter_eq_iff_hammingDist_le [DecidableEq F] {d e : ℕ} (he : e < 2 ^ d)
    (w c : OracleTable d F) :
    2 ^ d - e - 1 < (Finset.univ.filter fun s : Fin (2 ^ d) => w s = c s).card ↔
      hammingDist w c ≤ e := by
  have htot := card_filter_eq_add_hammingDist w c
  simp only [Fintype.card_fin] at htot
  omega

/-- Private helper: converts any real-density affine correlated-agreement step on `params.eval 0`
into `BatchRound0Escape params t e (ENNReal.ofReal R)` via
`PMF.toOuterMeasure_uniformOfFintype_toReal`. -/
private theorem batchRound0Escape_of_real_density [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t e : ℕ) (R : ℝ → ℝ)
    (hca : Function.Injective (params.eval 0) →
      params.dim 0 ≤ Fintype.card (Fin (2 ^ (params.d - 0))) →
      ∀ stmt : FRIBatchStmt F params.d t, ∀ T : Finset (Fin t → F),
        R (Fintype.card (Fin (2 ^ (params.d - 0))) : ℝ) <
          (T.card : ℝ) / ((Fintype.card F : ℝ) ^ t) →
        (∀ x ∈ T, ∃ c ∈ params.initialCode, hammingDist (stmt.eval x) c ≤ e) →
        ∃ D' : Finset (Fin (2 ^ (params.d - 0))),
          Fintype.card (Fin (2 ^ (params.d - 0))) - e ≤ D'.card ∧
          ∃ v₀ ∈ params.initialCode, ∃ v : Fin t → OracleTable params.d F,
            (∀ j, v j ∈ params.initialCode) ∧
            ∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s) :
    BatchRound0Escape params t e (ENNReal.ofReal (R (2 ^ params.d : ℝ))) := by
  classical
  intro stmt hnot
  have he_lt : e < 2 ^ params.d := params.lt_two_pow_of_not_mem_batchProximityLang hnot
  have hα : Function.Injective (params.eval 0) :=
    cosetEval_injective params.hg params.hω (Nat.zero_le params.d)
  have hk_le_n : params.dim 0 ≤ Fintype.card (Fin (2 ^ (params.d - 0))) := by
    simpa only [Fintype.card_fin] using params.dim_le_domainSize (Nat.zero_le params.m)
  set S : Set (Fin t → F) := {x | ∃ c ∈ params.initialCode,
    2 ^ params.d - e - 1 <
      (Finset.univ.filter fun s : Fin (2 ^ params.d) => stmt.eval x s = c s).card}
  set T_bad : Finset (Fin t → F) := Finset.univ.filter (· ∈ S)
  have hclose : ∀ x ∈ T_bad, ∃ c ∈ params.initialCode, hammingDist (stmt.eval x) c ≤ e := by
    intro x hx
    obtain ⟨c, hc, hgt⟩ := (Finset.mem_filter.mp hx).2
    exact ⟨c, hc, (lt_card_filter_eq_iff_hammingDist_le he_lt (stmt.eval x) c).mp hgt⟩
  have hR_eq : R (Fintype.card (Fin (2 ^ (params.d - 0))) : ℝ) = R (2 ^ params.d : ℝ) := by
    simp only [Fintype.card_fin, Nat.sub_zero, Nat.cast_pow, Nat.cast_ofNat]
  have hle_R : (T_bad.card : ℝ) / ((Fintype.card F : ℝ) ^ t) ≤ R (2 ^ params.d : ℝ) := by
    by_contra hgt
    obtain ⟨D', hD'_card, v₀, hv₀, v, hv, hagree⟩ :=
      hca hα hk_le_n stmt T_bad (by rw [hR_eq]; exact lt_of_not_ge hgt) hclose
    simp only [Fintype.card_fin, Nat.sub_zero] at hD'_card
    exact hnot ⟨D', hD'_card, v₀, hv₀, v, hv, hagree⟩
  have htoReal :
      ((PMF.uniformOfFintype (Fin t → F)).toOuterMeasure S).toReal =
        (T_bad.card : ℝ) / ((Fintype.card F : ℝ) ^ t) := by
    rw [PMF.toOuterMeasure_uniformOfFintype_toReal]
    simp only [T_bad, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hne_top : (PMF.uniformOfFintype (Fin t → F)).toOuterMeasure S ≠ ⊤ := by
    rw [PMF.toOuterMeasure_uniformOfFintype]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  rw [← ENNReal.ofReal_toReal hne_top, htoReal]
  exact ENNReal.ofReal_le_ofReal hle_R

/-- **Unconditional unique-decoding `BatchRound0GapBound`** for `(t + 1)`-word batched FRI
(applying [BenSassonCarmonIshaiKoppartySaraf2020], Theorems 1.6 and 4.1).

Applies `Cslib.Code.exists_weighted_correlatedAgreement_affine_of_line` with constant weight `1`,
unique-decoding list bound `L = 1 < |F|`, and `Cslib.Code.exists_correlatedAgreement_unique` to
obtain the upper bound `|F| * #T ≤ 2 ^ d * |F| ^ t` (exact denominator `|F|` rather than
`|F| - 1`) uniformly for all `t : ℕ` with no list-size premise. -/
theorem batchRound0GapBound_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ}
    (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) :
    BatchRound0GapBound params t e (2 ^ params.d) := by
  classical
  intro stmt hnot T hT_good
  by_contra hgt
  have hT : 2 ^ params.d * Fintype.card F ^ t < Fintype.card F * T.card := Nat.lt_of_not_ge hgt
  have he_lt : e < 2 ^ params.d := params.lt_two_pow_of_not_mem_batchProximityLang hnot
  have hα : Function.Injective (params.eval 0) :=
    cosetEval_injective params.hg params.hω (Nat.zero_le params.d)
  have hlist : ∀ u : Fin (2 ^ params.d) → F,
      ∃ Lset : Finset (Fin (2 ^ params.d) → F), Lset.card ≤ 1 ∧
        ∀ c ∈ params.initialCode,
          2 ^ params.d - e ≤
            ∑ _i ∈ Finset.univ.filter (fun i => u i = c i), (1 : ℕ) →
          c ∈ Lset := by
    intro u
    by_cases hex : ∃ c ∈ params.initialCode,
        2 ^ params.d - e ≤ ∑ _i ∈ Finset.univ.filter (fun i => u i = c i), (1 : ℕ)
    · obtain ⟨c₀, hc₀, hge₀⟩ := hex
      refine ⟨{c₀}, (Finset.card_singleton c₀).le, fun c hc hge => ?_⟩
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at hge₀ hge
      have hd₀ : hammingDist u c₀ ≤ e :=
        (lt_card_filter_eq_iff_hammingDist_le he_lt u c₀).mp (by omega)
      have hdc : hammingDist u c ≤ e :=
        (lt_card_filter_eq_iff_hammingDist_le he_lt u c).mp (by omega)
      have heq : c = c₀ :=
        eq_of_hammingDist_le_reedSolomon hα
          (by simpa only [Fintype.card_fin, Nat.sub_zero] using huniq) hc hc₀ hdc hd₀
      exact Finset.mem_singleton.mpr heq
    · refine ⟨∅, by simp, fun c hc hge => False.elim (hex ⟨c, hc, hge⟩)⟩
  have hline : ∀ {B' : ℕ}, 2 ^ params.d - e ≤ B' →
      ∀ (a b : Fin (2 ^ params.d) → F) (S : Finset F),
        2 ^ params.d < S.card →
        (∀ z ∈ S, ∃ c ∈ params.initialCode,
          B' ≤ ∑ _i ∈ Finset.univ.filter (fun i => (a + z • b) i = c i), (1 : ℕ)) →
        ∃ D' : Finset (Fin (2 ^ params.d)), B' ≤ ∑ _i ∈ D', (1 : ℕ) ∧
          ∃ w₀ ∈ params.initialCode, ∃ w₁ ∈ params.initialCode,
            ∀ i ∈ D', a i = w₀ i ∧ b i = w₁ i := by
    intro B' hB' a b S hS hcl
    obtain ⟨z₀, hz₀⟩ := Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hS)
    obtain ⟨c₀, _, hc₀_ge⟩ := hcl z₀ hz₀
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hc₀_ge
    have hc₀_le : (Finset.univ.filter fun i : Fin (2 ^ params.d) => (a + z₀ • b) i = c₀ i).card ≤
        2 ^ params.d :=
      (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
    have hB'_le : B' ≤ 2 ^ params.d := hc₀_ge.trans hc₀_le
    set e' : ℕ := 2 ^ params.d - B'
    have huniq' : 2 * e' + params.dim 0 ≤ Fintype.card (Fin (2 ^ (params.d - 0))) := by
      simp only [Fintype.card_fin, Nat.sub_zero]
      omega
    have hcl_dist : ∀ z ∈ S, ∃ c ∈ params.initialCode, hammingDist (a + z • b) c ≤ e' := by
      intro z hz
      obtain ⟨c, hc, hge⟩ := hcl z hz
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at hge
      have htot := card_filter_eq_add_hammingDist (a + z • b) c
      simp only [Fintype.card_fin] at htot
      exact ⟨c, hc, by omega⟩
    obtain ⟨D', hD'_card, w₀, hw₀, w₁, hw₁, hag⟩ :=
      exists_correlatedAgreement_unique hα huniq' a b S
        (by simpa only [Fintype.card_fin, Nat.sub_zero] using hS) hcl_dist
    refine ⟨D', ?_, w₀, hw₀, w₁, hw₁, hag⟩
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    simp only [Fintype.card_fin, Nat.sub_zero] at hD'_card
    omega
  have hcloseW : ∀ x ∈ T, ∃ c ∈ params.initialCode,
      2 ^ params.d - e ≤
        ∑ _i ∈ Finset.univ.filter (fun i => (stmt.base + ∑ j : Fin t, x j • stmt.terms j) i = c i),
          (1 : ℕ) := by
    intro x hx
    obtain ⟨c, hc, hgt_c⟩ := hT_good x hx
    refine ⟨c, hc, ?_⟩
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    change 2 ^ params.d - e ≤
      (Finset.univ.filter fun s : Fin (2 ^ params.d) => stmt.eval x s = c s).card
    omega
  obtain ⟨D', _, hD'_sum, v₀, hv₀, v, hv, hagree⟩ :=
    exists_weighted_correlatedAgreement_affine_of_line (C := params.initialCode)
      (W := fun _ => 1) (B_W := 2 ^ params.d - e) (B_line := 2 ^ params.d) (L := 1)
      hlist hline (fun _ => Fintype.one_lt_card) stmt.base stmt.terms T hT hcloseW
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hD'_sum
  exact hnot ⟨D', hD'_sum, v₀, hv₀, v, hv, hagree⟩

/-- **Unconditional unique-decoding `BatchRound0Escape` upper bound** for `(t + 1)`-word batched
FRI: bounds the round-`0` unweighted affine-word escape probability by
`(2 ^ params.d : ℝ≥0∞) / |F|` uniformly for all `t : ℕ` whenever `2 * e + params.dim 0 ≤ 2 ^ d`
(at batch size `t = 0`, `stmt.eval x = stmt.base` is independent of `x` and the actual round-`0`
escape probability is `0`). -/
theorem batchRound0Escape_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ}
    (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) :
    BatchRound0Escape params t e ((2 ^ params.d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    batchRound0Escape_of_gapBound params (batchRound0GapBound_of_unique params t huniq)

/-- **Unconditional explicit-parameter Johnson `BatchRound0GapBound`** for `(t + 1)`-word batched
FRI (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on printed p. 6).

Given Guruswami–Sudan parameters `(m₀, D₀)` at round `0` satisfying the interpolation and
root-divisibility conditions, discharges `BatchRound0GapBound params t e B_batch` directly from
`Cslib.Code.exists_correlatedAgreement_affine_johnson` with `johnsonCurveBound` budget independent
of `t` and no list-size premise. -/
theorem batchRound0GapBound_of_johnson_discrete [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e m₀ D₀ B_batch : ℕ}
    (hm₀ : 1 ≤ m₀)
    (hk_le : params.dim 0 ≤ 2 ^ params.d - e)
    (hinterp : 2 ^ params.d * (m₀ * (m₀ + 1) / 2) <
      #(Sudan.monomials (params.dim 0 - 1) D₀))
    (hroot : D₀ < m₀ * (2 ^ params.d - e))
    (hbound : ProximityGap.johnsonCurveBound (2 ^ params.d) m₀
      (params.dim 0 - 1) D₀ 1 (2 ^ params.d) ≤ B_batch) :
    BatchRound0GapBound params t e B_batch := by
  intro stmt hnot T hT_good
  by_contra hgt
  have he_lt : e < 2 ^ params.d := params.lt_two_pow_of_not_mem_batchProximityLang hnot
  have hα : Function.Injective (params.eval 0) :=
    cosetEval_injective params.hg params.hω (Nat.zero_le params.d)
  have hT_jb :
      ProximityGap.johnsonCurveBound (Fintype.card (Fin (2 ^ (params.d - 0)))) m₀
          (params.dim 0 - 1) D₀ 1 (Fintype.card (Fin (2 ^ (params.d - 0)))) *
        Fintype.card F ^ t < Fintype.card F * T.card := by
    simp only [Fintype.card_fin, Nat.sub_zero]
    exact (Nat.mul_le_mul_right _ hbound).trans_lt (Nat.lt_of_not_ge hgt)
  have hclose : ∀ x ∈ T, ∃ c ∈ params.initialCode,
      hammingDist (stmt.base + ∑ j : Fin t, x j • stmt.terms j) c ≤ e := by
    intro x hx
    obtain ⟨c, hc, hgt_c⟩ := hT_good x hx
    exact ⟨c, hc, (lt_card_filter_eq_iff_hammingDist_le he_lt (stmt.eval x) c).mp hgt_c⟩
  obtain ⟨D', hD'_card, v₀, hv₀, v, hv, hagree⟩ :=
    exists_correlatedAgreement_affine_johnson hα (params.one_le_dim 0) hm₀
      (by simpa only [Fintype.card_fin, Nat.sub_zero] using hk_le)
      (by simpa only [Fintype.card_fin, Nat.sub_zero] using hinterp)
      (by simpa only [Fintype.card_fin, Nat.sub_zero] using hroot)
      stmt.base stmt.terms T hT_jb hclose
  simp only [Fintype.card_fin, Nat.sub_zero] at hD'_card
  exact hnot ⟨D', hD'_card, v₀, hv₀, v, hv, hagree⟩

/-- **Unconditional explicit-parameter Johnson `BatchRound0Escape` upper bound** for `(t + 1)`-word
batched FRI, bounding the round-`0` unweighted affine-word escape probability by `B_batch / |F|`
uniformly for all `t : ℕ` with no list-size premise. -/
theorem batchRound0Escape_of_johnson_discrete [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e m₀ D₀ B_batch : ℕ}
    (hm₀ : 1 ≤ m₀)
    (hk_le : params.dim 0 ≤ 2 ^ params.d - e)
    (hinterp : 2 ^ params.d * (m₀ * (m₀ + 1) / 2) <
      #(Sudan.monomials (params.dim 0 - 1) D₀))
    (hroot : D₀ < m₀ * (2 ^ params.d - e))
    (hbound : ProximityGap.johnsonCurveBound (2 ^ params.d) m₀
      (params.dim 0 - 1) D₀ 1 (2 ^ params.d) ≤ B_batch) :
    BatchRound0Escape params t e ((B_batch : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  batchRound0Escape_of_gapBound params
    (batchRound0GapBound_of_johnson_discrete params t hm₀ hk_le hinterp hroot hbound)

/-- Explicit Siegel integer round-`0` batching budget for `(t + 1)`-word FRI in the Johnson regime
with multiplicity slack `mJ`: `(1800 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3) / params.dim 0`
(the un-folded `n_0 = 2 ^ d` counterpart of `friJohnsonCommitBound`). -/
abbrev friBatchJohnsonRound0Bound (params : FRIParams F) (mJ : ℕ) : ℕ :=
  (1800 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3) / params.dim 0

/-- **Original explicit-constant Johnson `BatchRound0GapBound`** for `(t + 1)`-word batched FRI up
to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - √ρ / (2 * mJ)` (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on printed p. 6).

Instantiates `ProximityGap.johnson_line_params_bound` and `batchRound0GapBound_of_johnson_discrete`
with this library's explicit Siegel budget `friBatchJohnsonRound0Bound params mJ`, uniformly for all
`t : ℕ` and with no list-size premise (not uniformly smaller at small `mJ` than the paper's
displayed finite constant). -/
theorem batchRound0GapBound_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ))) :
    BatchRound0GapBound params t e (friBatchJohnsonRound0Bound params mJ) := by
  set n₀ : ℕ := 2 ^ params.d
  set k₀ : ℕ := params.dim 0
  have hk₀_pos : 0 < k₀ := params.one_le_dim 0
  have hk₀_le_n₀ : k₀ ≤ n₀ := by
    simpa only [Nat.sub_zero] using params.dim_le_domainSize (Nat.zero_le params.m)
  obtain ⟨hk_sub, hinterp, hroot, hjb⟩ :=
    ProximityGap.johnson_line_params_bound (n := n₀) (k := k₀) (e := e) (m := mJ)
      hk₀_pos hk₀_le_n₀ hmJ (by simpa only [n₀, k₀, Nat.cast_pow, Nat.cast_ofNat] using he)
  have hk₀R_pos : (0 : ℝ) < (k₀ : ℝ) := Nat.cast_pos.mpr hk₀_pos
  have hn₀R_ne : (n₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (by positivity))
  have hmulR :
      (ProximityGap.johnsonCurveBound n₀ (mJ + 1) (k₀ - 1)
          ((mJ + 1) * ⌈(1 + 1 / (2 * (mJ : ℝ))) * Real.sqrt ((n₀ : ℝ) * (k₀ : ℝ))⌉₊ - 1) 1 n₀ : ℝ) *
        (k₀ : ℝ) ≤ 1800 * ((mJ + 1 : ℝ) ^ 6) * ((n₀ : ℝ) ^ 3) := by
    have h1 := mul_le_mul_of_nonneg_right hjb hk₀R_pos.le
    have hrhs :
        (1800 * ((mJ + 1 : ℝ) ^ 6) * ((n₀ : ℝ) ^ 2) / ((k₀ : ℝ) / (n₀ : ℝ))) * (k₀ : ℝ) =
          1800 * ((mJ + 1 : ℝ) ^ 6) * ((n₀ : ℝ) ^ 3) := by
      field_simp
    linarith
  have hbound :
      ProximityGap.johnsonCurveBound n₀ (mJ + 1) (k₀ - 1)
          ((mJ + 1) * ⌈(1 + 1 / (2 * (mJ : ℝ))) * Real.sqrt ((n₀ : ℝ) * (k₀ : ℝ))⌉₊ - 1) 1 n₀ ≤
        friBatchJohnsonRound0Bound params mJ :=
    (Nat.le_div_iff_mul_le hk₀_pos).mpr (by exact_mod_cast hmulR)
  exact batchRound0GapBound_of_johnson_discrete params t (by omega) hk_sub hinterp hroot hbound

/-- **Original explicit-constant Johnson `BatchRound0Escape` upper bound** for `(t + 1)`-word
batched FRI up to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - √ρ / (2 * mJ)` (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on printed p. 6).

Bounds the round-`0` unweighted affine-word escape probability by
`ENNReal.ofReal (1800 * (mJ + 1) ^ 6 * (2 ^ d) ^ 2 / (ρ * |F|))` uniformly for all `t : ℕ` with no
list-size premise via `Cslib.Code.exists_correlatedAgreement_affine_johnson_of_multiplicity` (this
library's original Siegel constant, not uniformly smaller at small `mJ` than the paper's displayed
constant). -/
theorem batchRound0Escape_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ))) :
    BatchRound0Escape params t e
      (ENNReal.ofReal
        (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
          (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ)))) :=
  batchRound0Escape_of_real_density params t e
    (fun N => 1800 * ((mJ + 1 : ℝ) ^ 6) * (N ^ 2) /
      (((params.dim 0 : ℝ) / N) * (Fintype.card F : ℝ)))
    fun hα hk_le_n stmt T hT hclose =>
      exists_correlatedAgreement_affine_johnson_of_multiplicity hα (params.one_le_dim 0) hk_le_n hmJ
        (by simpa only [Fintype.card_fin, Nat.sub_zero, Nat.cast_pow, Nat.cast_ofNat] using he)
        stmt.base stmt.terms T hT hclose

/-- **Original explicit-constant `η`-gap Johnson `BatchRound0Escape` upper bound** for
`(t + 1)`-word batched FRI up to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - η` (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on printed p. 6).

Bounds the round-`0` unweighted affine-word escape probability by
`ENNReal.ofReal (115200 * (2 ^ d) ^ 2 / (ρ * η ^ 6 * |F|))` uniformly for all `t : ℕ` with no
list-size premise via `Cslib.Code.exists_correlatedAgreement_affine_johnson_of_eta` (an original
finite bound using `η` directly rather than `min(η, √ρ / 20)` in Eq. (1.3)). -/
theorem batchRound0Escape_of_johnson_eta [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η) :
    BatchRound0Escape params t e
      (ENNReal.ofReal
        (115200 * ((2 ^ params.d : ℝ) ^ 2) /
          (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)))) :=
  batchRound0Escape_of_real_density params t e
    (fun N => 115200 * (N ^ 2) /
      (((params.dim 0 : ℝ) / N) * (η ^ 6) * (Fintype.card F : ℝ)))
    fun hα hk_le_n stmt T hT hclose =>
      exists_correlatedAgreement_affine_johnson_of_eta hα (params.one_le_dim 0) hk_le_n hη
        (by simpa only [Fintype.card_fin, Nat.sub_zero, Nat.cast_pow, Nat.cast_ofNat] using he)
        stmt.base stmt.terms T hT hclose

end Round0ContractsAndDischarges

/-! ### Section 4: Conditional Uniform RBR Escape & Adaptive Two-Channel BCS ROM Composition -/

section UniformRBRAndBCSROM

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Uniform per-round escape error for `(params.m + 2)`-round `friBatchIOP`: the maximum of the
round-`0` batching escape `ε_batch` and `friRBRError params e B_commit` (covering folding rounds
`1, …, m` at `B_commit / |F|` and the final query round `m + 1` at `((2 ^ d - e - 1) / 2 ^ d) ^ q`).
-/
@[expose] noncomputable def friBatchRBRError (params : FRIParams F) (ε_batch : ℝ≥0∞)
    (e B_commit : ℕ) : ℝ≥0∞ :=
  max ε_batch (friRBRError params e B_commit)

/-- **Conditional step (uniform batched FRI round-by-round escape bound assuming `BatchRound0Escape`
and `WeightedLineGapBound`)**: across all transcript prefixes `pref` (round-`0` batching
`pref = []`, folding rounds `1 ≤ pref.length ≤ m`, query round `pref.length = m + 1`, and
unreachable lengths `pref.length ≥ m + 2`), the per-round escape probability is at most
`friBatchRBRError params ε_batch e B_commit`. Discharging `BatchRound0Escape` and
`WeightedLineGapBound` is left to the caller. -/
theorem friBatchRBREscape_of_escape (params : FRIParams F) (t : ℕ) {e B_commit : ℕ}
    {ε_batch : ℝ≥0∞}
    (hbatch : BatchRound0Escape params t e ε_batch)
    (hgap : WeightedLineGapBound params (2 ^ params.d - e - 1) B_commit) :
    ∀ stmt ∉ params.batchProximityLang t e, ∀ pref π,
      friBatchDoomed params t (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
        {c | ¬ friBatchGoodStep params t (2 ^ params.d - e - 1) stmt pref π c} ≤
      friBatchRBRError params ε_batch e B_commit := by
  intro stmt hnot pref π hdoomed
  cases pref with
  | nil =>
    exact (friBatchRound0_escape_le_of_escape params t hbatch hnot π).trans (le_max_left _ _)
  | cons head rest =>
    by_cases hle : (head :: rest).length ≤ params.m
    · have hpos : 1 ≤ (head :: rest).length := by simp
      exact (friBatchCommitRound_escape_le_of_weightedLineGap params t hgap stmt (head :: rest)
        hpos hle π hdoomed).trans ((le_max_left _ _).trans (le_max_right _ _))
    · by_cases heq : (head :: rest).length = params.m + 1
      · exact (friBatchQueryRound_escape_le params t (2 ^ params.d - e - 1) stmt (head :: rest)
          heq π hdoomed).trans ((le_max_right _ _).trans (le_max_right _ _))
      · have hgt : ¬ (head :: rest).length ≤ params.m + 1 := by omega
        simp only [friBatchGoodStep, hgt, ↓reduceIte, not_true_eq_false, Set.ofPred_false]
        exact (MeasureTheory.OuterMeasure.empty _).trans_le zero_le

/-- **Conditional step (adaptive two-channel BCS-FRI ROM soundness for `friBatchIOP` assuming
`BatchRound0Escape` and `WeightedLineGapBound`)**: composes `friBatchIOP_rbrSound` and
`friBatchRBREscape_of_escape` with `Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound`
([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]); discharging `BatchRound0Escape` and
`WeightedLineGapBound` is left to the caller. -/
theorem friBatchBCS_romSoundness_bound_of_escape (params : FRIParams F) (t : ℕ) {e B_commit : ℕ}
    {ε_batch : ℝ≥0∞}
    (hbatch : BatchRound0Escape params t e ε_batch)
    (hgap : WeightedLineGapBound params (2 ^ params.d - e - 1) B_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friBatchIOP params t) encSym (params.batchProximityLang t e) P) Q_MT) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friBatchRBRError params ε_batch e B_commit +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound (friBatchIOP_rbrSound params t e)
    (friBatchRBREscape_of_escape params t hbatch hgap) hdec 0 σ hFS hMT

/-- **Conditional step (adaptive two-channel BCS-FRI ROM soundness for `friBatchIOP` with separate
prover/verifier Merkle budgets assuming `BatchRound0Escape` and `WeightedLineGapBound`)**: bounds
verifier Merkle cost via `isCostBounded_bcsMTCost_friBatchVerifyROM`
(`q_V = params.proofOracleQueries * (L_path + 1)`, independent of `t`) and composes with
`Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound_of_prover_verifier` ([BenSassonChiesaSpooner2016];
[ChiesaYogev2024]); discharging `BatchRound0Escape` and `WeightedLineGapBound` is left to the
caller. -/
theorem friBatchBCS_romSoundness_bound_of_prover_verifier_of_escape (params : FRIParams F) (t : ℕ)
    {e B_commit : ℕ} {ε_batch : ℝ≥0∞}
    (hbatch : BatchRound0Escape params t e ε_batch)
    (hgap : WeightedLineGapBound params (2 ^ params.d - e - 1) B_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friBatchRBRError params ε_batch e B_commit +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound_of_prover_verifier (friBatchIOP_rbrSound params t e)
    (friBatchRBREscape_of_escape params t hbatch hgap) hdec 0 σ hMT hFS
    (fun x prf hmem =>
      isCostBounded_bcsMTCost_friBatchVerifyROM params t encSym x prf (hops x prf hmem))

end UniformRBRAndBCSROM

end Cslib.Crypto.Protocols.FRI
