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
import CslibFrontier.Foundations.Data.Hamming
import CslibFrontier.Probability.PMF.UniformBound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Smooth & Binary Batched FRI Round-0 Soundness, Affine Correlated Agreement, and BCS Composition

This module proves unconditional round-by-round soundness
(`Cslib.Crypto.Protocols.BCS.IOPRoundByRoundSoundness` — initialization on false tuples,
preservation on good transitions, and terminal rejection), marginal challenge projections, and
unconditional round-`0` unweighted affine-word escape upper bounds for the `(params.m + 2)`-round
smooth batched FRI IOP `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP` (with per-round folding arity
`l⁽ⁱ⁾ = 2 ^ stepLog i ≥ 2`) and its binary 2-to-1 specialization
`Cslib.Crypto.Protocols.FRI.friBatchIOP`
([BenSassonCarmonIshaiKoppartySaraf2020], accepted *Journal of the ACM* 2023 manuscript,
Section 8.2 on printed pp. 36–40 and Section 8.2.1 on printed pp. 41–43), together with conditional
whole-protocol uniform escape and two-channel BCS random-oracle composition steps
([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]).

## Summary of the round-by-round invariant and round-0 probability bounds

1. **Smooth & binary round-by-round invariant (`friSmoothBatchDoomed`, `friSmoothBatchGoodStep`,
   `friSmoothBatchIOP_rbrSound`, and binary corollaries).**
   `friSmoothBatchIOP_rbrSound` establishes initialization on any false tuple
   `stmt ∉ params.batchProximityLang t e` (`init_doomed`), preservation of `friSmoothBatchDoomed`
   on good round transitions (`step_doomed`), and terminal verifier rejection (`iopVerify = false`)
   of any complete doomed transcript (`reject_of_doomed`). In this Lean ordering, the uniform
   round-`0` batching challenge `x = c₀.batchCoeffs : Fin t → F` selects the affine word
   `stmt.eval x` first, and an adaptive prover can choose its next oracle (`f⁽⁰⁾`, round `1`) after
   seeing `c₀`. After round `0` (`(_, c₀) :: rest`), `friSmoothBatchDoomed` delegates to single-word
   `friSmoothDoomed` on `stmt.eval c₀.batchCoeffs` and `friBatchTailTranscript rest`, absorbing any
   discrepancy between the reported oracle `f⁽⁰⁾` and `stmt.eval x` via
   `sum_agree_friSmoothOracleFilterWeight_le`.
2. **Marginal challenge projections and 1-line tail reuse.**
   Via `FRIBatchChal.equivProd`, uniform sampling on `FRIBatchChal F d q t` projects to uniform
   `Fin t → F` under `batchCoeffs` (`toOuterMeasure_uniform_friBatchChal_batchCoeffs`) and to
   uniform `FRIChal F d q` under `toFRIChal` (`toOuterMeasure_uniform_friBatchChal_toFRIChal`),
   reducing every non-empty prefix escape probability
   (`toOuterMeasure_not_friSmoothBatchGoodStep_cons`), query-round escape
   (`friSmoothBatchQueryRound_escape_le`), and folding-round escape
   (`friSmoothBatchCommitRound_escape_le_of_weightedCurveGap`) directly to
   `CslibFrontier/Crypto/Protocols/FRI/Soundness.lean` with zero duplicated folding or query proofs.
3. **Round-0 probability upper bounds from affine correlated agreement, and whole-protocol steps.**
   The unique-decoding (`smoothBatchRound0GapBound_of_unique`, `smoothBatchRound0Escape_of_unique`),
   discrete Johnson (`smoothBatchRound0GapBound_of_johnson_discrete`,
   `smoothBatchRound0Escape_of_johnson_discrete`), and closed-form Johnson / `η`-gap
   (`smoothBatchRound0GapBound_of_johnson`, `smoothBatchRound0Escape_of_johnson`,
   `smoothBatchRound0Escape_of_johnson_eta`) results supply round-`0` probability upper bounds
   (with exact denominator `|F|` and no list-size premise) on the chance that the affine word
   `stmt.eval x` is within Hamming distance `e` of `params.initialCode` for a false tuple under
   their respective parameter conditions. At batch size `t = 0`, the false word
   `stmt.eval x = stmt.base` is independent of the challenge and its actual round-`0` escape
   probability is `0` (while the `t`-uniform theorems still supply valid upper bounds). Whole-
   protocol steps (`friSmoothBatchRBREscape_of_escape`,
   `friSmoothBatchBCS_romSoundness_bound_of_escape`,
   `FRI.friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_escape`) still require escape
   estimates (`WeightedCurveGapBound`) for the remaining `m` folding rounds alongside the query
   bound. All binary `FRIParams` theorems are proved as short corollaries via `FRIParams.toSmooth`
   and `friBatchIOP_eq_friSmoothBatchIOP`.

## Scope and relationship to the source theorems

* **Round-`0` event vs. Section 8.2.1 Eq. (8.8) (printed pp. 41–42):** In
  [BenSassonCarmonIshaiKoppartySaraf2020], Section 8.2.1 defines the round-`0` bad event `E⁽⁰⁾`
  using `μ⁽⁰⁾`-**weighted agreement of the reported oracle** `f⁽⁰⁾`, where `μ⁽⁰⁾(s) = 1` only where
  `f⁽⁰⁾(s)` matches the affine evaluation `stmt.eval x s` and `0` otherwise. High weighted agreement
  of `f⁽⁰⁾` therefore implies high unweighted agreement of the affine word `stmt.eval x`, whereas a
  prover that reports a value different from `stmt.eval x` everywhere makes `μ⁽⁰⁾ ≡ 0` and shows why
  the reverse implication can fail. The cutoffs differ as well: for `n = 2 ^ d` and
  `B = n - e - 1`, Lean's round-`0` event (`SmoothBatchRound0GapBound`, `SmoothBatchRound0Escape`,
  `¬ friSmoothBatchGoodStep ... [] π c`) tests unweighted agreement strictly above `B / n`, whereas
  the paper's `E⁽⁰⁾` uses the cutoff `max(α, √ρ · (1 + 1 / (2 * m)))` (for example, with
  `n = 16, k = 4, e = 7, α = 1 / 2, m = 3`, Lean's cutoff `8 / 16` admits nine agreeing positions
  while the paper's cutoff `7 / 12` starts at ten). Consequently, for a tuple with common agreement
  at most `B / n` (`stmt ∉ params.batchProximityLang t e`), **the Lean round-`0` event contains the
  paper's event `E⁽⁰⁾` whenever the paper's cutoff `max(α, √ρ · (1 + 1 / (2 * m)))` is at least
  `B / n`**.
* **Explicit Siegel constants and direct `η`:** The closed-form round-`0` upper bounds
  (`friSmoothBatchJohnsonRound0Bound`, `1800 * (mJ + 1) ^ 6 * (2 ^ d) ^ 2 / (ρ * |F|)`, and
  `115200 * (2 ^ d) ^ 2 / (ρ * η ^ 6 * |F|)`) are this library's original explicit Siegel finite
  bounds from `CslibFrontier/Foundations/Data/Code/ProximityGap/Curve.lean`, not the paper's
  displayed `(m + 1 / 2) ^ 7 / (3 * ρ ^ (3 / 2))` expression (not uniformly smaller at small `mJ`,
  and Eq. (1.3) uses `min(η, √ρ / 20)` whereas `smoothBatchRound0Escape_of_johnson_eta` uses `η`
  directly).
* **Whole-protocol summed IOP soundness:** Full summed interactive smooth and binary batched FRI
  soundness (in the setting of JACM Lemma 8.2 / Section 8.2.1 and Theorem 8.3) is completed in
  `CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness`; exact correspondence with the paper's
  displayed constants remains open on `#5968`.

## Main definitions

* `Cslib.Crypto.Protocols.FRI.friBatchTailTranscript`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchDoomed`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchGoodStep`,
  `Cslib.Crypto.Protocols.FRI.friBatchDoomed`,
  `Cslib.Crypto.Protocols.FRI.friBatchGoodStep`: transcript-tail projection and smooth / binary
  round-by-round doomed and good-step predicates.
* `Cslib.Crypto.Protocols.FRI.FRIBatchRound0GapBound`,
  `Cslib.Crypto.Protocols.FRI.FRIBatchRound0Escape`,
  `Cslib.Crypto.Protocols.FRI.SmoothBatchRound0GapBound`,
  `Cslib.Crypto.Protocols.FRI.SmoothBatchRound0Escape`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchJohnsonRound0Bound` (and binary counterparts
  `BatchRound0GapBound`, `BatchRound0Escape`, `friBatchJohnsonRound0Bound`): code-parameterized,
  smooth, and binary integer / `ℝ≥0∞` round-`0` unweighted affine-word escape contracts and
  explicit-constant Johnson round-`0` budget.
* `Cslib.Crypto.Protocols.FRI.friSmoothBatchRBRError` &
  `Cslib.Crypto.Protocols.FRI.friBatchRBRError`: uniform per-round escape error combining round-`0`
  batching escape `ε_batch` with `friSmoothRBRError` / `friRBRError`.

## Main results

* `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_rbrSound` &
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_rbrSound`: unconditional `IOPRoundByRoundSoundness` for
  smooth and binary batched FRI.
* `Cslib.Crypto.Protocols.FRI.uniformOfFintype_friBatchChal_map_batchCoeffs`,
  `Cslib.Crypto.Protocols.FRI.uniformOfFintype_friBatchChal_map_toFRIChal`,
  `Cslib.Crypto.Protocols.FRI.toOuterMeasure_uniform_friBatchChal_batchCoeffs`,
  `Cslib.Crypto.Protocols.FRI.toOuterMeasure_uniform_friBatchChal_toFRIChal`,
  `Cslib.Crypto.Protocols.FRI.toOuterMeasure_not_friSmoothBatchGoodStep_cons`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchQueryRound_escape_le`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitRound_escape_le_of_weightedCurveGap`: marginal
  challenge laws and 1-line smooth tail escape reductions (with binary corollaries).
* `Cslib.Crypto.Protocols.FRI.friBatchRound0Escape_of_gapBound`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchRound0_escape_le_of_escape`,
  `Cslib.Crypto.Protocols.FRI.smoothBatchRound0GapBound_of_unique`,
  `Cslib.Crypto.Protocols.FRI.smoothBatchRound0Escape_of_unique`,
  `Cslib.Crypto.Protocols.FRI.smoothBatchRound0GapBound_of_johnson_discrete`,
  `Cslib.Crypto.Protocols.FRI.smoothBatchRound0Escape_of_johnson_discrete`,
  `Cslib.Crypto.Protocols.FRI.smoothBatchRound0GapBound_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.smoothBatchRound0Escape_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.smoothBatchRound0Escape_of_johnson_eta`: unconditional round-`0`
  batching discharges across all four regimes (with binary corollaries).
* `Cslib.Crypto.Protocols.FRI.friSmoothBatchRBREscape_of_escape`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchBCS_romSoundness_bound_of_escape`,
  `FRI.friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_escape` (and binary corollaries):
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

/-! ### Section 1: Shared Tail Transcript & Smooth Batched Round-by-Round Invariant -/

section SmoothRoundByRoundInvariant

variable {F : Type} [Field F]

/-- Project a batched FRI transcript tail to the corresponding single-word FRI transcript tail
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

/-- **Smooth batched FRI round-by-round doomed-state predicate** at agreement upper bound `B : ℕ`:
* On the empty prefix `[]` (prior to sampling the round-`0` batching vector), every shared
  agreement set `D' ⊆ Fin (2 ^ d)` on which `(stmt.base, stmt.terms)` matches codewords in
  `params.initialCode` has cardinality at most `B`.
* On any non-empty prefix `(_, c₀) :: rest`, delegates directly to single-word `friSmoothDoomed` on
  the affine evaluation `stmt.eval c₀.batchCoeffs` and projected tail `friBatchTailTranscript rest`.
-/
@[expose] def friSmoothBatchDoomed [DecidableEq F] (params : FRISmoothParams F) (t B : ℕ)
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
    friSmoothDoomed params B (stmt.eval c₀.batchCoeffs) (friBatchTailTranscript rest)

/-- For `e < 2 ^ d`, the empty prefix is smooth-doomed at `B = 2 ^ d - e - 1` if and only if
`stmt ∉ params.batchProximityLang t e`. -/
theorem friSmoothBatchDoomed_nil_iff_not_mem_batchProximityLang [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) (stmt : FRIBatchStmt F params.d t) {e : ℕ}
    (he : e < 2 ^ params.d) :
    friSmoothBatchDoomed params t (2 ^ params.d - e - 1) stmt [] ↔
      stmt ∉ params.batchProximityLang t e := by
  simp only [friSmoothBatchDoomed, FRISmoothParams.batchProximityLang, Set.mem_ofPred_eq]
  refine ⟨fun h ⟨D', hge, v₀, hv₀, v, hv, hag⟩ => by have := h D' v₀ hv₀ v hv hag; omega,
    fun h D' v₀ hv₀ v hv hag => by_contra fun hgt => h ⟨D', by omega, v₀, hv₀, v, hv, hag⟩⟩

/-- **Smooth batched FRI round-by-round good-step predicate**: for active rounds
`pref.length ≤ params.m + 1`, extending `pref` by `(π, c)` preserves `friSmoothBatchDoomed`; for
unreachable lengths `params.m + 2 ≤ pref.length`, holds trivially (`True`). -/
@[expose] def friSmoothBatchGoodStep [DecidableEq F] (params : FRISmoothParams F) (t B : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (pref : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    (π : OracleTable params.d F) (c : FRIBatchChal F params.d params.q t) : Prop :=
  if pref.length ≤ params.m + 1 then
    friSmoothBatchDoomed params t B stmt (pref ++ [(π, c)])
  else
    True

/-- On the empty prefix `[]`, `friSmoothBatchGoodStep` holds at challenge `c` if and only if no
codeword `c' ∈ params.initialCode` agrees with `stmt.eval c.batchCoeffs` on more than `B`
coordinates. -/
theorem friSmoothBatchGoodStep_nil_iff [DecidableEq F] (params : FRISmoothParams F) (t B : ℕ)
    (stmt : FRIBatchStmt F params.d t) (π : OracleTable params.d F)
    (c : FRIBatchChal F params.d params.q t) :
    friSmoothBatchGoodStep params t B stmt [] π c ↔
      ∀ c' ∈ params.initialCode,
        (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
          stmt.eval c.batchCoeffs s = c' s).card ≤ B := by
  simp only [friSmoothBatchGoodStep, List.length_nil, Nat.zero_le, ↓reduceIte, List.nil_append,
    friSmoothBatchDoomed, friBatchTailTranscript_nil, friSmoothDoomed, ↓reduceDIte,
    friSmoothCommitDoomed, friSmoothTargetWord, friSmoothPreWeight, restrictOracle,
    FRISmoothParams.domainSize, friCumLog_zero, Nat.sub_zero, Fin.eta, Finset.sum_const,
    smul_eq_mul, mul_one, FRISmoothParams.initialCode]
  rfl

/-- On any non-empty prefix `(π₀, c₀) :: rest`, `friSmoothBatchGoodStep` reduces unconditionally to
single-word `friSmoothGoodStep` on `stmt.eval c₀.batchCoeffs` and `friBatchTailTranscript rest`. -/
@[simp]
theorem friSmoothBatchGoodStep_cons [DecidableEq F] (params : FRISmoothParams F) (t B : ℕ)
    (stmt : FRIBatchStmt F params.d t) (π₀ : OracleTable params.d F)
    (c₀ : FRIBatchChal F params.d params.q t)
    (rest : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    (π : OracleTable params.d F) (c : FRIBatchChal F params.d params.q t) :
    friSmoothBatchGoodStep params t B stmt ((π₀, c₀) :: rest) π c ↔
      friSmoothGoodStep params B (stmt.eval c₀.batchCoeffs)
        (friBatchTailTranscript rest) π c.toFRIChal := by
  simp only [friSmoothBatchGoodStep, List.length_cons, Nat.succ_le_succ_iff, List.cons_append,
    friSmoothBatchDoomed, friBatchTailTranscript_append, friBatchTailTranscript_cons,
    friBatchTailTranscript_nil, friSmoothGoodStep, length_friBatchTailTranscript]

/-- **Unconditional round-by-round soundness invariant for `friSmoothBatchIOP`**: for every batch
size `t : ℕ` and distance threshold `e : ℕ`, `friSmoothBatchIOP params t` satisfies
`IOPRoundByRoundSoundness` with respect to `params.batchProximityLang t e`,
`friSmoothBatchDoomed params t (2 ^ params.d - e - 1)`, and
`friSmoothBatchGoodStep params t (2 ^ params.d - e - 1)`. -/
theorem friSmoothBatchIOP_rbrSound [DecidableEq F] (params : FRISmoothParams F) (t e : ℕ) :
    IOPRoundByRoundSoundness (friSmoothBatchIOP params t) (params.batchProximityLang t e)
      (friSmoothBatchDoomed params t (2 ^ params.d - e - 1))
      (friSmoothBatchGoodStep params t (2 ^ params.d - e - 1)) where
  init_doomed stmt hnot :=
    (friSmoothBatchDoomed_nil_iff_not_mem_batchProximityLang params t stmt
      (lt_two_pow_of_not_mem_friBatchProximityLang hnot)).mpr hnot
  step_doomed stmt pref π c _ hgood := by
    by_cases h : pref.length ≤ params.m + 1
    · simpa only [friSmoothBatchGoodStep, h, ↓reduceIte] using hgood
    · cases pref with
      | nil => exact absurd (Nat.zero_le _) h
      | cons head rest =>
        simp only [List.length_cons, List.cons_append, friSmoothBatchDoomed, friSmoothDoomed,
          length_friBatchTailTranscript, List.length_append] at h ⊢
        split_ifs <;> omega
  reject_of_doomed stmt oracles chals hdoomed := by
    rw [iopVerify_friSmoothBatchIOP_eq_iopVerify_friSmoothIOP]
    rw [List.ofFn_succ] at hdoomed
    simp only [friSmoothBatchDoomed, friBatchTailTranscript, List.map_ofFn] at hdoomed
    exact (friSmoothIOP_rbrSound params e).reject_of_doomed (stmt.eval (chals 0).batchCoeffs)
      (fun j => oracles j.succ) (friTailChals chals) hdoomed

end SmoothRoundByRoundInvariant

/-! ### Section 2: Marginal Challenge Projections and Smooth Tail Escape Lifts -/

section MarginalProjectionsAndSmoothTailEscape

/-- Projecting a uniform `FRIBatchChal F d q t` onto `batchCoeffs` yields the uniform distribution
on `Fin t → F`. -/
theorem uniformOfFintype_friBatchChal_map_batchCoeffs {F : Type} [Fintype F] [Nonempty F]
    (d q t : ℕ) :
    (PMF.uniformOfFintype (FRIBatchChal F d q t)).map FRIBatchChal.batchCoeffs =
      PMF.uniformOfFintype (Fin t → F) := by
  change (PMF.uniformOfFintype (FRIBatchChal F d q t)).map
    (Prod.fst ∘ FRIBatchChal.equivProd F d q t) = _
  rw [← PMF.map_comp, PMF.uniformOfFintype_map_equiv, PMF.uniformOfFintype_prod_map_fst]

/-- Projecting a uniform `FRIBatchChal F d q t` onto `toFRIChal` yields the uniform distribution
on `FRIChal F d q`. -/
theorem uniformOfFintype_friBatchChal_map_toFRIChal {F : Type} [Fintype F] [Nonempty F]
    (d q t : ℕ) :
    (PMF.uniformOfFintype (FRIBatchChal F d q t)).map FRIBatchChal.toFRIChal =
      PMF.uniformOfFintype (FRIChal F d q) := by
  change (PMF.uniformOfFintype (FRIBatchChal F d q t)).map
    (Prod.snd ∘ FRIBatchChal.equivProd F d q t) = _
  rw [← PMF.map_comp, PMF.uniformOfFintype_map_equiv, PMF.uniformOfFintype_prod_map_snd]

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

/-- Exact reduction of any non-empty prefix escape probability in `friSmoothBatchIOP`
(`pref = (π₀, c₀) :: rest`) to the corresponding single-word `friSmoothIOP` escape probability on
`stmt.eval c₀.batchCoeffs` and `friBatchTailTranscript rest`. -/
theorem toOuterMeasure_not_friSmoothBatchGoodStep_cons [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t B : ℕ) (stmt : FRIBatchStmt F params.d t)
    (π₀ : OracleTable params.d F) (c₀ : FRIBatchChal F params.d params.q t)
    (rest : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    (π : OracleTable params.d F) :
    (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
        {c | ¬ friSmoothBatchGoodStep params t B stmt ((π₀, c₀) :: rest) π c} =
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c' | ¬ friSmoothGoodStep params B (stmt.eval c₀.batchCoeffs)
          (friBatchTailTranscript rest) π c'} := by
  simp only [friSmoothBatchGoodStep_cons]
  rw [← toOuterMeasure_uniform_friBatchChal_toFRIChal (t := t)]
  rfl

/-- **Unconditional query-round escape bound for `friSmoothBatchIOP`**: when
`pref.length = params.m + 1` and `pref` is doomed at threshold `B`, the probability over a uniform
`FRIBatchChal` that all `q` query repetitions pass is at most `(B / 2 ^ d) ^ q`. -/
theorem friSmoothBatchQueryRound_escape_le [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t B : ℕ) (stmt : FRIBatchStmt F params.d t)
    (pref : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    (hlen : pref.length = params.m + 1) (π : OracleTable params.d F)
    (hdoomed : friSmoothBatchDoomed params t B stmt pref) :
    (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
        {c | ¬ friSmoothBatchGoodStep params t B stmt pref π c} ≤
      ((B : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  cases pref with
  | nil => simp at hlen
  | cons head rest =>
    rw [toOuterMeasure_not_friSmoothBatchGoodStep_cons]
    exact friSmoothQueryRound_escape_le params B (stmt.eval head.2.batchCoeffs)
      (friBatchTailTranscript rest) (by simpa using hlen) π hdoomed

/-- **Conditional step (smooth batched folding-round escape bound assuming
`WeightedCurveGapBound`)**: for any folding round (`1 ≤ pref.length` and `pref.length ≤ params.m`)
that is doomed at threshold `B`, the escape probability over a uniform `FRIBatchChal` is at most
`B_commit / |F|`. -/
theorem friSmoothBatchCommitRound_escape_le_of_weightedCurveGap [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {B B_commit : ℕ}
    (hgap : WeightedCurveGapBound params B B_commit)
    (stmt : FRIBatchStmt F params.d t)
    (pref : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    (hpos : 1 ≤ pref.length) (hle : pref.length ≤ params.m) (π : OracleTable params.d F)
    (hdoomed : friSmoothBatchDoomed params t B stmt pref) :
    (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
        {c | ¬ friSmoothBatchGoodStep params t B stmt pref π c} ≤
      (B_commit : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  cases pref with
  | nil => simp at hpos
  | cons head rest =>
    rw [toOuterMeasure_not_friSmoothBatchGoodStep_cons]
    exact friSmoothCommitRound_escape_le_of_weightedCurveGap params hgap
      (stmt.eval head.2.batchCoeffs) (friBatchTailTranscript rest)
      (by simpa [List.length_cons] using hle) π hdoomed

end MarginalProjectionsAndSmoothTailEscape

/-! ### Section 3: Smooth Round-0 Unweighted Affine-Word Escape Contracts and Discharges -/

section SmoothRound0ContractsAndDischarges

variable {F : Type} [Field F]

/-- **Code-parameterized integer round-0 batching proximity-gap contract** relative to an initial
linear code `C : Submodule F (OracleTable d F)`: for every false tuple
`stmt ∉ friBatchProximityLang C t e`, any set `T` of batching vectors `x : Fin t → F` whose affine
evaluation `stmt.eval x` achieves unweighted agreement `> 2 ^ d - e - 1` with `C` satisfies
`|F| * #T ≤ B_batch * |F| ^ t`. -/
@[expose] def FRIBatchRound0GapBound [Fintype F] [DecidableEq F] {d : ℕ}
    (C : Submodule F (OracleTable d F)) (t e B_batch : ℕ) : Prop :=
  ∀ stmt ∉ friBatchProximityLang C t e, ∀ T : Finset (Fin t → F),
    (∀ x ∈ T, ∃ c ∈ C,
      2 ^ d - e - 1 <
        (Finset.univ.filter fun s : Fin (2 ^ d) => stmt.eval x s = c s).card) →
    Fintype.card F * T.card ≤ B_batch * Fintype.card F ^ t

theorem FRIBatchRound0GapBound.mono [Fintype F] [DecidableEq F] {d : ℕ}
    {C : Submodule F (OracleTable d F)} {t e B₁ B₂ : ℕ}
    (h : FRIBatchRound0GapBound C t e B₁) (hle : B₁ ≤ B₂) :
    FRIBatchRound0GapBound C t e B₂ :=
  fun stmt hnot T hT => (h stmt hnot T hT).trans (Nat.mul_le_mul_right _ hle)

/-- **Code-parameterized `ℝ≥0∞` round-0 batching escape contract** relative to an initial linear
code `C : Submodule F (OracleTable d F)`: for every false tuple
`stmt ∉ friBatchProximityLang C t e`, a uniformly sampled batching vector `x : Fin t → F` lands at
unweighted agreement `> 2 ^ d - e - 1` with `C` with probability at most `ε_batch`. -/
@[expose] def FRIBatchRound0Escape [Fintype F] [DecidableEq F] {d : ℕ}
    (C : Submodule F (OracleTable d F)) (t e : ℕ) (ε_batch : ℝ≥0∞) : Prop :=
  ∀ stmt ∉ friBatchProximityLang C t e,
    (PMF.uniformOfFintype (Fin t → F)).toOuterMeasure
      {x : Fin t → F | ∃ c ∈ C,
        2 ^ d - e - 1 <
          (Finset.univ.filter fun s : Fin (2 ^ d) => stmt.eval x s = c s).card} ≤ ε_batch

theorem FRIBatchRound0Escape.mono [Fintype F] [DecidableEq F] {d : ℕ}
    {C : Submodule F (OracleTable d F)} {t e : ℕ} {ε₁ ε₂ : ℝ≥0∞}
    (h : FRIBatchRound0Escape C t e ε₁) (hle : ε₁ ≤ ε₂) :
    FRIBatchRound0Escape C t e ε₂ :=
  fun stmt hnot => (h stmt hnot).trans hle

/-- Convert a code-parameterized integer `FRIBatchRound0GapBound` budget `B_batch` into
`FRIBatchRound0Escape` with escape bound `(B_batch : ℝ≥0∞) / |F|`. -/
theorem friBatchRound0Escape_of_gapBound [Fintype F] [DecidableEq F] {d : ℕ}
    (C : Submodule F (OracleTable d F)) {t e B_batch : ℕ}
    (hgap : FRIBatchRound0GapBound C t e B_batch) :
    FRIBatchRound0Escape C t e ((B_batch : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) := by
  classical
  exact fun stmt hnot => PMF.toOuterMeasure_uniformOfFintype_le_div Fintype.card_pos (by
    simpa only [Fintype.card_fun, Fintype.card_fin] using
      hgap stmt hnot _ fun _ hx => (Finset.mem_filter.mp hx).2)

/-- **Polymorphic integer smooth round-0 batching proximity-gap contract** (specialization of
`FRIBatchRound0GapBound` to `params.initialCode`). -/
abbrev SmoothBatchRound0GapBound [Fintype F] [DecidableEq F] (params : FRISmoothParams F)
    (t e B_batch : ℕ) : Prop :=
  FRIBatchRound0GapBound params.initialCode t e B_batch

/-- **Polymorphic `ℝ≥0∞` smooth round-0 batching escape contract** (specialization of
`FRIBatchRound0Escape` to `params.initialCode`). -/
abbrev SmoothBatchRound0Escape [Fintype F] [DecidableEq F] (params : FRISmoothParams F)
    (t e : ℕ) (ε_batch : ℝ≥0∞) : Prop :=
  FRIBatchRound0Escape params.initialCode t e ε_batch

/-- **Conditional step (smooth round-0 batching escape bound assuming
`SmoothBatchRound0Escape`)**: for any false tuple `stmt ∉ params.batchProximityLang t e` and any
round-`0` announcement table `π`, the probability over a uniform `FRIBatchChal` that round `0`
escapes `friSmoothBatchDoomed` is at most `ε_batch`. -/
theorem friSmoothBatchRound0_escape_le_of_escape [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e : ℕ} {ε_batch : ℝ≥0∞}
    (hescape : SmoothBatchRound0Escape params t e ε_batch)
    {stmt : FRIBatchStmt F params.d t} (hnot : stmt ∉ params.batchProximityLang t e)
    (π : OracleTable params.d F) :
    (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
        {c | ¬ friSmoothBatchGoodStep params t (2 ^ params.d - e - 1) stmt [] π c} ≤ ε_batch := by
  simp only [friSmoothBatchGoodStep_nil_iff, not_forall, not_le, exists_prop]
  exact (toOuterMeasure_uniform_friBatchChal_batchCoeffs _).trans_le (hescape stmt hnot)

omit [Field F] in
/-- Private helper: for `e < 2 ^ d`, agreement `> 2 ^ d - e - 1` is equivalent to Hamming distance
`≤ e`. -/
private theorem lt_card_filter_eq_iff_hammingDist_le [DecidableEq F] {d e : ℕ} (he : e < 2 ^ d)
    (w c : OracleTable d F) :
    2 ^ d - e - 1 < (Finset.univ.filter fun s : Fin (2 ^ d) => w s = c s).card ↔
      hammingDist w c ≤ e := by
  have htot := Fintype.card_fin (2 ^ d) ▸ card_filter_eq_add_hammingDist w c
  omega

/-- Private helper: converts any real-density affine correlated-agreement step on `params.eval 0`
into `SmoothBatchRound0Escape params t e (ENNReal.ofReal R)` via
`PMF.toOuterMeasure_uniformOfFintype_toReal`. -/
private theorem smoothBatchRound0Escape_of_real_density [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t e : ℕ) (R : ℝ → ℝ)
    (hca : Function.Injective (params.eval 0 : Fin (2 ^ params.d) → F) →
      params.dim 0 ≤ Fintype.card (Fin (2 ^ params.d)) →
      ∀ stmt : FRIBatchStmt F params.d t, ∀ T : Finset (Fin t → F),
        R (Fintype.card (Fin (2 ^ params.d)) : ℝ) <
          (T.card : ℝ) / ((Fintype.card F : ℝ) ^ t) →
        (∀ x ∈ T, ∃ c ∈ params.initialCode, hammingDist (stmt.eval x) c ≤ e) →
        ∃ D' : Finset (Fin (2 ^ params.d)),
          Fintype.card (Fin (2 ^ params.d)) - e ≤ D'.card ∧
          ∃ v₀ ∈ params.initialCode, ∃ v : Fin t → OracleTable params.d F,
            (∀ j, v j ∈ params.initialCode) ∧
            ∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s) :
    SmoothBatchRound0Escape params t e (ENNReal.ofReal (R (2 ^ params.d : ℝ))) := by
  classical
  intro stmt hnot
  have he_lt := lt_two_pow_of_not_mem_friBatchProximityLang hnot
  have hα := cosetEval_injective params.hg params.hω (Nat.zero_le params.d)
  have hk_le_n : params.dim 0 ≤ Fintype.card (Fin (2 ^ params.d)) := by
    simpa only [Fintype.card_fin, FRISmoothParams.domainSize, FRISmoothParams.cumLog,
      friCumLog_zero, Nat.sub_zero] using params.dim_le_domainSize (Nat.zero_le params.m)
  set S : Set (Fin t → F) := {x | ∃ c ∈ params.initialCode,
    2 ^ params.d - e - 1 <
      (Finset.univ.filter fun s : Fin (2 ^ params.d) => stmt.eval x s = c s).card}
  have hle_R : ((Finset.univ.filter (· ∈ S)).card : ℝ) / ((Fintype.card F : ℝ) ^ t) ≤
      R (2 ^ params.d : ℝ) := by
    by_contra hgt
    obtain ⟨D', hD'_card, v₀, hv₀, v, hv, hagree⟩ := hca hα hk_le_n stmt
      (Finset.univ.filter (· ∈ S))
      (by simpa only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using lt_of_not_ge hgt)
      fun x hx =>
        let ⟨c, hc, hc_gt⟩ := (Finset.mem_filter.mp hx).2
        ⟨c, hc, (lt_card_filter_eq_iff_hammingDist_le he_lt (stmt.eval x) c).mp hc_gt⟩
    exact hnot ⟨D', by rwa [Fintype.card_fin] at hD'_card, v₀, hv₀, v, hv, hagree⟩
  have hne_top : (PMF.uniformOfFintype (Fin t → F)).toOuterMeasure S ≠ ⊤ :=
    PMF.toOuterMeasure_uniformOfFintype S ▸
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by simp)
  rw [← ENNReal.ofReal_toReal hne_top, PMF.toOuterMeasure_uniformOfFintype_toReal]
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using ENNReal.ofReal_le_ofReal hle_R

/-- **Unconditional unique-decoding `SmoothBatchRound0GapBound`** for `(t + 1)`-word smooth batched
FRI (applying [BenSassonCarmonIshaiKoppartySaraf2020], Theorems 1.6 and 4.1). -/
theorem smoothBatchRound0GapBound_of_unique [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e : ℕ}
    (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) :
    SmoothBatchRound0GapBound params t e (2 ^ params.d) := by
  intro stmt hnot T hT_good
  by_contra hgt
  have he_lt := lt_two_pow_of_not_mem_friBatchProximityLang hnot
  obtain ⟨D', hD'_card, v₀, hv₀, v, hv, hagree, _⟩ :=
    exists_uniqueMaximal_correlatedAgreement_affine_unique (ι := Fin (2 ^ params.d))
      (cosetEval_injective params.hg params.hω (Nat.zero_le params.d))
      (by rwa [Fintype.card_fin]) stmt.base stmt.terms T
      (by rw [Fintype.card_fin]; exact Nat.lt_of_not_ge hgt)
      fun x hx => let ⟨c, hc, hgt_c⟩ := hT_good x hx
        ⟨c, hc, (lt_card_filter_eq_iff_hammingDist_le he_lt (stmt.eval x) c).mp hgt_c⟩
  exact hnot ⟨D', by rwa [Fintype.card_fin] at hD'_card, v₀, hv₀, v, hv, hagree⟩

/-- **Unconditional unique-decoding `SmoothBatchRound0Escape` upper bound** for `(t + 1)`-word
smooth batched FRI: bounds the round-`0` unweighted affine-word escape probability by
`(2 ^ params.d : ℝ≥0∞) / |F|` uniformly for all `t : ℕ` whenever
`2 * e + params.dim 0 ≤ 2 ^ d`. -/
theorem smoothBatchRound0Escape_of_unique [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e : ℕ}
    (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) :
    SmoothBatchRound0Escape params t e ((2 ^ params.d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    friBatchRound0Escape_of_gapBound params.initialCode
      (smoothBatchRound0GapBound_of_unique params t huniq)

/-- **Unconditional explicit-parameter Johnson `SmoothBatchRound0GapBound`** for `(t + 1)`-word
smooth batched FRI (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on
printed p. 6). -/
theorem smoothBatchRound0GapBound_of_johnson_discrete [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e m₀ D₀ B_batch : ℕ}
    (hm₀ : 1 ≤ m₀)
    (hk_le : params.dim 0 ≤ 2 ^ params.d - e)
    (hinterp : 2 ^ params.d * (m₀ * (m₀ + 1) / 2) <
      #(Sudan.monomials (params.dim 0 - 1) D₀))
    (hroot : D₀ < m₀ * (2 ^ params.d - e))
    (hbound : ProximityGap.johnsonCurveBound (2 ^ params.d) m₀
      (params.dim 0 - 1) D₀ 1 (2 ^ params.d) ≤ B_batch) :
    SmoothBatchRound0GapBound params t e B_batch := by
  intro stmt hnot T hT_good
  by_contra hgt
  have he_lt := lt_two_pow_of_not_mem_friBatchProximityLang hnot
  obtain ⟨D', hD'_card, v₀, hv₀, v, hv, hagree⟩ :=
    exists_correlatedAgreement_affine_johnson (ι := Fin (2 ^ params.d))
      (cosetEval_injective params.hg params.hω (Nat.zero_le params.d)) (params.one_le_dim 0) hm₀
      (by rwa [Fintype.card_fin]) (by rwa [Fintype.card_fin]) (by rwa [Fintype.card_fin])
      stmt.base stmt.terms T
      (by rw [Fintype.card_fin]
          exact (Nat.mul_le_mul_right _ hbound).trans_lt (Nat.lt_of_not_ge hgt))
      fun x hx => let ⟨c, hc, hgt_c⟩ := hT_good x hx
        ⟨c, hc, (lt_card_filter_eq_iff_hammingDist_le he_lt (stmt.eval x) c).mp hgt_c⟩
  exact hnot ⟨D', by rwa [Fintype.card_fin] at hD'_card, v₀, hv₀, v, hv, hagree⟩

/-- **Unconditional explicit-parameter Johnson `SmoothBatchRound0Escape` upper bound** for
`(t + 1)`-word smooth batched FRI. -/
theorem smoothBatchRound0Escape_of_johnson_discrete [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e m₀ D₀ B_batch : ℕ}
    (hm₀ : 1 ≤ m₀)
    (hk_le : params.dim 0 ≤ 2 ^ params.d - e)
    (hinterp : 2 ^ params.d * (m₀ * (m₀ + 1) / 2) <
      #(Sudan.monomials (params.dim 0 - 1) D₀))
    (hroot : D₀ < m₀ * (2 ^ params.d - e))
    (hbound : ProximityGap.johnsonCurveBound (2 ^ params.d) m₀
      (params.dim 0 - 1) D₀ 1 (2 ^ params.d) ≤ B_batch) :
    SmoothBatchRound0Escape params t e ((B_batch : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  friBatchRound0Escape_of_gapBound params.initialCode
    (smoothBatchRound0GapBound_of_johnson_discrete params t hm₀ hk_le hinterp hroot hbound)

/-- Explicit Siegel integer round-`0` batching budget for `(t + 1)`-word smooth FRI in the Johnson
regime with multiplicity slack `mJ`: `(1800 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3) / params.dim 0`.
-/
abbrev friSmoothBatchJohnsonRound0Bound (params : FRISmoothParams F) (mJ : ℕ) : ℕ :=
  (1800 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3) / params.dim 0

/-- **Original explicit-constant Johnson `SmoothBatchRound0GapBound`** for `(t + 1)`-word smooth
batched FRI up to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - √ρ / (2 * mJ)` (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on printed p. 6). -/
theorem smoothBatchRound0GapBound_of_johnson [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ))) :
    SmoothBatchRound0GapBound params t e (friSmoothBatchJohnsonRound0Bound params mJ) := by
  have hk₀_le_n₀ : params.dim 0 ≤ 2 ^ params.d := by
    simpa only [FRISmoothParams.domainSize, FRISmoothParams.cumLog, friCumLog_zero, Nat.sub_zero]
      using params.dim_le_domainSize (Nat.zero_le params.m)
  obtain ⟨hk_sub, hinterp, hroot, hjb⟩ := ProximityGap.johnson_line_params_bound
    (params.one_le_dim 0) hk₀_le_n₀ hmJ (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using he)
  have hmul := mul_le_mul_of_nonneg_right hjb (Nat.cast_nonneg (params.dim 0))
  have hrhs : (1800 * ((mJ + 1 : ℝ) ^ 6) * (((2 ^ params.d : ℕ) : ℝ) ^ 2) /
      ((params.dim 0 : ℝ) / ((2 ^ params.d : ℕ) : ℝ))) * (params.dim 0 : ℝ) =
      1800 * ((mJ + 1 : ℝ) ^ 6) * (((2 ^ params.d : ℕ) : ℝ) ^ 3) := by
    have := params.one_le_dim 0
    field_simp
  exact smoothBatchRound0GapBound_of_johnson_discrete params t (by omega) hk_sub hinterp hroot
    ((Nat.le_div_iff_mul_le (params.one_le_dim 0)).mpr (by exact_mod_cast hrhs ▸ hmul))

/-- **Original explicit-constant Johnson `SmoothBatchRound0Escape` upper bound** for `(t + 1)`-word
smooth batched FRI up to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - √ρ / (2 * mJ)` (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on printed p. 6). -/
theorem smoothBatchRound0Escape_of_johnson [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ))) :
    SmoothBatchRound0Escape params t e
      (ENNReal.ofReal
        (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
          (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ)))) :=
  smoothBatchRound0Escape_of_real_density params t e
    (fun N => 1800 * ((mJ + 1 : ℝ) ^ 6) * (N ^ 2) /
      (((params.dim 0 : ℝ) / N) * (Fintype.card F : ℝ)))
    fun hα hk_le_n stmt T hT hclose =>
      exists_correlatedAgreement_affine_johnson_of_multiplicity (ι := Fin (2 ^ params.d)) hα
        (params.one_le_dim 0) hk_le_n hmJ
        (by rw [Fintype.card_fin]; simpa only [Nat.cast_pow, Nat.cast_ofNat] using he)
        stmt.base stmt.terms T hT hclose

/-- **Original explicit-constant `η`-gap Johnson `SmoothBatchRound0Escape` upper bound** for
`(t + 1)`-word smooth batched FRI up to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - η` (using `η` directly rather
than `min(η, √ρ / 20)` in Eq. (1.3)). -/
theorem smoothBatchRound0Escape_of_johnson_eta [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η) :
    SmoothBatchRound0Escape params t e
      (ENNReal.ofReal
        (115200 * ((2 ^ params.d : ℝ) ^ 2) /
          (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)))) :=
  smoothBatchRound0Escape_of_real_density params t e
    (fun N => 115200 * (N ^ 2) /
      (((params.dim 0 : ℝ) / N) * (η ^ 6) * (Fintype.card F : ℝ)))
    fun hα hk_le_n stmt T hT hclose =>
      exists_correlatedAgreement_affine_johnson_of_eta (ι := Fin (2 ^ params.d)) hα
        (params.one_le_dim 0) hk_le_n hη
        (by rw [Fintype.card_fin]; simpa only [Nat.cast_pow, Nat.cast_ofNat] using he)
        stmt.base stmt.terms T hT hclose

end SmoothRound0ContractsAndDischarges

/-! ### Section 4: Conditional Smooth Uniform RBR Escape & Adaptive Two-Channel BCS ROM -/

section SmoothUniformRBRAndBCSROM

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Uniform per-round escape error for `(params.m + 2)`-round `friSmoothBatchIOP`: the maximum of
the round-`0` batching escape `ε_batch` and `friSmoothRBRError params e B_commit`. -/
@[expose] noncomputable def friSmoothBatchRBRError (params : FRISmoothParams F) (ε_batch : ℝ≥0∞)
    (e B_commit : ℕ) : ℝ≥0∞ :=
  max ε_batch (friSmoothRBRError params e B_commit)

/-- **Conditional step (uniform smooth batched FRI round-by-round escape bound assuming
`SmoothBatchRound0Escape` and `WeightedCurveGapBound`)**. -/
theorem friSmoothBatchRBREscape_of_escape (params : FRISmoothParams F) (t : ℕ) {e B_commit : ℕ}
    {ε_batch : ℝ≥0∞}
    (hbatch : SmoothBatchRound0Escape params t e ε_batch)
    (hgap : WeightedCurveGapBound params (2 ^ params.d - e - 1) B_commit) :
    ∀ stmt ∉ params.batchProximityLang t e, ∀ pref π,
      friSmoothBatchDoomed params t (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
        {c | ¬ friSmoothBatchGoodStep params t (2 ^ params.d - e - 1) stmt pref π c} ≤
      friSmoothBatchRBRError params ε_batch e B_commit := by
  intro stmt hnot pref π hdoomed
  cases pref with
  | nil =>
    exact (friSmoothBatchRound0_escape_le_of_escape params t hbatch hnot π).trans (le_max_left _ _)
  | cons head rest =>
    by_cases hle : (head :: rest).length ≤ params.m
    · exact (friSmoothBatchCommitRound_escape_le_of_weightedCurveGap params t hgap stmt
        (head :: rest) (Nat.succ_pos _) hle π hdoomed).trans
        ((le_max_left _ _).trans (le_max_right _ _))
    · by_cases heq : (head :: rest).length = params.m + 1
      · exact (friSmoothBatchQueryRound_escape_le params t (2 ^ params.d - e - 1) stmt
          (head :: rest) heq π hdoomed).trans ((le_max_right _ _).trans (le_max_right _ _))
      · have hgt : ¬ (head :: rest).length ≤ params.m + 1 := by omega
        simp only [friSmoothBatchGoodStep, hgt, ↓reduceIte, not_true_eq_false, Set.ofPred_false]
        exact (MeasureTheory.OuterMeasure.empty _).trans_le zero_le

/-- **Conditional step (adaptive two-channel BCS-FRI ROM soundness for `friSmoothBatchIOP` assuming
`SmoothBatchRound0Escape` and `WeightedCurveGapBound`)**
([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]). -/
theorem friSmoothBatchBCS_romSoundness_bound_of_escape (params : FRISmoothParams F) (t : ℕ)
    {e B_commit : ℕ} {ε_batch : ℝ≥0∞}
    (hbatch : SmoothBatchRound0Escape params t e ε_batch)
    (hgap : WeightedCurveGapBound params (2 ^ params.d - e - 1) B_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friSmoothBatchIOP params t) encSym (params.batchProximityLang t e) P)
      Q_MT) :
    bcsSoundnessGame (friSmoothBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friSmoothBatchRBRError params ε_batch e B_commit +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound (friSmoothBatchIOP_rbrSound params t e)
    (friSmoothBatchRBREscape_of_escape params t hbatch hgap) hdec 0 σ hFS hMT

/-- **Conditional step (adaptive two-channel BCS-FRI ROM soundness for `friSmoothBatchIOP` with
separate prover/verifier Merkle budgets assuming `SmoothBatchRound0Escape` and
`WeightedCurveGapBound`)** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]). -/
theorem friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_escape
    (params : FRISmoothParams F) (t : ℕ) {e B_commit : ℕ} {ε_batch : ℝ≥0∞}
    (hbatch : SmoothBatchRound0Escape params t e ε_batch)
    (hgap : WeightedCurveGapBound params (2 ^ params.d - e - 1) B_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friSmoothBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friSmoothBatchRBRError params ε_batch e B_commit +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound_of_prover_verifier (friSmoothBatchIOP_rbrSound params t e)
    (friSmoothBatchRBREscape_of_escape params t hbatch hgap) hdec 0 σ hMT hFS
    (fun x prf hmem =>
      isCostBounded_bcsMTCost_friSmoothBatchVerifyROM params t encSym x prf (hops x prf hmem))

end SmoothUniformRBRAndBCSROM

/-! ### Section 5: Binary 2-to-1 Batched FRI Definitions, Bridges, and Corollaries -/

section BinaryBatchCorollaries

variable {F : Type} [Field F]

/-- **Batched FRI round-by-round doomed-state predicate** at agreement upper bound `B : ℕ`. -/
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

/-- **Batched FRI round-by-round good-step predicate**. -/
@[expose] def friBatchGoodStep [DecidableEq F] (params : FRIParams F) (t B : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (pref : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    (π : OracleTable params.d F) (c : FRIBatchChal F params.d params.q t) : Prop :=
  if pref.length ≤ params.m + 1 then
    friBatchDoomed params t B stmt (pref ++ [(π, c)])
  else
    True

/-- **Polymorphic integer round-0 batching proximity-gap contract** (specialization of
`FRIBatchRound0GapBound` to `params.initialCode`). -/
abbrev BatchRound0GapBound [Fintype F] [DecidableEq F] (params : FRIParams F)
    (t e B_batch : ℕ) : Prop :=
  FRIBatchRound0GapBound params.initialCode t e B_batch

theorem BatchRound0GapBound.mono [Fintype F] [DecidableEq F] {params : FRIParams F}
    {t e B₁ B₂ : ℕ} (h : BatchRound0GapBound params t e B₁) (hle : B₁ ≤ B₂) :
    BatchRound0GapBound params t e B₂ :=
  FRIBatchRound0GapBound.mono h hle

/-- **Polymorphic `ℝ≥0∞` round-0 batching escape contract** (specialization of
`FRIBatchRound0Escape` to `params.initialCode`). -/
abbrev BatchRound0Escape [Fintype F] [DecidableEq F] (params : FRIParams F)
    (t e : ℕ) (ε_batch : ℝ≥0∞) : Prop :=
  FRIBatchRound0Escape params.initialCode t e ε_batch

theorem BatchRound0Escape.mono [Fintype F] [DecidableEq F] {params : FRIParams F}
    {t e : ℕ} {ε₁ ε₂ : ℝ≥0∞} (h : BatchRound0Escape params t e ε₁) (hle : ε₁ ≤ ε₂) :
    BatchRound0Escape params t e ε₂ :=
  FRIBatchRound0Escape.mono h hle

/-- Explicit Siegel integer round-`0` batching budget for `(t + 1)`-word binary FRI in the Johnson
regime with multiplicity slack `mJ`: `(1800 * (mJ + 1) ^ 6 * (2 ^ params.d) ^ 3) / params.dim 0`.
-/
abbrev friBatchJohnsonRound0Bound (params : FRIParams F) (mJ : ℕ) : ℕ :=
  friSmoothBatchJohnsonRound0Bound params.toSmooth mJ

/-- Uniform per-round escape error for `(params.m + 2)`-round `friBatchIOP`. -/
noncomputable abbrev friBatchRBRError [Fintype F] (params : FRIParams F) (ε_batch : ℝ≥0∞)
    (e B_commit : ℕ) : ℝ≥0∞ :=
  friSmoothBatchRBRError params.toSmooth ε_batch e B_commit

/-- Exact equivalence between binary `friBatchDoomed` and smooth `friSmoothBatchDoomed` at
`params.toSmooth`. -/
theorem friBatchDoomed_iff_friSmoothBatchDoomed [DecidableEq F] (params : FRIParams F) (t B : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (pref : List (OracleTable params.d F × FRIBatchChal F params.d params.q t)) :
    friBatchDoomed params t B stmt pref ↔
      friSmoothBatchDoomed params.toSmooth t B stmt pref := by
  cases pref with
  | nil => simp only [friBatchDoomed, friSmoothBatchDoomed, params.toSmooth_initialCode]
  | cons head rest =>
    exact friDoomed_iff_friSmoothDoomed params B (stmt.eval head.2.batchCoeffs)
      (friBatchTailTranscript rest)

/-- Exact equivalence between binary `friBatchGoodStep` and smooth `friSmoothBatchGoodStep` at
`params.toSmooth`. -/
theorem friBatchGoodStep_iff_friSmoothBatchGoodStep [DecidableEq F] (params : FRIParams F) (t B : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (pref : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    (π : OracleTable params.d F) (c : FRIBatchChal F params.d params.q t) :
    friBatchGoodStep params t B stmt pref π c ↔
      friSmoothBatchGoodStep params.toSmooth t B stmt pref π c := by
  simp only [friBatchGoodStep, friSmoothBatchGoodStep, friBatchDoomed_iff_friSmoothBatchDoomed]

private theorem batchRound0GapBound_iff_smooth [Fintype F] [DecidableEq F] (params : FRIParams F)
    (t e B_batch : ℕ) :
    BatchRound0GapBound params t e B_batch ↔
      SmoothBatchRound0GapBound params.toSmooth t e B_batch := by
  simp only [BatchRound0GapBound, SmoothBatchRound0GapBound, params.toSmooth_initialCode]

private theorem batchRound0Escape_iff_smooth [Fintype F] [DecidableEq F] (params : FRIParams F)
    (t e : ℕ) (ε_batch : ℝ≥0∞) :
    BatchRound0Escape params t e ε_batch ↔ SmoothBatchRound0Escape params.toSmooth t e ε_batch := by
  simp only [BatchRound0Escape, SmoothBatchRound0Escape, params.toSmooth_initialCode]

/-- For `e < 2 ^ d`, the empty prefix is doomed at `B = 2 ^ d - e - 1` if and only if
`stmt ∉ params.batchProximityLang t e`. -/
theorem friBatchDoomed_nil_iff_not_mem_batchProximityLang [DecidableEq F] (params : FRIParams F)
    (t : ℕ) (stmt : FRIBatchStmt F params.d t) {e : ℕ} (he : e < 2 ^ params.d) :
    friBatchDoomed params t (2 ^ params.d - e - 1) stmt [] ↔
      stmt ∉ params.batchProximityLang t e := by
  rw [friBatchDoomed_iff_friSmoothBatchDoomed, ← params.toSmooth_batchProximityLang]
  exact friSmoothBatchDoomed_nil_iff_not_mem_batchProximityLang params.toSmooth t stmt he

/-- On the empty prefix `[]`, `friBatchGoodStep` holds at challenge `c` if and only if no codeword
`c' ∈ params.initialCode` agrees with `stmt.eval c.batchCoeffs` on more than `B` coordinates. -/
theorem friBatchGoodStep_nil_iff [DecidableEq F] (params : FRIParams F) (t B : ℕ)
    (stmt : FRIBatchStmt F params.d t) (π : OracleTable params.d F)
    (c : FRIBatchChal F params.d params.q t) :
    friBatchGoodStep params t B stmt [] π c ↔
      ∀ c' ∈ params.initialCode,
        (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
          stmt.eval c.batchCoeffs s = c' s).card ≤ B := by
  rw [friBatchGoodStep_iff_friSmoothBatchGoodStep, ← params.toSmooth_initialCode]
  exact friSmoothBatchGoodStep_nil_iff params.toSmooth t B stmt π c

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
  rw [friBatchGoodStep_iff_friSmoothBatchGoodStep, friSmoothBatchGoodStep_cons,
    ← friGoodStep_iff_friSmoothGoodStep]

/-- **Unconditional round-by-round soundness invariant for `friBatchIOP`** (corollary of
`friSmoothBatchIOP_rbrSound`). -/
theorem friBatchIOP_rbrSound [DecidableEq F] (params : FRIParams F) (t e : ℕ) :
    IOPRoundByRoundSoundness (friBatchIOP params t) (params.batchProximityLang t e)
      (friBatchDoomed params t (2 ^ params.d - e - 1))
      (friBatchGoodStep params t (2 ^ params.d - e - 1)) where
  init_doomed stmt hnot :=
    (friBatchDoomed_iff_friSmoothBatchDoomed params t _ stmt []).mpr
      ((friSmoothBatchIOP_rbrSound params.toSmooth t e).init_doomed stmt
        (by rwa [params.toSmooth_batchProximityLang]))
  step_doomed stmt pref π c hdoom hgood :=
    (friBatchDoomed_iff_friSmoothBatchDoomed params t _ stmt _).mpr
      ((friSmoothBatchIOP_rbrSound params.toSmooth t e).step_doomed stmt pref π c
        ((friBatchDoomed_iff_friSmoothBatchDoomed params t _ stmt pref).mp hdoom)
        ((friBatchGoodStep_iff_friSmoothBatchGoodStep params t _ stmt pref π c).mp hgood))
  reject_of_doomed stmt oracles chals hdoomed := by
    rw [friBatchIOP_eq_friSmoothBatchIOP]
    exact (friSmoothBatchIOP_rbrSound params.toSmooth t e).reject_of_doomed stmt oracles chals
      ((friBatchDoomed_iff_friSmoothBatchDoomed params t _ stmt _).mp hdoomed)

/-- Exact reduction of any non-empty prefix escape probability in `friBatchIOP`
(`pref = (π₀, c₀) :: rest`) to the corresponding single-word `friIOP` escape probability. -/
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
  simp only [friBatchGoodStep_iff_friSmoothBatchGoodStep, friGoodStep_iff_friSmoothGoodStep]
  exact toOuterMeasure_not_friSmoothBatchGoodStep_cons params.toSmooth t B stmt π₀ c₀ rest π

/-- **Unconditional query-round escape bound for `friBatchIOP`** (corollary of
`friSmoothBatchQueryRound_escape_le`). -/
theorem friBatchQueryRound_escape_le [Fintype F] [DecidableEq F] (params : FRIParams F) (t B : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (pref : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    (hlen : pref.length = params.m + 1) (π : OracleTable params.d F)
    (hdoomed : friBatchDoomed params t B stmt pref) :
    (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
        {c | ¬ friBatchGoodStep params t B stmt pref π c} ≤
      ((B : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  simp only [friBatchGoodStep_iff_friSmoothBatchGoodStep]
  exact friSmoothBatchQueryRound_escape_le params.toSmooth t B stmt pref hlen π
    ((friBatchDoomed_iff_friSmoothBatchDoomed params t B stmt pref).mp hdoomed)

/-- **Conditional step (batched folding-round escape bound assuming `WeightedLineGapBound`)**
(corollary of `friSmoothBatchCommitRound_escape_le_of_weightedCurveGap`). -/
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
  simp only [friBatchGoodStep_iff_friSmoothBatchGoodStep]
  exact friSmoothBatchCommitRound_escape_le_of_weightedCurveGap params.toSmooth t
    ((weightedLineGapPerRound_iff_weightedCurveGapPerRound params B _).mp hgap) stmt pref hpos hle
    π ((friBatchDoomed_iff_friSmoothBatchDoomed params t B stmt pref).mp hdoomed)

/-- Convert an integer `BatchRound0GapBound` budget `B_batch` into `BatchRound0Escape`. -/
theorem batchRound0Escape_of_gapBound [Fintype F] [DecidableEq F] (params : FRIParams F)
    {t e B_batch : ℕ} (hgap : BatchRound0GapBound params t e B_batch) :
    BatchRound0Escape params t e ((B_batch : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  friBatchRound0Escape_of_gapBound params.initialCode hgap

/-- **Conditional step (round-0 batching escape bound assuming `BatchRound0Escape`)**. -/
theorem friBatchRound0_escape_le_of_escape [Fintype F] [DecidableEq F] (params : FRIParams F)
    (t : ℕ) {e : ℕ} {ε_batch : ℝ≥0∞} (hescape : BatchRound0Escape params t e ε_batch)
    {stmt : FRIBatchStmt F params.d t} (hnot : stmt ∉ params.batchProximityLang t e)
    (π : OracleTable params.d F) :
    (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
        {c | ¬ friBatchGoodStep params t (2 ^ params.d - e - 1) stmt [] π c} ≤ ε_batch := by
  simp only [friBatchGoodStep_iff_friSmoothBatchGoodStep]
  exact friSmoothBatchRound0_escape_le_of_escape params.toSmooth t
    ((batchRound0Escape_iff_smooth params t e ε_batch).mp hescape)
    (by rwa [params.toSmooth_batchProximityLang]) π

/-- **Unconditional unique-decoding `BatchRound0GapBound`** (corollary of
`smoothBatchRound0GapBound_of_unique`). -/
theorem batchRound0GapBound_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ}
    (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) :
    BatchRound0GapBound params t e (2 ^ params.d) :=
  (batchRound0GapBound_iff_smooth params t e _).mpr
    (smoothBatchRound0GapBound_of_unique params.toSmooth t
      (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using huniq))

/-- **Unconditional unique-decoding `BatchRound0Escape` upper bound** (corollary of
`smoothBatchRound0Escape_of_unique`). -/
theorem batchRound0Escape_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ}
    (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) :
    BatchRound0Escape params t e ((2 ^ params.d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  (batchRound0Escape_iff_smooth params t e _).mpr
    (smoothBatchRound0Escape_of_unique params.toSmooth t
      (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using huniq))

/-- **Unconditional explicit-parameter Johnson `BatchRound0GapBound`** (corollary of
`smoothBatchRound0GapBound_of_johnson_discrete`). -/
theorem batchRound0GapBound_of_johnson_discrete [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e m₀ D₀ B_batch : ℕ}
    (hm₀ : 1 ≤ m₀)
    (hk_le : params.dim 0 ≤ 2 ^ params.d - e)
    (hinterp : 2 ^ params.d * (m₀ * (m₀ + 1) / 2) <
      #(Sudan.monomials (params.dim 0 - 1) D₀))
    (hroot : D₀ < m₀ * (2 ^ params.d - e))
    (hbound : ProximityGap.johnsonCurveBound (2 ^ params.d) m₀
      (params.dim 0 - 1) D₀ 1 (2 ^ params.d) ≤ B_batch) :
    BatchRound0GapBound params t e B_batch :=
  (batchRound0GapBound_iff_smooth params t e B_batch).mpr
    (smoothBatchRound0GapBound_of_johnson_discrete params.toSmooth t hm₀
      (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using hk_le)
      (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using hinterp)
      hroot
      (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using hbound))

/-- **Unconditional explicit-parameter Johnson `BatchRound0Escape` upper bound** (corollary of
`smoothBatchRound0Escape_of_johnson_discrete`). -/
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

/-- **Original explicit-constant Johnson `BatchRound0GapBound`** (corollary of
`smoothBatchRound0GapBound_of_johnson`). -/
theorem batchRound0GapBound_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ))) :
    BatchRound0GapBound params t e (friBatchJohnsonRound0Bound params mJ) := by
  rw [batchRound0GapBound_iff_smooth]
  exact smoothBatchRound0GapBound_of_johnson params.toSmooth t hmJ
    (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using he)

/-- **Original explicit-constant Johnson `BatchRound0Escape` upper bound** (corollary of
`smoothBatchRound0Escape_of_johnson`). -/
theorem batchRound0Escape_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ))) :
    BatchRound0Escape params t e
      (ENNReal.ofReal
        (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
          (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ)))) := by
  simpa only [batchRound0Escape_iff_smooth, params.toSmooth_dim (Nat.zero_le _)] using
    smoothBatchRound0Escape_of_johnson params.toSmooth t hmJ
      (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using he)

/-- **Original explicit-constant `η`-gap Johnson `BatchRound0Escape` upper bound** (corollary of
`smoothBatchRound0Escape_of_johnson_eta`). -/
theorem batchRound0Escape_of_johnson_eta [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η) :
    BatchRound0Escape params t e
      (ENNReal.ofReal
        (115200 * ((2 ^ params.d : ℝ) ^ 2) /
          (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)))) := by
  simpa only [batchRound0Escape_iff_smooth, params.toSmooth_dim (Nat.zero_le _)] using
    smoothBatchRound0Escape_of_johnson_eta params.toSmooth t hη
      (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using he)

/-- **Conditional step (uniform batched FRI round-by-round escape bound assuming `BatchRound0Escape`
and `WeightedLineGapBound`)** (corollary of `friSmoothBatchRBREscape_of_escape`). -/
theorem friBatchRBREscape_of_escape [Fintype F] [DecidableEq F] (params : FRIParams F) (t : ℕ)
    {e B_commit : ℕ} {ε_batch : ℝ≥0∞}
    (hbatch : BatchRound0Escape params t e ε_batch)
    (hgap : WeightedLineGapBound params (2 ^ params.d - e - 1) B_commit) :
    ∀ stmt ∉ params.batchProximityLang t e, ∀ pref π,
      friBatchDoomed params t (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
        {c | ¬ friBatchGoodStep params t (2 ^ params.d - e - 1) stmt pref π c} ≤
      friBatchRBRError params ε_batch e B_commit := by
  intro stmt hnot pref π hdoomed
  simp only [friBatchGoodStep_iff_friSmoothBatchGoodStep]
  exact friSmoothBatchRBREscape_of_escape params.toSmooth t
    ((batchRound0Escape_iff_smooth params t e ε_batch).mp hbatch)
    ((weightedLineGapPerRound_iff_weightedCurveGapPerRound params _ _).mp hgap)
    stmt (by rwa [params.toSmooth_batchProximityLang]) pref π
    ((friBatchDoomed_iff_friSmoothBatchDoomed params t _ stmt pref).mp hdoomed)

/-- **Conditional step (adaptive two-channel BCS-FRI ROM soundness for `friBatchIOP` assuming
`BatchRound0Escape` and `WeightedLineGapBound`)** (corollary of
`friSmoothBatchBCS_romSoundness_bound_of_escape`). -/
theorem friBatchBCS_romSoundness_bound_of_escape [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e B_commit : ℕ} {ε_batch : ℝ≥0∞}
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
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [friBatchIOP_eq_friSmoothBatchIOP, ← params.toSmooth_batchProximityLang] at hMT ⊢
  exact friSmoothBatchBCS_romSoundness_bound_of_escape params.toSmooth t
    ((batchRound0Escape_iff_smooth params t e ε_batch).mp hbatch)
    ((weightedLineGapPerRound_iff_weightedCurveGapPerRound params _ _).mp hgap) hdec σ hFS hMT

/-- **Conditional step (adaptive two-channel BCS-FRI ROM soundness for `friBatchIOP` with separate
prover/verifier Merkle budgets assuming `BatchRound0Escape` and `WeightedLineGapBound`)**
(corollary of `friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_escape`). -/
theorem friBatchBCS_romSoundness_bound_of_prover_verifier_of_escape [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e B_commit : ℕ} {ε_batch : ℝ≥0∞}
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
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [friBatchIOP_eq_friSmoothBatchIOP, ← params.toSmooth_batchProximityLang,
    ← params.toSmooth_proofOracleQueries]
  exact friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_escape params.toSmooth t
    ((batchRound0Escape_iff_smooth params t e ε_batch).mp hbatch)
    ((weightedLineGapPerRound_iff_weightedCurveGapPerRound params _ _).mp hgap) hdec σ hMT hFS hops

end BinaryBatchCorollaries

end Cslib.Crypto.Protocols.FRI
