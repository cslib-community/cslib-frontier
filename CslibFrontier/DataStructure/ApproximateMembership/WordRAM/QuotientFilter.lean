/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.ApproximateMembership.QuotientFilter.Probability
public import CslibFrontier.DataStructure.ApproximateMembership.WordRAM.QuotientFilter.Code
public import CslibFrontier.DataStructure.WordRAM.Randomized.ObliviousSequence
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Tactic.FinIndex
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.SuppCases
import CslibFrontier.Tactic.WramOmega

/-!
# Word-RAM Implementation of the Two-Stage Quotient Filter

This module packages the bit-packed two-stage quotient filter into a reusable
`Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl` certificate realizing
`Cslib.DataStructure.ApproximateMembership.spec U n ε` on the Word-RAM without any universe-to-table
restriction `log₂ U ≤ c · log₂ n`. Keys fit in half a word: every certificate assumes `U ≤ 2 ^ w₀`
with `0 < w₀` and `2 * w₀ ≤ w`.

## Architecture

1. **Deterministic branch-wise transcript (`simResult`, `simTranscript`):**
   Because runs are maintained in canonical sorted order, on each fixed random seed
   `p : FilterSeed w₀ n` the active slot configuration depends only on the current active set
   `S : Finset (Fin U)`. Every query on seed `p` deterministically returns
   `decide (remHash U w₀ k p.2 u ∈ bucketRun S (quotHash U w₀ n p.1) (remHash U w₀ k p.2) _)`.
   Hence zero false negatives hold on every random branch, and the false-positive event at query
   index `idx` is bounded by `(1 / 2 : ℝ≥0∞) ^ k ≤ ε`.
2. **Expected `O(1)` time per operation (`charge = opStepBound 290`):**
   Evaluating the two-stage quotient hash and the independent remainder hash takes at most
   `236841 + 45 = 236886` instructions, and the `Memory.Prog` cluster operation lowered via the
   `realize` tactic (`realizes_clusterOp.code`) executes in at most
   `19 + clusterFactor * (11 * ℓ + 14)` instructions for a cluster of length `ℓ`. By
   `tsum_seedClusterBound_le` (`𝔼[ℓ] ≤ 290`), the expected instruction count of every operation is
   at most `charge = opStepBound 290`.
3. **Compact space (`space_le`, `implOfEps_space_le`):**
   The single contiguous memory block of `space w w₀ n k` words stores the two-stage quotient seed,
   the `o(n)`-bit Four-Russians carryless multiplication table, the remainder seed, and the four
   bit-packed slot arrays (`isFull`, `isOcc`, `isRunStart`, `remAt`), totaling at most
   `640 * ((n * k + w - 1) / w + 1)` words.

## Main definitions

* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.subroutineCode`:
  Word-RAM `SubroutineCode .exact rQF 0` for the quotient filter.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.impl`,
  `Cslib.DataStructure.ApproximateMembership.QuotientFilter.implStandard`:
  `ObliviousSequenceImpl` certificates realizing `spec U n ((1 / 2 : ℝ≥0∞) ^ k)`.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.implOfEps`,
  `Cslib.DataStructure.ApproximateMembership.QuotientFilter.implOfEpsStandard`:
  `ObliviousSequenceImpl` certificates realizing `spec U n ε` for any `ε ≠ 0` using
  `k = epsLog ε = max 1 ⌈log₂(1 / ε)⌉`.

## Main results

* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.quotBits_lt_w_of_fits_space`:
  `quotBits w₀ n < w` holds automatically whenever `0 < w₀`, `2 * w₀ ≤ w`, and
  `Fits w (base + space w w₀ n k)`.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.contract_map_simTranscript`:
  `simTranscript` under `filterSeedLaw w₀ n` satisfies `spec U n ((1 / 2 : ℝ≥0∞) ^ k).Contract ops`.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.opCode_execWithin`:
  single-operation deterministic execution and invariant preservation on each seed `p`.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.implOfEps_space_le`:
  word-space bound `≤ 640 * ((n * epsLog ε + w - 1) / w + 1)`.

## References

* [A. Pagh, R. Pagh and S. S. Rao, *An optimal Bloom filter replacement*][PaghPaghRao2005]
* [M. A. Bender, M. Farach-Colton, R. Johnson, R. Kraner, B. C. Kuszmaul, D. Medjedovic, P. Montes,
  P. Shetty, R. P. Spillane and E. Zadok, *Don't thrash: how to cache your hash on
  flash*][BenderEtAl2012]
-/

public section

namespace Cslib.DataStructure.ApproximateMembership.QuotientFilter

open Cslib.WordRAM Cslib.DataStructure.WordRAM.Randomized Cslib.Probability
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.LinearProbing
open scoped ENNReal BigOperators Finset

attribute [local wram_arith] ReducedKWise.seedWords ReducedKWise.tableWords
  ReducedKWise.space ReducedKWise.tabBase ReducedKWise.coeffLimbAddr

/-! ## Section 1: Derived word-width bounds and representation invariant `Rep` -/

/-- Whenever `0 < w₀`, `2 * w₀ ≤ w`, and `Fits w (base + space w w₀ n k)`, the Four-Russians double
limb width `2 * reducedChunkBits` is strictly less than `w`. -/
theorem two_mul_reducedChunkBits_lt_of_fits_space {base w w₀ n k : ℕ}
    (hw₀ : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit : Fits w (base + space w w₀ n k)) :
    2 * reducedChunkBits (reducedTrinomialStep w₀ (quotBits w₀ n) (quotBits w₀ n)) < w := by
  have hb_lt := quotBits_lt_w_of_fits_space hw₀ hw hfit
  have hc_le :=
    two_mul_reducedChunkBits_le (b := quotBits w₀ n) (by omega : w₀ ≤ w) hb_lt.le (by omega)
  have hsp_le : ReducedKWise.space w w₀ (quotBits w₀ n) (quotBits w₀ n) 5 ≤ space w w₀ n k := by
    wram_omega
  exact ReducedKWise.two_mul_reducedChunkBits_lt_of_fits_space (base := base) (k := 5) hc_le
    (by fits [hsp_le])

/-- `ReducedKWise.TableRep` depends only on memory below `base + ReducedKWise.space`. -/
theorem tableRep_congr {base w w₀ b b' k : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (h : ∀ a < base + ReducedKWise.space w w₀ b b' k, mem₁ a = mem₂ a) :
    ReducedKWise.TableRep base w w₀ b b' k mem₁ ↔
      ReducedKWise.TableRep base w w₀ b b' k mem₂ := by
  dsimp only [ReducedKWise.TableRep]
  refine and_congr (forall₂_congr fun wIdx hwIdx => ?_) (forall₂_congr fun idx hidx => ?_)
  · rw [h _ (by wram_omega)]
  · rw [h _ (by wram_omega [shiftRight_lt_reducedTableWords (w := w) hidx])]

/-- `ReducedKWise.SeedRep` depends only on memory below `base + ReducedKWise.space`. -/
theorem seedRep_congr {base w w₀ b b' k : ℕ} (θ : ReducedPolySeed w₀ b b' k)
    {mem₁ mem₂ : ℕ → ℕ}
    (h : ∀ a < base + ReducedKWise.space w w₀ b b' k, mem₁ a = mem₂ a) :
    ReducedKWise.SeedRep base w₀ b b' k θ mem₁ ↔
      ReducedKWise.SeedRep base w₀ b b' k θ mem₂ := by
  dsimp only [ReducedKWise.SeedRep]
  refine and_congr (by rw [h base (by wram_omega)]) (forall₂_congr fun j m => ?_)
  have hlt : m.val + reducedLimbCount (reducedTrinomialStep w₀ b b') * j.val <
      k * reducedLimbCount (reducedTrinomialStep w₀ b b') := by
    have := Nat.mul_le_mul_right (reducedLimbCount (reducedTrinomialStep w₀ b b')) j.isLt
    have := m.isLt
    linarith
  rw [h _ (by wram_omega [hlt])]

/-- Seed-coupled Word-RAM representation invariant linking seed `p : FilterSeed w₀ n`, active key
set `S : Finset (Fin U)`, and machine state `x : Data rQF`. -/
@[expose] def Rep (U w base w₀ n k : ℕ) (p : FilterSeed w₀ n) (S : Finset (Fin U))
    (x : Data rQF) : Prop :=
  x.Bounded w ∧
  x.regs (qfReg 0) = base ∧
  x.regs (qfReg 240) = base + space w w₀ n k ∧
  ReducedKWise.TableRep base w w₀ (quotBits w₀ n) (quotBits w₀ n) 5 x.mem ∧
  ReducedKWise.SeedRep base w₀ (quotBits w₀ n) (quotBits w₀ n) 5 p.1 x.mem ∧
  x.mem (remSeedAddr base w w₀ n) = p.2.val ∧
  FilterInv n S (quotHash U w₀ n p.1) (remHash U w₀ k p.2)
    (extractFilterState base w w₀ n k x.mem)

/-! ## Section 2: Deterministic branch-wise transcript (`simResult`, `simTranscript`) -/

/-- Deterministic branch-wise result of operation `o : Op U` on seed `p : FilterSeed w₀ n` from
active key set `S : Finset (Fin U)`. -/
@[expose] noncomputable def simResult (U w₀ n k : ℕ) (p : FilterSeed w₀ n)
    (S : Finset (Fin U)) : (o : Op U) → Result o
  | .insert _ => PUnit.unit
  | .delete _ => PUnit.unit
  | .query u =>
      decide (remHash U w₀ k p.2 u ∈
        bucketRun S (quotHash U w₀ n p.1) (remHash U w₀ k p.2) (quotHash U w₀ n p.1 u))

/-- Deterministic branch-wise transcript produced across `ops : List (Op U)` on seed
`p : FilterSeed w₀ n` starting from active key set `S : Finset (Fin U)`. -/
@[expose] noncomputable def simTranscript (U w₀ n k : ℕ) (p : FilterSeed w₀ n) :
    Finset (Fin U) → List (Op U) → List (Label U)
  | _, [] => []
  | S, o :: rest =>
      ⟨o, simResult U w₀ n k p S o⟩ :: simTranscript U w₀ n k p (stepSet S o) rest

@[simp]
theorem simTranscript_nil (U w₀ n k : ℕ) (p : FilterSeed w₀ n) (S : Finset (Fin U)) :
    simTranscript U w₀ n k p S [] = [] := rfl

@[simp]
theorem simTranscript_cons (U w₀ n k : ℕ) (p : FilterSeed w₀ n) (S : Finset (Fin U))
    (o : Op U) (rest : List (Op U)) :
    simTranscript U w₀ n k p S (o :: rest) =
      ⟨o, simResult U w₀ n k p S o⟩ :: simTranscript U w₀ n k p (stepSet S o) rest := rfl

theorem simTranscript_append (U w₀ n k : ℕ) (p : FilterSeed w₀ n)
    (S : Finset (Fin U)) (ops₁ ops₂ : List (Op U)) :
    simTranscript U w₀ n k p S (ops₁ ++ ops₂) =
      simTranscript U w₀ n k p S ops₁ ++
        simTranscript U w₀ n k p (activeSetFrom S ops₁) ops₂ := by
  induction ops₁ generalizing S with
  | nil => simp
  | cons o rest ih =>
    simp only [List.cons_append, simTranscript_cons, activeSetFrom_cons, ih (stepSet S o)]

theorem transcriptMatches_simTranscript (U w₀ n k : ℕ) (p : FilterSeed w₀ n)
    (S : Finset (Fin U)) (ops : List (Op U)) :
    TranscriptMatches ops (simTranscript U w₀ n k p S ops) := by
  induction ops generalizing S with
  | nil => rfl
  | cons o rest ih =>
    simp only [simTranscript_cons, Cslib.DataStructure.transcriptMatches_cons]
    exact ih (stepSet S o)

theorem getElem?_simTranscript (U w₀ n k : ℕ) (p : FilterSeed w₀ n)
    (S : Finset (Fin U)) (ops : List (Op U)) (idx : ℕ) :
    (simTranscript U w₀ n k p S ops)[idx]? =
      ops[idx]?.map fun o =>
        ⟨o, simResult U w₀ n k p (activeSetFrom S (ops.take idx)) o⟩ := by
  induction ops generalizing S idx with
  | nil => simp
  | cons o rest ih =>
    cases idx with
    | zero => simp
    | succ idx =>
      simp only [simTranscript_cons, List.getElem?_cons_succ, List.take_succ_cons,
        activeSetFrom_cons, ih (stepSet S o) idx]

private theorem simTranscript_query_eq_true_iff {U w₀ n k : ℕ} (p : FilterSeed w₀ n)
    {ops : List (Op U)} {idx : ℕ} {u : Fin U} (hq : ops[idx]? = some (.query u)) :
    (simTranscript U w₀ n k p ∅ ops)[idx]? = some ⟨.query u, true⟩ ↔
      ∃ x ∈ activeSetBefore ops idx,
        quotHash U w₀ n p.1 x = quotHash U w₀ n p.1 u ∧
        remHash U w₀ k p.2 x = remHash U w₀ k p.2 u := by
  rw [getElem?_simTranscript, hq]
  simp only [Option.map_some, Option.some.injEq, Sigma.mk.injEq, true_and, heq_eq_eq,
    simResult, activeSetBefore, decide_eq_true_eq]
  exact mem_bucketRun_iff _ _ _ _ _

theorem noFalseNegatives_simTranscript (U w₀ n k : ℕ) (p : FilterSeed w₀ n)
    (ops : List (Op U)) :
    NoFalseNegatives ops (simTranscript U w₀ n k p ∅ ops) :=
  fun _ _ u hq hu => (simTranscript_query_eq_true_iff p hq).mpr ⟨u, hu, rfl, rfl⟩

theorem falsePositiveAt_simTranscript_iff (U w₀ n k : ℕ) (p : FilterSeed w₀ n)
    (ops : List (Op U)) {idx : ℕ} {u : Fin U}
    (hq : ops[idx]? = some (.query u)) :
    FalsePositiveAt (simTranscript U w₀ n k p ∅ ops) idx u ↔
      ∃ x ∈ activeSetBefore ops idx,
        quotHash U w₀ n p.1 x = quotHash U w₀ n p.1 u ∧
        remHash U w₀ k p.2 x = remHash U w₀ k p.2 u :=
  simTranscript_query_eq_true_iff p hq

/-- The transcript distribution induced by `simTranscript` under `filterSeedLaw w₀ n` satisfies
`(spec U n ((1 / 2 : ℝ≥0∞) ^ k)).Contract ops`. -/
theorem contract_map_simTranscript {U w₀ n k : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {ops : List (Op U)} (hv : ValidOpSeq n ops) :
    (spec U n ((1 / 2 : ℝ≥0∞) ^ k)).Contract ops
      ((filterSeedLaw w₀ n).map fun p => simTranscript U w₀ n k p ∅ ops) := by
  refine ⟨fun tr htr => ?_, fun idx _ u hq hnotMem => ?_⟩
  · supp_cases htr with ⟨p, -, rfl⟩
    exact ⟨transcriptMatches_simTranscript U w₀ n k p ∅ ops,
      noFalseNegatives_simTranscript U w₀ n k p ops⟩
  · rw [PMF.toOuterMeasure_map_apply]
    convert toOuterMeasure_falsePositive_le hw₀ hU (card_activeSetBefore_le hv idx) hnotMem using 2
    ext p
    exact falsePositiveAt_simTranscript_iff U w₀ n k p ops hq

/-! ## Section 3: Initialization (`allocSpan`, `initSetup`, `initSetup_exec`) -/

/-- Allocate `[base, base + space w w₀ n k)` by setting `qfReg 0 ← qfReg 240` and advancing
`qfReg 240 ← qfReg 0 + space w w₀ n k` in `3` instructions. -/
@[expose] noncomputable def allocSpan (w w₀ n k : ℕ) : Code .exact rQF :=
  .seq (.op (.copy (qfReg 0) (qfReg 240)))
  (.seq (.op (.const (qfReg 30) (space w w₀ n k)))
        (.op (.exactBin .add (qfReg 240) (qfReg 0) (qfReg 30))))

theorem allocSpan_execWithin {base w w₀ n k : ℕ}
    (hfit_space : Fits w (base + space w w₀ n k))
    {x : Data rQF} (hfr : x.regs (qfReg 240) = base) :
    ∃ x₁ : Data rQF,
      ExecWithin w (allocSpan w w₀ n k) x x₁ 3 ∧
      x₁.mem = x.mem ∧
      x₁.regs (qfReg 0) = base ∧
      x₁.regs (qfReg 240) = base + space w w₀ n k := by
  unfold allocSpan
  wram_exec [hfr]
  exact ⟨rfl, by wram_simp, by wram_simp⟩

/-- Initialize the Four-Russians carryless multiplication table, sample the two-stage quotient seed,
and sample the multiply-shift remainder seed. -/
@[expose] noncomputable def initSetup (w w₀ n : ℕ) : Code .exact rQF :=
  let b := quotBits w₀ n
  .seq ((ReducedKWise.initTableCode w w₀ b b 5).rename kwiseMap)
  (.seq ((ReducedKWise.resampleCode w₀ b b 5).rename kwiseMap)
        (remInitCode w w₀ n))

/-- Exact instruction count of `initSetup w w₀ n`. -/
@[expose] def setupSteps (w₀ n : ℕ) : ℕ :=
  let b := quotBits w₀ n
  ReducedKWise.initTableSteps w₀ b b + (ReducedKWise.resampleSteps w₀ b b 5 + 5)

/-- Combined `ProbComp` semantics for sampling the quotient seed and the remainder seed. -/
@[expose] noncomputable def sampleSeedsComp (base w w₀ n : ℕ) (x₂ : Data rQF) :
    ProbComp (Data rQF × ℕ) := do
  let b := quotBits w₀ n
  let z1 ← ReducedKWise.resampleComp base w₀ b b 5 (x₂.comap kwiseMap)
  let x₃ := z1.1.extend kwiseMap x₂
  let z2 ← remInitComp base w w₀ n x₃
  pure (z2.1, z1.2 + z2.2)

theorem extractSeed_remInitData (base w w₀ n : ℕ) (x : Data rQF) (γ : ℕ) :
    ReducedKWise.extractSeed base w₀ (quotBits w₀ n) (quotBits w₀ n) 5
      (remInitData base w w₀ n x γ).mem =
    ReducedKWise.extractSeed base w₀ (quotBits w₀ n) (quotBits w₀ n) 5 x.mem := by
  have hmem (a : ℕ) (ha : a ≠ remSeedAddr base w w₀ n) :
      (remInitData base w w₀ n x γ).mem a = x.mem a :=
    Function.update_of_ne ha _ _
  have hslice (a c m : ℕ) (hm : a + m ≤ remSeedAddr base w w₀ n) :
      Tabulation.extractSlice a c m (remInitData base w w₀ n x γ).mem =
        Tabulation.extractSlice a c m x.mem := by
    funext idx; simp only [Tabulation.extractSlice]
    rw [hmem _ (by have := idx.isLt; omega)]
  dsimp only [ReducedKWise.extractSeed]
  refine Prod.ext (by
    dsimp only [ReducedKWise.extractTop]
    exact congrArg _ (hslice base (w₀ - 1) 1 (by wram_omega))) (by
    dsimp only [ReducedKWise.extractBot]
    exact congrArg _ (hslice (base + 1) _ _ (by wram_omega)))

theorem map_extractFilterSeed_eval_sampleSeedsComp (base w w₀ n : ℕ) (x₂ : Data rQF) :
    ((sampleSeedsComp base w w₀ n x₂).eval).map
      (fun z => extractFilterSeed base w w₀ n z.1.mem) =
      filterSeedLaw w₀ n := by
  set b := quotBits w₀ n
  dsimp only [sampleSeedsComp]
  rw [ProbComp.eval_bind, PMF.map_bind]
  trans ((ReducedKWise.resampleComp base w₀ b b 5 (x₂.comap kwiseMap)).eval.map
      fun z1 => ReducedKWise.extractSeed base w₀ b b 5 z1.1.mem).bind
      fun θ => (PMF.uniformOfFintype (RemSeed w₀)).map (θ, ·)
  · rw [PMF.bind_map]
    congr 1 with z1 : 1
    dsimp only [Function.comp_apply]
    rw [bind_pure_comp, ProbComp.eval_map, PMF.map_comp,
      ← map_extractRemSeed_eval_remInitComp base w w₀ n (z1.1.extend kwiseMap x₂), PMF.map_comp]
    refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun z2 hz2 => ?_
    supp_cases hz2 [remInitComp] with ⟨γ, rfl⟩
    exact Prod.ext (extractSeed_remInitData base w w₀ n _ γ.val) rfl
  · rw [ReducedKWise.map_extractSeed_eval_resampleComp, filterSeedLaw, PMF.uniformOfFintype_prod]

theorem initSetup_exec {U base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w)
    (hfit_space : Fits w (base + space w w₀ n k))
    {x₁ : Data rQF}
    (hx₁ : x₁.Bounded w) (hb : x₁.regs (qfReg 0) = base)
    (hfr : x₁.regs (qfReg 240) = base + space w w₀ n k)
    (hzero : ∀ a ∈ (Block.mk base (space w w₀ n k)).footprint, x₁.mem a = 0) :
    ∃ ν₀ : PMF (LatentState (FilterSeed w₀ n) rQF),
      ExecCodeDist w (initSetup w w₀ n) x₁ (ν₀.map LatentState.data) (setupSteps w₀ n) ∧
      (ν₀.map LatentState.latent = filterSeedLaw w₀ n ∧
        ∀ t ∈ ν₀.support, Rep U w base w₀ n k t.latent ∅ t.data) ∧
      ∀ t ∈ ν₀.support,
        t.data.Bounded w ∧
        t.data.regs (qfReg 240) = base + space w w₀ n k ∧
        Modifies (Block.mk base (space w w₀ n k)).footprint x₁.mem t.data.mem := by
  let b := quotBits w₀ n
  have hc_lt := two_mul_reducedChunkBits_lt_of_fits_space hw₀_pos hw hfit_space
  have hfit_kwise : Fits w (base + ReducedKWise.space w w₀ b b 5) := by
    have : ReducedKWise.space w w₀ b b 5 ≤ space w w₀ n k := by wram_omega
    fits [this]
  obtain ⟨y_tab, he_tab_inner, hy_tab_0, htab, hframe_tab⟩ :=
    ReducedKWise.initTableCode_exec (k := 5) (x := x₁.comap kwiseMap) hb hc_lt.le hfit_kwise
  have he_tab := he_tab_inner.rename injective_kwiseMap
  set x₂ := y_tab.extend kwiseMap x₁
  have hx₂_0 : (x₂.comap kwiseMap).regs 0 = base := by
    rwa [Data.comap_extend injective_kwiseMap]
  have hx₂_fr : x₂.regs (qfReg 240) = base + space w w₀ n k := by
    rwa [extend_kwiseMap_regs (by decide : 240 ≤ (qfReg 240).val)]
  have he_res := (ReducedKWise.resampleCode_execRand (base := base) (w := w) (w₀ := w₀)
    (b := b) (b' := b) (k := 5) (x := x₂.comap kwiseMap) hx₂_0 (by omega) hc_lt.le
    hfit_kwise).rename injective_kwiseMap
  have he_seeds : ExecRand w
      (.seq ((ReducedKWise.resampleCode w₀ b b 5).rename kwiseMap) (remInitCode w w₀ n))
      x₂ (sampleSeedsComp base w w₀ n x₂) := by
    have hseq := ExecRand.seq (m₂ := remInitComp base w w₀ n) he_res fun x₃ hx₃ => by
      supp_cases hx₃ with ⟨z1, hz1, rfl⟩
      have hz1_0 := (ReducedKWise.mem_support_resampleComp hx₂_0 htab hz1).1
      refine remInitCode_execRand (by omega) hfit_space ?_
      change ((z1.1.extend kwiseMap x₂).comap kwiseMap).regs 0 = base
      rwa [Data.comap_extend injective_kwiseMap]
    simpa only [sampleSeedsComp, bind_assoc, pure_bind, map_eq_bind_pure_comp,
      Function.comp_def] using hseq
  have hsupp : ∀ z ∈ (sampleSeedsComp base w w₀ n x₂).support,
      z.1.Bounded w ∧
      z.1.regs (qfReg 240) = base + space w w₀ n k ∧
      Rep U w base w₀ n k (extractFilterSeed base w w₀ n z.1.mem) ∅ z.1 ∧
      Modifies (Block.mk base (space w w₀ n k)).footprint x₁.mem z.1.mem ∧
      z.2 ≤ ReducedKWise.resampleSteps w₀ b b 5 + 5 := by
    intro z hz
    have hbdd_z := he_seeds.bounded (he_tab.within.bounded hx₁) hz
    supp_cases hz [sampleSeedsComp, remInitComp] with ⟨z1, hz1, _, ⟨γ, rfl⟩, rfl⟩
    obtain ⟨hz1_0, htab1, hseed1, hframe1, hsteps1⟩ :=
      ReducedKWise.mem_support_resampleComp hx₂_0 htab hz1
    set y := remInitData base w w₀ n (z1.1.extend kwiseMap x₂) γ.val
    have hmem_outside (a : ℕ) (ha : a < base ∨ fullBase base w w₀ n ≤ a) :
        y.mem a = x₁.mem a := by
      have hne : a ≠ remSeedAddr base w w₀ n := by rcases ha with h | h <;> wram_omega [h]
      rw [show y.mem a = z1.1.mem a from Function.update_of_ne hne _ _]
      exact (hframe1 a (ha.imp_right fun h => by wram_omega [h])).trans
        (hframe_tab a (ha.imp (fun h => by wram_omega [h]) (fun h => by wram_omega [h])))
    have hmem_below : ∀ a < base + ReducedKWise.space w w₀ b b 5, y.mem a = z1.1.mem a :=
      fun a ha => Function.update_of_ne (by wram_omega [ha]) _ _
    have hy_0 : y.regs (qfReg 0) = base := by
      wram_simp [y, remInitData]
      change ((z1.1.extend kwiseMap x₂).comap kwiseMap).regs 0 = base
      rwa [Data.comap_extend injective_kwiseMap]
    have hy_fr : y.regs (qfReg 240) = base + space w w₀ n k := by
      wram_simp [y, remInitData]
      rwa [extend_kwiseMap_regs (by decide : 240 ≤ (qfReg 240).val)]
    have hrem_y : y.mem (remSeedAddr base w w₀ n) = (extractRemSeed base w w₀ n y.mem).val := by
      have hγ : γ.val < 2 ^ (w₀ - 1) := by
        have := γ.isLt; have := Nat.one_le_two_pow (n := w₀ - 1); omega
      simp [extractRemSeed, y, remInitData, Data.write, Data.set, Cslib.WordRAM.wordOfNat, hγ]
    have hinv_y : FilterInv n (∅ : Finset (Fin U))
        (quotHash U w₀ n (extractFilterSeed base w w₀ n y.mem).1)
        (remHash U w₀ k (extractFilterSeed base w w₀ n y.mem).2)
        (extractFilterState base w w₀ n k y.mem) := by
      rw [extractFilterState_of_zero fun a hle hlt =>
        (hmem_outside a (Or.inr hle)).trans
          (hzero a (Block.mem_footprint.mpr ⟨by wram_omega [hle], hlt⟩))]
      exact filterInv_empty n _ _
    have hmod_y : Modifies (Block.mk base (space w w₀ n k)).footprint x₁.mem y.mem := by
      intro a ha
      rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
      exact hmem_outside a (ha.imp_right fun h => by wram_omega [h])
    refine ⟨hbdd_z, hy_fr, ⟨hbdd_z, hy_0, hy_fr, (tableRep_congr hmem_below).mpr htab1, ?_,
      hrem_y, hinv_y⟩, hmod_y, by rw [hsteps1]⟩
    dsimp only [extractFilterSeed, y]
    rw [extractSeed_remInitData]
    exact (seedRep_congr _ hmem_below).mpr hseed1
  let ν₀ : PMF (LatentState (FilterSeed w₀ n) rQF) :=
    (sampleSeedsComp base w w₀ n x₂).eval.map fun z => ⟨extractFilterSeed base w w₀ n z.1.mem, z.1⟩
  refine ⟨ν₀, ?_, ⟨by rw [PMF.map_comp]; exact map_extractFilterSeed_eval_sampleSeedsComp ..,
      fun t ht => ?_⟩, fun t ht => ?_⟩
  · dsimp only [initSetup, setupSteps]; rw [Nat.cast_add]
    refine (ExecCodeDist.of_execWithin he_tab.within).seq_pure
      ((ExecCodeDist.of_execRand he_seeds).congr_dist
        (by simp [ν₀, ProbComp.eval_map, PMF.map_comp]; rfl) ?_)
    calc ProbComp.expect (sampleSeedsComp base w w₀ n x₂) (fun z => (z.2 : ℝ≥0∞))
        ≤ ProbComp.expect (sampleSeedsComp base w w₀ n x₂)
            (fun _ => ((ReducedKWise.resampleSteps w₀ b b 5 + 5 : ℕ) : ℝ≥0∞)) :=
          ProbComp.expect_mono_on_support fun z hz => Nat.cast_le.mpr (hsupp z hz).2.2.2.2
      _ = _ := ProbComp.expect_const _ _
  · supp_cases ht [ν₀, ProbComp.support_eval] with ⟨z, hz, rfl⟩
    exact (hsupp z hz).2.2.1
  · supp_cases ht [ν₀, ProbComp.support_eval] with ⟨z, hz, rfl⟩
    obtain ⟨hb, hf, _, hm, _⟩ := hsupp z hz
    exact ⟨hb, hf, hm⟩

/-! ## Section 4: Operation dispatcher `opCode` and single-step execution -/

/-- Underlying key `Fin U` of a filter operation `o : Op U`. -/
@[expose] def opKey {U : ℕ} : Op U → Fin U
  | .insert u => u
  | .delete u => u
  | .query u => u

/-- Numeric operation tag (`0 = insert`, `1 = delete`, `2 = query`). -/
@[expose] def opTag {U : ℕ} : Op U → ℕ
  | .insert _ => 0
  | .delete _ => 1
  | .query _ => 2

/-- Input-register mask (`qfReg 1` = key, `qfReg 247` = operation tag). -/
@[expose] noncomputable def inputReg : Fin rQF → Bool :=
  fun i => decide (i = qfReg 1 ∨ i = qfReg 247)

/-- Standalone register encoding for argument delivery. -/
@[expose] noncomputable def encode {U : ℕ} (o : Op U) (i : Fin rQF) : ℕ :=
  if i = qfReg 1 then (opKey o).val
  else if i = qfReg 247 then opTag o
  else 0

/-- Output decoder reading typed operation observations from final registers. -/
@[expose] noncomputable def decode {U : ℕ} : (o : Op U) → (Fin rQF → ℕ) → Option (Result o)
  | .insert _, _ => some PUnit.unit
  | .delete _, _ => some PUnit.unit
  | .query _, regs => some (decide (regs (qfReg 1) = 1))

/-- Unified Word-RAM operation body: evaluates the two-stage quotient hash into `qfReg 2` and the
remainder hash into `qfReg 3`, then runs the realized `clusterCode` (`clusterOpProg`). -/
@[expose] noncomputable def opCode (w w₀ n k : ℕ) : Code .exact rQF :=
  let b := quotBits w₀ n
  .seq (.op (.copy (qfReg 246) (qfReg 1)))
  (.seq ((ReducedKWise.evalCode w w₀ b b 5).rename kwiseMap)
  (.seq (.op (.copy (qfReg 1) (qfReg 246)))
  (.seq (.op (.copy (qfReg 245) (qfReg 2)))
  (.seq (remEvalCode w w₀ n k)
  (.seq (.op (.copy (qfReg 2) (qfReg 245)))
        (clusterCode w w₀ n k))))))

/-- Upper bound `clusterFactor * (11 * ℓ + 14) + 236909` on the instruction count of `opCode` when
the cluster around `quot u` has length `ℓ`. -/
@[expose] noncomputable def opStepBound (ℓ : ℕ) : ℕ :=
  clusterFactor * (11 * ℓ + 14) + 236909

/-- Per-operation expected instruction charge `opStepBound 290`. -/
@[expose] noncomputable def charge : ℕ :=
  opStepBound 290

theorem opCode_execWithin {U base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n k))
    {S : Finset (Fin U)} (hS : #S ≤ n)
    {p : FilterSeed w₀ n} {o : Op U} (ho : ValidOp n S o)
    {x : Data rQF}
    (hrep : Rep U w base w₀ n k p S x)
    (h1 : x.regs (qfReg 1) = (opKey o).val)
    (h247 : x.regs (qfReg 247) = opTag o) :
    ∃ y : Data rQF,
      ExecWithin w (opCode w w₀ n k) x y
        (opStepBound (seedClusterBound U w₀ n S (opKey o) p.1)) ∧
      Rep U w base w₀ n k p (stepSet S o) y ∧
      decode o y.regs = some (simResult U w₀ n k p S o) ∧
      Modifies (Block.mk base (space w w₀ n k)).footprint x.mem y.mem := by
  let b := quotBits w₀ n
  let u := opKey o
  obtain ⟨hx_bdd, hx_0, hx_fr, htab, hseed, hrem_seed, hinv⟩ := hrep
  have hb_lt := quotBits_lt_w_of_fits_space hw₀_pos hw hfit_space
  have hc_lt := two_mul_reducedChunkBits_lt_of_fits_space hw₀_pos hw hfit_space
  have hfit_kwise : Fits w (base + ReducedKWise.space w w₀ b b 5) := by
    have : ReducedKWise.space w w₀ b b 5 ≤ space w w₀ n k := by wram_omega
    fits [this]
  have hS_lt : #S < 2 ^ b := card_lt_two_pow_quotBits hU hS
  have hk_ne (j : Fin 248) (hj : 240 ≤ j.val) : ∀ i, kwiseMap i ≠ qfReg j := by
    intro i; fin_index [kwiseMap, qfReg]
  have hop_lt : opTag o < 4 := by cases o <;> simp [opTag]
  set s₀ : Memory.State := ⟨x.mem, base + space w w₀ n k⟩
  have hwp : WP w (opCode w w₀ n k) x fun y T =>
      T ≤ opStepBound (seedClusterBound U w₀ n S u p.1) ∧
      Rep U w base w₀ n k p (stepSet S o) y ∧
      decode o y.regs = some (simResult U w₀ n k p S o) ∧
      Modifies (Block.mk base (space w w₀ n k)).footprint x.mem y.mem := by
    unfold opCode
    wram_exec [h1]
    have hs1_bdd : (x.set (qfReg 246) u.val).Bounded w := by
      simpa [h1] using (Exec.copy (B := .exact) (w := w) (x := x)
        (d := qfReg 246) (s := qfReg 1)).within.bounded hx_bdd
    have hev_ex : ∃ y, ExecWithin w (ReducedKWise.evalCode w w₀ b b 5)
        ((x.set (qfReg 246) u.val).comap kwiseMap) y (ReducedKWise.evalSteps w₀ b b 5) ∧
        y.Bounded w ∧ y.regs 0 = base ∧ y.regs 2 = (quotHash U w₀ n p.1 u).val ∧
          y.mem = x.mem := by
      obtain ⟨y, he, h0, h2, hmem⟩ := ReducedKWise.evalCode_exec hw₀_pos (by omega) hU hb_lt.le
        hc_lt hfit_kwise p.1 u ((x.set (qfReg 246) u.val).comap kwiseMap)
        (by change (x.set (qfReg 246) u.val).regs (qfReg 0) = base; wram_simp [hx_0])
        (by change (x.set (qfReg 246) u.val).regs (qfReg 1) = u.val; wram_simp [h1, u]) htab hseed
      exact ⟨y, he.within, he.within.bounded (hs1_bdd.comap _), h0, h2, hmem⟩
    wram_call hev_ex renamed injective_kwiseMap with s2 ⟨⟨hs2_bdd_in, hs2_0, hs2_2, hs2_mem⟩, hfr2⟩
    have hs2_240 : s2.regs (qfReg 240) = base + space w w₀ n k := by
      rw [hfr2 _ (hk_ne 240 (by decide))]; wram_simp [hx_fr]
    have hs2_246 : s2.regs (qfReg 246) = u.val := by
      rw [hfr2 _ (hk_ne 246 (by decide))]; wram_simp [u]
    have hs2_247 : s2.regs (qfReg 247) = opTag o := by
      rw [hfr2 _ (hk_ne 247 (by decide))]; wram_simp [h247]
    have hs2_bdd : s2.Bounded w := by
      refine ⟨fun i => ?_, fun a => hs2_bdd_in.2 a⟩
      by_cases hi : ∃ j, kwiseMap j = i
      · rcases hi with ⟨j, rfl⟩; exact hs2_bdd_in.1 j
      · rw [hfr2 i fun j hj => hi ⟨j, hj⟩]; exact hs1_bdd.1 i
    wram_exec [hs2_246, show s2.regs (qfReg 2) = (quotHash U w₀ n p.1 u).val from hs2_2]
    have hs4_bdd :
        ((s2.set (qfReg 1) u.val).set (qfReg 245) (quotHash U w₀ n p.1 u).val).Bounded w := by
      have h1' : Fits w u.val := by rw [← hs2_246]; exact hs2_bdd.1 (qfReg 246)
      have h2' : Fits w (quotHash U w₀ n p.1 u).val := by
        rw [← show s2.regs (qfReg 2) = _ from hs2_2]; exact hs2_bdd.1 (qfReg 2)
      exact (hs2_bdd.set h1').set h2'
    have hrem_ex : ∃ s5, ExecWithin w (remEvalCode w w₀ n k)
        ((s2.set (qfReg 1) u.val).set (qfReg 245) (quotHash U w₀ n p.1 u).val) s5 45 ∧
        s5.Bounded w ∧ s5.mem = s2.mem ∧ s5.regs (qfReg 0) = base ∧
        s5.regs (qfReg 3) = (remHash U w₀ k p.2 u).val ∧
        ∀ j : Fin rQF, 240 ≤ j.val →
          s5.regs j = ((s2.set (qfReg 1) u.val).set (qfReg 245)
            (quotHash U w₀ n p.1 u).val).regs j := by
      obtain ⟨s5, he5, h5⟩ := remEvalCode_exec hw₀_pos (by omega) hU hfit_space p.2 u
        (x := (s2.set (qfReg 1) u.val).set (qfReg 245) (quotHash U w₀ n p.1 u).val)
        (by wram_simp [show s2.regs (qfReg 0) = base from hs2_0])
        (by wram_simp) (by simpa [hs2_mem] using hrem_seed)
      exact ⟨s5, he5.within, he5.within.bounded hs4_bdd, h5⟩
    wram_call hrem_ex with s5 ⟨hs5_bdd, hs5_mem, hs5_0, hs5_3, hfr5⟩
    have hs5_240 : s5.regs (qfReg 240) = base + space w w₀ n k := by
      rw [hfr5 _ (by decide)]; wram_simp [hs2_240]
    have hs5_245 : s5.regs (qfReg 245) = (quotHash U w₀ n p.1 u).val := by
      rw [hfr5 _ (by decide)]; wram_simp
    have hs5_247 : s5.regs (qfReg 247) = opTag o := by
      rw [hfr5 _ (by decide)]; wram_simp [hs2_247]
    wram_exec [hs5_245]
    have hs6_mem : s5.mem = x.mem := hs5_mem.trans hs2_mem
    have hinv_s6 : FilterInv n S (quotHash U w₀ n p.1) (remHash U w₀ k p.2)
        (extractFilterState base w w₀ n k s5.mem) := by rwa [hs6_mem]
    have hs6_bdd : (s5.set (qfReg 2) (quotHash U w₀ n p.1 u).val).Bounded w :=
      hs5_bdd.set (by rw [← hs5_245]; exact hs5_bdd.1 (qfReg 245))
    wram_call (clusterCode_execWithin hw₀_pos hw hfit_space u hop_lt hs6_bdd
        (by wram_simp [hs5_0]) (by wram_simp [hs5_240]) (by wram_simp)
        (by wram_simp [hs5_3]) (by wram_simp [hs5_247]) hinv_s6 hS_lt)
      with y ⟨hy_bdd, hy_0, hy_fr, hy_1, hy_mem⟩
    refine ⟨?_, ?_⟩
    · have hev := ReducedKWise.evalSteps_le w₀ (quotBits w₀ n) (quotBits w₀ n) 5
      have hℓ := hinv_s6.clusterLen_le_seedClusterBound hS_lt u
      dsimp only [ReducedKWise.evalBound] at hev
      have hmul := Nat.mul_le_mul_left clusterFactor
        (Nat.add_le_add_right (Nat.mul_le_mul_left 11 hℓ) 14)
      exact (show 19 + clusterFactor *
          (11 * hinv_s6.clusterLen hS_lt (quotHash U w₀ n p.1 u) + 14) +
          1 + 45 + 1 + 1 + ReducedKWise.evalSteps w₀ (quotBits w₀ n) (quotBits w₀ n) 5 + 1 ≤
          clusterFactor * (11 * seedClusterBound U w₀ n S u p.1 + 14) + 236909 by omega)
    · simp only [Data.set_mem, hs6_mem] at hy_fr hy_1 hy_mem
      have rep_of_frame {S' : Finset (Fin U)} {s' : Memory.State}
          (hfr' : y.regs (qfReg 240) = s'.frontier) (hmem' : y.mem = s'.mem)
          (hframe : SlotFrame base w w₀ n k s₀ s')
          (hinv' : FilterInv n S' (quotHash U w₀ n p.1) (remHash U w₀ k p.2)
            (extractFilterState base w w₀ n k y.mem)) :
          Rep U w base w₀ n k p S' y ∧
          Modifies (Block.mk base (space w w₀ n k)).footprint x.mem y.mem := by
        have hbelow : ∀ a < base + ReducedKWise.space w w₀ b b 5, y.mem a = x.mem a :=
          fun a ha => hmem' ▸ hframe.2 a (Or.inl (by wram_omega [ha]))
        refine ⟨⟨hy_bdd, hy_0, hfr'.trans hframe.1, (tableRep_congr hbelow).mpr htab,
          (seedRep_congr p.1 hbelow).mpr hseed,
          (hmem' ▸ hframe.2 _ (Or.inl (by wram_omega))).trans hrem_seed, hinv'⟩, fun a ha => ?_⟩
        rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
        exact hmem' ▸ hframe.2 a (ha.imp_left fun h => by wram_omega [h])
      cases o with
      | insert u' =>
        dsimp only [u, opKey, opTag] at hy_fr hy_1 hy_mem ho ⊢
        obtain ⟨_, hst_y, hframe_y⟩ := clusterOpProg_mk_insert base w w₀ n k u' s₀ hinv hS_lt
        have hcap' := card_stepSet_le hS ho
        obtain ⟨hr, hm⟩ := rep_of_frame hy_fr hy_mem hframe_y (by
          rw [hy_mem, hst_y]; exact hinv.insertState_filterInv ho.1 hcap'
            (card_lt_two_pow_quotBits hU hcap'))
        exact ⟨hr, rfl, hm⟩
      | delete u' =>
        dsimp only [u, opKey, opTag] at hy_fr hy_1 hy_mem ho ⊢
        obtain ⟨_, hst_y, hframe_y⟩ := clusterOpProg_mk_delete base w w₀ n k ho s₀ hinv hS_lt
        obtain ⟨hr, hm⟩ := rep_of_frame hy_fr hy_mem hframe_y (by
          rw [hy_mem, hst_y]; exact hinv.deleteState_filterInv ho hS_lt)
        exact ⟨hr, rfl, hm⟩
      | query u' =>
        dsimp only [u, opKey, opTag] at hy_fr hy_1 hy_mem ⊢
        obtain ⟨hres_y, hst_y⟩ := clusterOpProg_mk_query base w w₀ n k u' s₀ hinv hS_lt
        obtain ⟨hr, hm⟩ := rep_of_frame (hy_fr.trans (congrArg Memory.State.frontier hst_y))
          (hy_mem.trans (congrArg Memory.State.mem hst_y)) (SlotFrame.refl ..)
          (by rwa [hy_mem, hst_y])
        refine ⟨hr, ?_, hm⟩
        simp only [decode, simResult, hy_1]
        rw [show (Memory.spec 0).clientResult s₀ _ = _ from hres_y]
        cases decide (remHash U w₀ k p.2 u' ∈ bucketRun S (quotHash U w₀ n p.1)
          (remHash U w₀ k p.2) (quotHash U w₀ n p.1 u')) <;> rfl
  obtain ⟨y, T, hex, hT, hrep', hdec, hmod⟩ := hwp
  exact ⟨y, hex.mono hT, hrep', hdec, hmod⟩

/-! ## Section 5: Packaging as `SubroutineCode` and `ObliviousSequenceImpl` -/

/-- Relocatable Word-RAM `SubroutineCode` for the two-stage quotient filter over `Basis.exact`. -/
@[expose] noncomputable def subroutineCode (w w₀ n k : ℕ) : SubroutineCode .exact rQF 0 where
  allocSpan := allocSpan w w₀ n k
  initSetup := initSetup w w₀ n
  code := opCode w w₀ n k
  frontierReg := qfReg 240
  baseReg := qfReg 0
  initParams := ![]
  curReg := qfReg 241
  zeroReg := qfReg 242
  oneReg := qfReg 243
  incCur := .exactBin .add (qfReg 241) (qfReg 241) (qfReg 243)
  input := inputReg
  output := qfReg 1

private theorem encode_fits {U w w₀ : ℕ} (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (o : Op U) (i : Fin rQF) : Fits w (encode o i) := by
  unfold encode
  split_ifs
  · fits [(opKey o).isLt.trans_le hU, Nat.pow_le_pow_right two_pos (by omega : w₀ ≤ w)]
  · fits [show opTag o ≤ 2 by cases o <;> simp [opTag],
      Nat.pow_le_pow_right two_pos (by omega : 2 ≤ w)]
  · exact fits_zero w

theorem prepare_rep {U base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    {p : FilterSeed w₀ n} {S : Finset (Fin U)} (o : Op U) {x : Data rQF}
    (hrep : Rep U w base w₀ n k p S x) :
    let x_prep := (subroutineCode w w₀ n k).prepare encode o x
    Rep U w base w₀ n k p S x_prep ∧
    x_prep.regs (qfReg 1) = (opKey o).val ∧
    x_prep.regs (qfReg 247) = opTag o ∧
    (∀ i, (subroutineCode w w₀ n k).input i = true → Fits w (encode o i)) := by
  intro x_prep
  have hfit_args : ∀ i, (subroutineCode w w₀ n k).input i = true → Fits w (encode o i) :=
    fun i _ => encode_fits hw₀_pos hw hU o i
  refine ⟨⟨(subroutineCode w w₀ n k).prepare_bounded encode hrep.1 hfit_args, ?_, ?_, hrep.2.2.2⟩,
    ?_, ?_, hfit_args⟩ <;>
    simp +decide [x_prep, SubroutineCode.prepare, subroutineCode, encode, hrep.2.1, hrep.2.2.1]

theorem tsum_opStepBound_le {U w₀ n : ℕ} (hw₀_pos : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {S : Finset (Fin U)} (hS : #S ≤ n) (u : Fin U) :
    (∑' p : FilterSeed w₀ n,
      (filterSeedLaw w₀ n) p *
        (opStepBound (seedClusterBound U w₀ n S u p.1) : ℝ≥0∞)) ≤
      (charge : ℝ≥0∞) := by
  let A : ℝ≥0∞ := (clusterFactor * 11 : ℕ)
  let B : ℝ≥0∞ := (clusterFactor * 14 + 236909 : ℕ)
  have hop (ℓ : ℕ) : (opStepBound ℓ : ℝ≥0∞) = A * ℓ + B := by
    dsimp only [opStepBound, A, B]; push_cast; ring
  calc (∑' p : FilterSeed w₀ n,
        (filterSeedLaw w₀ n) p * (opStepBound (seedClusterBound U w₀ n S u p.1) : ℝ≥0∞))
      = ∑' p, ((filterSeedLaw w₀ n) p * (A * (seedClusterBound U w₀ n S u p.1 : ℝ≥0∞)) +
          (filterSeedLaw w₀ n) p * B) := tsum_congr fun p => by rw [hop, mul_add]
    _ = A * (∑' p, (filterSeedLaw w₀ n) p * (seedClusterBound U w₀ n S u p.1 : ℝ≥0∞)) + B := by
        rw [Summable.tsum_add CompleteLattice.summable CompleteLattice.summable,
          ENNReal.tsum_mul_right, (filterSeedLaw w₀ n).tsum_coe, one_mul, ← ENNReal.tsum_mul_left]
        exact congrArg (· + B) (tsum_congr fun p => by ring)
    _ ≤ A * 290 + B := by have := tsum_seedClusterBound_le hw₀_pos hU hS u; gcongr
    _ = (charge : ℝ≥0∞) := (hop 290).symm

private theorem steps_exec_aux {U base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n k))
    {ε : ℝ≥0∞}
    (prefOps remOps : List (Op U))
    (ν : PMF (SeqOutcome (FilterSeed w₀ n) (@Result U) rQF))
    (hS : #(activeSet prefOps) ≤ n)
    (hv : ValidOpSeqFrom n (activeSet prefOps) remOps)
    (hseed : ν.map SeqOutcome.latent = filterSeedLaw w₀ n)
    (hsupp : ∀ t ∈ ν.support,
      t.transcript = simTranscript U w₀ n k t.latent ∅ prefOps ∧
      Rep U w base w₀ n k t.latent (activeSet prefOps) t.data) :
    ∃ (ν_final : PMF (SeqOutcome (FilterSeed w₀ n) (@Result U) rQF)) (T_ops : ℝ≥0∞),
      ExecSteps (subroutineCode w w₀ n k) (spec U n ε)
        (FilterSeed w₀ n) w base (space w w₀ n k) encode decode remOps ν ν_final T_ops ∧
      ν_final.map SeqOutcome.latent = filterSeedLaw w₀ n ∧
      (∀ t ∈ ν_final.support,
        t.transcript = simTranscript U w₀ n k t.latent ∅ (prefOps ++ remOps) ∧
        Rep U w base w₀ n k t.latent (activeSet (prefOps ++ remOps)) t.data) ∧
      T_ops ≤ ((remOps.map (fun _ : Op U => charge)).sum : ℝ≥0∞) := by
  induction remOps generalizing prefOps ν with
  | nil =>
    exact ⟨ν, 0, ExecSteps.nil (S := spec U n ε) ν, hseed,
      fun t ht => by simpa only [List.append_nil] using hsupp t ht, by simp⟩
  | cons o os ih =>
    classical
    set S := activeSet prefOps
    obtain ⟨ho_valid, hos_valid⟩ := hv
    have hstep (t : SeqOutcome (FilterSeed w₀ n) (@Result U) rQF) (ht : t ∈ ν.support) :=
      let ⟨hrep_p, h1_p, h247_p, _⟩ := prepare_rep hw₀_pos hw hU o (hsupp t ht).2
      opCode_execWithin hw₀_pos hw hU hfit_space hS ho_valid hrep_p h1_p h247_p
    let nextData (t : SeqOutcome (FilterSeed w₀ n) (@Result U) rQF) : Data rQF :=
      if ht : t ∈ ν.support then Classical.choose (hstep t ht) else t.data
    let μ_step (t : SeqOutcome (FilterSeed w₀ n) (@Result U) rQF) :
        PMF (StepOutcome (FilterSeed w₀ n) (Result o) rQF) :=
      PMF.pure ⟨t.latent, nextData t, simResult U w₀ n k t.latent S o⟩
    let T_step (t : SeqOutcome (FilterSeed w₀ n) (@Result U) rQF) : ℝ≥0∞ :=
      (opStepBound (seedClusterBound U w₀ n S (opKey o) t.latent.1) : ℝ≥0∞)
    let ν₁ := ν.bind fun t => (μ_step t).map (t.appendStep o)
    have hact : activeSet (prefOps ++ [o]) = stepSet S o := by
      simp [activeSet, S, activeSetFrom_append]
    have hseed₁ : ν₁.map SeqOutcome.latent = filterSeedLaw w₀ n := by
      dsimp only [ν₁, μ_step]
      rw [PMF.map_bind]
      exact (congrArg (ν.bind ·) (funext fun t => by rw [PMF.pure_map, PMF.pure_map]; rfl)).trans
        hseed
    have hsupp₁ : ∀ q ∈ ν₁.support,
        q.transcript = simTranscript U w₀ n k q.latent ∅ (prefOps ++ [o]) ∧
        Rep U w base w₀ n k q.latent (activeSet (prefOps ++ [o])) q.data := by
      intro q hq
      supp_cases hq [ν₁, μ_step] with ⟨t, ht, rfl⟩
      have hspec := Classical.choose_spec (hstep t ht)
      refine ⟨?_, ?_⟩
      · simp only [SeqOutcome.appendStep, (hsupp t ht).1, simTranscript_append]; rfl
      · dsimp only [SeqOutcome.appendStep, nextData]
        rw [hact, dite_eq_left_of_eq_true (eq_true ht)]
        exact hspec.2.1
    obtain ⟨ν_final, T_rest, hex_rest, hseed_final, hsupp_final, hcost_rest⟩ :=
      ih (prefOps ++ [o]) ν₁ (hact ▸ card_stepSet_le hS ho_valid) (hact ▸ hos_valid) hseed₁ hsupp₁
    refine ⟨ν_final, (∑' t, ν t * T_step t) + T_rest,
      ExecSteps.cons (S := spec U n ε) (μ_step := μ_step) (T_step := T_step) (fun t ht => ?_)
        hex_rest, hseed_final,
      fun t ht => by simpa [List.append_assoc] using hsupp_final t ht, ?_⟩
    · obtain ⟨hrep_p, _, _, hfit_args⟩ := prepare_rep hw₀_pos hw hU o (hsupp t ht).2
      have hspec := Classical.choose_spec (hstep t ht)
      have hnd : nextData t = Classical.choose (hstep t ht) :=
        dite_eq_left_of_eq_true (eq_true ht)
      refine ⟨(hsupp t ht).2.1, hfit_args, hrep_p.1, ?_, fun q hq => ?_⟩
      · dsimp only [μ_step]; rw [PMF.pure_map, hnd]
        exact ExecCodeDist.of_execWithin hspec.1
      · supp_cases hq [μ_step]
        simpa only [hnd] using ⟨hspec.2.1.1, hspec.2.2.1, hspec.2.2.2⟩
    · have hT₁ : (∑' t, ν t * T_step t) ≤ (charge : ℝ≥0∞) := by
        rw [← Cslib.Probability.PMF.tsum_map_mul ν SeqOutcome.latent
          (fun p => (opStepBound (seedClusterBound U w₀ n S (opKey o) p.1) : ℝ≥0∞)), hseed]
        exact tsum_opStepBound_le hw₀_pos hU hS (opKey o)
      simpa only [List.map_cons, List.sum_cons, Nat.cast_add] using add_le_add hT₁ hcost_rest

/-- Parametric `ObliviousSequenceImpl` certificate for `spec U n ε` whenever
`(1 / 2 : ℝ≥0∞) ^ k ≤ ε`. -/
@[expose] noncomputable def implOfLe {U base w w₀ n k : ℕ} {ε : ℝ≥0∞}
    (hε : (1 / 2 : ℝ≥0∞) ^ k ≤ ε)
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n k)) :
    ObliviousSequenceImpl (subroutineCode w w₀ n k)
      (spec U n ε) w base ![] where
  Latent := FilterSeed w₀ n
  space := space w w₀ n k
  spanTime := 3
  setupTime := setupSteps w₀ n
  initPotential := 0
  charge _ := charge
  initInv ν₀ :=
    ν₀.map LatentState.latent = filterSeedLaw w₀ n ∧
    ∀ t ∈ ν₀.support, Rep U w base w₀ n k t.latent ∅ t.data
  validOp _ _ := True
  encode := encode
  decode := decode
  bounded hinv t ht := (hinv.2 t ht).1
  arguments_fit o _ i _ := by exact encode_fits hw₀_pos hw hU o i
  clear_nodup := by simp +decide [subroutineCode]
  params_not_clear j := Fin.elim0 j
  incCur_eval {x} h1 hfit := by
    dsimp only [subroutineCode] at h1 hfit ⊢
    rw [Op.eval_exactBin, h1]
    exact Data.put_of_fits hfit
  span_exec _ hfr _ := by
    obtain ⟨x₁, he, hmem, hb, hfr₁⟩ := allocSpan_execWithin hfit_space hfr
    exact ⟨x₁, he, hmem, hb, hfr₁, fun j => Fin.elim0 j⟩
  setup_exec hx₁ hb hfr _ hz :=
    initSetup_exec hw₀_pos hw hfit_space hx₁ hb hfr hz
  steps_exec ops ν₀ hv hinv := by
    let ν_seq : PMF (SeqOutcome (FilterSeed w₀ n) (@Result U) rQF) :=
      ν₀.map SeqOutcome.ofLatentState
    have hseed_seq : ν_seq.map SeqOutcome.latent = filterSeedLaw w₀ n := by
      dsimp only [ν_seq]
      rw [PMF.map_comp]
      exact hinv.1
    have hsupp_seq : ∀ t ∈ ν_seq.support,
        t.transcript = simTranscript U w₀ n k t.latent ∅ [] ∧
        Rep U w base w₀ n k t.latent (activeSet []) t.data := by
      intro t ht
      supp_cases ht [ν_seq] with ⟨u, hu, rfl⟩
      exact ⟨rfl, hinv.2 u hu⟩
    obtain ⟨ν_final, T_ops, hex, hseed_final, hsupp_final, hcost⟩ :=
      steps_exec_aux hw₀_pos hw hU hfit_space [] ops ν_seq (by simp) hv hseed_seq hsupp_seq
    have htr_map :
        ν_final.map SeqOutcome.transcript =
          (filterSeedLaw w₀ n).map (fun p => simTranscript U w₀ n k p ∅ ops) := by
      have hcongr :
          ν_final.map SeqOutcome.transcript =
            ν_final.map ((fun p => simTranscript U w₀ n k p ∅ ops) ∘ SeqOutcome.latent) := by
        refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun t ht => ?_
        have h := (hsupp_final t ht).1
        rw [List.nil_append] at h
        exact h
      rw [hcongr, ← PMF.map_comp, hseed_final]
    refine ⟨ν_final, T_ops, hex, ?_, ?_⟩
    · rw [htr_map]
      exact spec_weaken hε (contract_map_simTranscript hw₀_pos hU hv)
    · simpa only [Nat.cast_zero, zero_add] using hcost

/-- Exact-basis `ObliviousSequenceImpl` certificate for the two-stage quotient filter realizing
`spec U n ((1 / 2 : ℝ≥0∞) ^ k)`. -/
@[expose] noncomputable def impl {U base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n k)) :
    ObliviousSequenceImpl (subroutineCode w w₀ n k)
      (spec U n ((1 / 2 : ℝ≥0∞) ^ k)) w base ![] :=
  implOfLe le_rfl hw₀_pos hw hU hfit_space

/-- Standard-basis `ObliviousSequenceImpl` certificate for `spec U n ((1 / 2 : ℝ≥0∞) ^ k)`. -/
@[expose] noncomputable def implStandard {U base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n k)) :
    ObliviousSequenceImpl (subroutineCode w w₀ n k).toStandard
      (spec U n ((1 / 2 : ℝ≥0∞) ^ k)) w base ![] :=
  (impl hw₀_pos hw hU hfit_space).toStandard

/-- Exact-basis `ObliviousSequenceImpl` certificate realizing `spec U n ε` for any `ε ≠ 0` by
choosing `k = epsLog ε = max 1 ⌈log₂(1 / ε)⌉`. -/
@[expose] noncomputable def implOfEps {U base w w₀ n : ℕ} {ε : ℝ≥0∞}
    (hε0 : ε ≠ 0) (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n (epsLog ε))) :
    ObliviousSequenceImpl (subroutineCode w w₀ n (epsLog ε))
      (spec U n ε) w base ![] :=
  implOfLe (two_pow_neg_epsLog_le hε0) hw₀_pos hw hU hfit_space

/-- Standard-basis `ObliviousSequenceImpl` certificate realizing `spec U n ε` for any `ε ≠ 0`. -/
@[expose] noncomputable def implOfEpsStandard {U base w w₀ n : ℕ} {ε : ℝ≥0∞}
    (hε0 : ε ≠ 0) (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n (epsLog ε))) :
    ObliviousSequenceImpl (subroutineCode w w₀ n (epsLog ε)).toStandard
      (spec U n ε) w base ![] :=
  (implOfEps hε0 hw₀_pos hw hU hfit_space).toStandard

/-- Space bound for `impl` without requiring `quotBits w₀ n ≤ w` as a separate hypothesis. -/
theorem impl_space_le {U base w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n k))
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (impl hw₀_pos hw hU hfit_space).space ≤ 640 * ((n * k + w - 1) / w + 1) :=
  space_le hw₀_pos hw (quotBits_lt_w_of_fits_space hw₀_pos hw hfit_space).le hn hk

/-- Space bound for `implOfEps`: at most `640 * ((n * epsLog ε + w - 1) / w + 1)` words for all
`1 ≤ n`, `0 < w₀`, `2 * w₀ ≤ w`. -/
theorem implOfEps_space_le {U base w w₀ n : ℕ} {ε : ℝ≥0∞}
    (hε0 : ε ≠ 0) (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hU : U ≤ 2 ^ w₀)
    (hfit_space : Fits w (base + space w w₀ n (epsLog ε)))
    (hn : 1 ≤ n) :
    (implOfEps hε0 hw₀_pos hw hU hfit_space).space ≤
      640 * ((n * epsLog ε + w - 1) / w + 1) :=
  impl_space_le hw₀_pos hw hU hfit_space hn (one_le_epsLog ε)

end Cslib.DataStructure.ApproximateMembership.QuotientFilter
