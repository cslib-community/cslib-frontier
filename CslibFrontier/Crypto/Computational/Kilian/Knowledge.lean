/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Kilian.Extraction
public import CslibFrontier.Crypto.Computational.Kilian.RawVerifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.PCP.Completeness
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Languages.Probabilistic.Repeat
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.List.GetD

/-!
# Amplified compact PCP-table extraction and bounded-prefix Kilian NP arguments

`CslibFrontier.Crypto.Computational.Kilian.Extraction` proves the single-execution rewinding
bound (`HashFamily.kilianTableExtraction`): running `kilianTableExtractor` once yields a compact
PCP table whose expanded proof passes strictly more than `(num / den)` of the PCP coins with
probability at least `Pr[P accepts] - 1 / (p n + 1) - ν n`.

This module upgrades single-trial compact-table extraction and unframed `KilianView` verification
to high-confidence compact-table extraction and worst-case bounded-prefix verification:

* **Polynomial-time compact-table acceptance check (`kilianTablePassesFrac`):**
  Tests whether a candidate `KilianExtractedTable α` passes strictly more than `(num / den)` of
  all `2 ^ V.coins ext.stmt` PCP coins by evaluating `V.verdict` via `kilianPosition` lookups in
  `ext.table` without materializing the exponential-length proof `V.proofOfTable`. This predicate
  is equivalent to the `acceptCount` condition of `kilianExtractionFracGame`
  (`kilianTablePassesFrac_eq_true_iff`) and runs in polynomial time
  (`computableInPolyTime_kilianTablePassesFrac`).
* **Amplified strict-PPT extractor (`kilianAmplifiedExtractor`):**
  Repeats independent `(k, kilianTableExtractor)` samples `R n` times and returns the first
  candidate passing `kilianTablePassesFrac V num den`. It runs in uniform strict PPT
  (`isPPT_kilianAmplifiedExtractor`), certifies `kilianTablePassesFrac` on every `some ext` it
  outputs (`mem_support_kilianAmplifiedExtractor_passes`), and amplifies extraction failure
  exponentially (`failProbability_kilianAmplifiedExtractionGame`). Whenever prover acceptance is at
  least `(p n + 1)⁻¹ + (q n + 1)⁻¹ + ν n`, the amplified extractor outputs a valid
  `(num / den)`-table with failure probability at most `2⁻ⁿ`
  (`HashFamily.kilianAmplifiedTableExtraction`, `HashFamily.kilianRawAmplifiedExtraction`).
  No NP witness `w` is extracted; these are compact PCP-table extraction bounds toward full
  Barak–Goldreich weak proof of knowledge.
* **Unified NP succinct argument with bounded-prefix verification and table extraction:**
  For any `HashFamily H` and `R : NPRelation enc`,
  `exists_kilianSuccinctTableExtractionArgument_of_npRelation` combines the polynomial-time PCP
  witness compiler (`Kilian.NP`), honest completeness (structured and raw bounded-prefix),
  polylogarithmic succinct communication, worst-case bounded-prefix raw-tape verifier time and
  space polynomial in `n + |enc x|` for **every** arbitrary unbounded `rawProver : List Bool`,
  computational soundness for both structured and raw provers, and high-confidence amplified
  strict-PPT extraction of compact PCP tables passing `> 1 / 2` of PCP coins (from which
  `∃ w, R.IsWitness ext.stmt w` follows non-constructively via PCP soundness without extracting
  an explicit NP witness `w`).

Locators in [BarakGoldreich2001] and [Kilian1992] are not re-verified against the primary PDFs
(`locator not re-verified against primary PDF`).

## Main definitions

* `Cslib.Crypto.kilianTablePassesFrac`: polynomial-time verifier coin-fraction check on an
  extracted compact PCP table.
* `Cslib.Crypto.kilianAmplifiedExtractor`, `Cslib.Crypto.kilianAmplifiedExtractionGame`:
  amplified strict-PPT extractor returning the first compact table passing
  `kilianTablePassesFrac`.
* `Cslib.Crypto.kilianRawAcceptGame`: single-run prover acceptance under `kilianVerifyRawBounded`.

## Main results

* `Cslib.Crypto.kilianTablePassesFrac_eq_true_iff`,
  `Cslib.Crypto.computableInPolyTime_kilianTablePassesFrac`.
* `Cslib.Crypto.isPPT_kilianAmplifiedExtractor`,
  `Cslib.Crypto.failProbability_kilianAmplifiedExtractionGame`.
* `Cslib.Crypto.HashFamily.kilianAmplifiedTableExtraction`,
  `Cslib.Crypto.HashFamily.kilianRawAmplifiedExtraction`.
* `Cslib.Crypto.exists_kilianSuccinctTableExtractionArgument_of_npRelation`.

## References

* [J. Kilian, *A note on efficient zero-knowledge proofs and arguments*][Kilian1992]
* [B. Barak, O. Goldreich, *Universal Arguments and their Applications*][BarakGoldreich2001],
  Construction 3.4 and Lemma 3.5.
-/

@[expose] public section

namespace Cslib.Crypto

open Complexity Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

variable {α : Type}

/-! ### Polynomial-time fraction check on extracted compact tables -/

/-- Check whether an extracted compact table passes strictly more than `num / den` of all
`2 ^ V.coins ext.stmt` PCP random strings by looking up each queried address directly in
`ext.table` via `kilianPosition` (avoiding materialization of `V.proofOfTable`). -/
def kilianTablePassesFrac (V : PCPVerifier α) (num den : ℕ)
    (ext : KilianExtractedTable α) : Bool :=
  let coins := BitString.enumList (V.coins ext.stmt)
  let passed := coins.countP fun ρ =>
    V.verdict ((ext.stmt, ρ),
      (V.queries (ext.stmt, ρ)).map fun a => ext.table.getD (kilianPosition V ext.stmt a) false)
  decide (num * coins.length < den * passed)

/-- `kilianTablePassesFrac` holds iff `V.proofOfTable ext.stmt ext.table` passes strictly more than
`num / den` of the `2 ^ V.coins ext.stmt` PCP random coins. -/
theorem kilianTablePassesFrac_eq_true_iff (V : PCPVerifier α) (num den : ℕ)
    (ext : KilianExtractedTable α) :
    kilianTablePassesFrac V num den ext = true ↔
      num * 2 ^ V.coins ext.stmt <
        den * acceptCount (fun y => V.accepts y.1 (V.proofOfTable ext.stmt ext.table) y.2)
          ext.stmt (V.coins ext.stmt) := by
  have hcount :
      (BitString.enumList (V.coins ext.stmt)).countP (fun ρ =>
        V.verdict ((ext.stmt, ρ),
          (V.queries (ext.stmt, ρ)).map fun a =>
            ext.table.getD (kilianPosition V ext.stmt a) false)) =
        acceptCount (fun y => V.accepts y.1 (V.proofOfTable ext.stmt ext.table) y.2)
          ext.stmt (V.coins ext.stmt) := by
    rw [BitString.countP_enumList, acceptCount]
    congr 1
    ext word
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [V.accepts_proofOfTable ext.stmt ext.table (List.ofFn word) (List.length_ofFn)]
    rfl
  simp only [kilianTablePassesFrac, BitString.length_enumList, hcount, decide_eq_true_eq]

attribute [local irreducible] ComputableInPolyTime in
/-- `kilianTablePassesFrac` is computable in polynomial time under `V.PolyTime enc` and
logarithmic randomness. -/
@[program_certificate]
theorem computableInPolyTime_kilianTablePassesFrac {V : PCPVerifier α} {enc : α ↪ List Bool}
    {c : ℕ} (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) (num den : ℕ) :
    ComputableInPolyTime (kilianTablePassesFrac V num den)
      (encKilianExtractedTable enc) encBool := by
  have hstmt : ComputableInPolyTime (fun ext : KilianExtractedTable α => ext.stmt)
      (encKilianExtractedTable enc) enc :=
    encKilianExtractedTable_stmt_polyTime enc ComputableInPolyTime.id'
  have htab : ComputableInPolyTime (fun ext : KilianExtractedTable α => ext.table)
      (encKilianExtractedTable enc) encBits :=
    encKilianExtractedTable_table_polyTime enc ComputableInPolyTime.id'
  have hcoinsEnum : ComputableInPolyTime
      (fun ext : KilianExtractedTable α => BitString.enumList (V.coins ext.stmt))
      (encKilianExtractedTable enc) (encList encBits) :=
    (PCPVerifier.isPolyTime_enumCoins hV hcoins).comp hstmt
  have hqTable : ComputableInPolyTime
      (fun ext : KilianExtractedTable α => V.queryTable ext.stmt)
      (encKilianExtractedTable enc) (encList encNat) :=
    (PCPVerifier.isPolyTime_queryTable hV hcoins).comp hstmt
  have hp1 := ComputableInPolyTime.fst (encKilianExtractedTable enc) encBits
  have hp2 := ComputableInPolyTime.snd (encKilianExtractedTable enc) encBits
  have hqueries : ComputableInPolyTime
      (fun p : KilianExtractedTable α × List Bool => V.queries (p.1.stmt, p.2))
      (encPair (encKilianExtractedTable enc) encBits) (encList encNat) :=
    hV.queries.comp ((hstmt.comp hp1).prod hp2)
  have hq1 := ComputableInPolyTime.fst (encPair (encKilianExtractedTable enc) encBits) encNat
  have hq2 := ComputableInPolyTime.snd (encPair (encKilianExtractedTable enc) encBits) encNat
  have hpos : ComputableInPolyTime
      (fun q : (KilianExtractedTable α × List Bool) × ℕ => kilianPosition V q.1.1.stmt q.2)
      (encPair (encPair (encKilianExtractedTable enc) encBits) encNat) encUnary :=
    ComputableInPolyTime.idxOfWithInput (hqTable.comp (hp1.comp hq1)) hq2
  have hbit : ComputableInPolyTime
      (fun q : (KilianExtractedTable α × List Bool) × ℕ =>
        q.1.1.table.getD (kilianPosition V q.1.1.stmt q.2) false)
      (encPair (encPair (encKilianExtractedTable enc) encBits) encNat) encBool :=
    ComputableInPolyTime.bitsGetDWithInput (htab.comp (hp1.comp hq1)) hpos false
  have hbits : ComputableInPolyTime
      (fun p : KilianExtractedTable α × List Bool =>
        (V.queries (p.1.stmt, p.2)).map fun a => p.1.table.getD (kilianPosition V p.1.stmt a) false)
      (encPair (encKilianExtractedTable enc) encBits) encBits :=
    ComputableInPolyTime.listToBits.comp
      (ComputableInPolyTime.mapWithInput
        (f := fun p a => p.1.table.getD (kilianPosition V p.1.stmt a) false)
        hqueries hbit)
  have htest : ComputableInPolyTime
      (fun p : KilianExtractedTable α × List Bool =>
        V.verdict ((p.1.stmt, p.2),
          (V.queries (p.1.stmt, p.2)).map fun a =>
            p.1.table.getD (kilianPosition V p.1.stmt a) false))
      (encPair (encKilianExtractedTable enc) encBits) encBool :=
    hV.verdict.comp (((hstmt.comp hp1).prod hp2).prod hbits)
  have hpassed : ComputableInPolyTime
      (fun ext : KilianExtractedTable α =>
        (BitString.enumList (V.coins ext.stmt)).countP fun ρ =>
          V.verdict ((ext.stmt, ρ),
            (V.queries (ext.stmt, ρ)).map fun a =>
              ext.table.getD (kilianPosition V ext.stmt a) false))
      (encKilianExtractedTable enc) encUnary :=
    ComputableInPolyTime.countPWithInput hcoinsEnum htest
  have hcoinsLen : ComputableInPolyTime
      (fun ext : KilianExtractedTable α => (BitString.enumList (V.coins ext.stmt)).length)
      (encKilianExtractedTable enc) encUnary :=
    (ComputableInPolyTime.length_list encBits).comp hcoinsEnum
  have hlt : ComputableInPolyTime
      (fun ext : KilianExtractedTable α =>
        decide (num * (BitString.enumList (V.coins ext.stmt)).length <
          den * ((BitString.enumList (V.coins ext.stmt)).countP fun ρ =>
            V.verdict ((ext.stmt, ρ),
              (V.queries (ext.stmt, ρ)).map fun a =>
                ext.table.getD (kilianPosition V ext.stmt a) false))))
      (encKilianExtractedTable enc) encBool :=
    ComputableInPolyTime.unary_lt.comp
      ((ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const num) hcoinsLen).prod
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const den) hpassed))
  exact hlt

/-! ### Amplified strict-PPT knowledge extractor -/

/-- **Amplified strict-PPT table extractor** for Kilian's protocol: runs `R n` independent trials
of `(k ← BitString.sampleList n; kilianTableExtractor H V P T n k)` and returns the first
extracted compact table passing `kilianTablePassesFrac V num den`. -/
noncomputable def kilianAmplifiedExtractor (H : List Bool → List Bool → List Bool)
    (V : PCPVerifier α) (P : KilianProver α) (T R : ℕ → ℕ) (num den n : ℕ) :
    ProbComp (Option (KilianExtractedTable α)) := do
  let cands ← OracleComp.replicate (R n) do
    let k ← BitString.sampleList n
    kilianTableExtractor H V P T n k
  return cands.find? (kilianTablePassesFrac V num den)

/-- Experiment measuring whether `kilianAmplifiedExtractor` returns `some ext`. -/
noncomputable def kilianAmplifiedExtractionGame (H : List Bool → List Bool → List Bool)
    (V : PCPVerifier α) (P : KilianProver α) (T R : ℕ → ℕ) (num den n : ℕ) :
    ProbComp Bool := do
  let out ← kilianAmplifiedExtractor H V P T R num den n
  return out.isSome

/-- Every `some ext` emitted by `kilianAmplifiedExtractor` passes `kilianTablePassesFrac V num den`
with certainty. -/
theorem mem_support_kilianAmplifiedExtractor_passes
    {H : List Bool → List Bool → List Bool} {V : PCPVerifier α} {P : KilianProver α}
    {T R : ℕ → ℕ} {num den n : ℕ} {ext : KilianExtractedTable α}
    (hmem : some ext ∈ (ProbComp.eval (kilianAmplifiedExtractor H V P T R num den n)).support) :
    kilianTablePassesFrac V num den ext = true := by
  simp only [kilianAmplifiedExtractor, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hmem
  obtain ⟨cands, -, hcands⟩ := hmem
  exact List.find?_some hcands.symm

/-- Every `some ext` emitted by `kilianAmplifiedExtractor` inherits any first-stage statement
invariant satisfied on all `n`-bit hash keys by `P.commit n k`. -/
theorem mem_support_kilianAmplifiedExtractor_stmt
    {H : List Bool → List Bool → List Bool} {V : PCPVerifier α} {P : KilianProver α}
    {T R : ℕ → ℕ} {num den n : ℕ} (Q : α → Prop)
    (hQ : ∀ k : List Bool, k.length = n → ∀ cm ∈ (ProbComp.eval (P.commit n k)).support, Q cm.stmt)
    {ext : KilianExtractedTable α}
    (hmem : some ext ∈ (ProbComp.eval (kilianAmplifiedExtractor H V P T R num den n)).support) :
    Q ext.stmt := by
  simp only [kilianAmplifiedExtractor, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hmem
  obtain ⟨cands, hcands, hfind⟩ := hmem
  have hext_cands : ext ∈ cands := List.mem_of_find?_eq_some hfind.symm
  rw [ProbComp.mem_support_replicate_iff] at hcands
  have hext_trial := hcands.2 ext hext_cands
  simp only [ProbComp.eval_bind, kilianTableExtractor, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hext_trial
  obtain ⟨k, hk, cm, hcm, runs, -, rfl⟩ := hext_trial
  have hklen : k.length = n := by
    simpa only [BitString.length_of_mem_support_uniformList] using
      BitString.length_of_mem_support_uniformList (by simpa using hk)
  exact hQ k hklen cm hcm

/-- **Uniform strict-PPT efficiency of `kilianAmplifiedExtractor`**: for any polynomial-time hash,
polynomial-time `O(log n)`-coin PCP verifier `V`, uniform strict PPT prover `P`, and polynomial-time
budgets `T` and `R`, `kilianAmplifiedExtractor` runs in uniform strict PPT. -/
theorem isPPT_kilianAmplifiedExtractor {H : List Bool → List Bool → List Bool} {V : PCPVerifier α}
    {enc : α ↪ List Bool} {c : ℕ} {P : KilianProver α} {T R : ℕ → ℕ}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length)
    (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hP : P.IsPPT enc)
    (hT : ComputableInPolyTime T encUnary encUnary)
    (hR : ComputableInPolyTime R encUnary encUnary)
    (num den : ℕ) :
    IsPPT (encOption (encKilianExtractedTable enc))
      (fun n _ => kilianAmplifiedExtractor H V P T R num den n) := by
  have hf : ComputableInPolyTime (fun q : ℕ × List Bool => q.1)
      (encPair encUnary encBits) encUnary :=
    ComputableInPolyTime.fst encUnary encBits
  have hsam : IsPPTOn (encPair encUnary encBits) encBits
      (fun q : ℕ × List Bool => BitString.sampleList q.1) :=
    isPPTOn_sampleList.preprocess hf
  have htrial : IsPPTOn (encPair encUnary encBits) (encKilianExtractedTable enc)
      (fun q : ℕ × List Bool => do
        let k ← BitString.sampleList q.1
        kilianTableExtractor H V P T q.1 k) := by
    refine IsPPTOn.bind_with hsam ?_
    exact (isPPT_kilianTableExtractor hH hlen hV hcoins hP hT).on.preprocess
      ((hf.comp (ComputableInPolyTime.fst (encPair encUnary encBits) encBits)).prod
        (ComputableInPolyTime.snd (encPair encUnary encBits) encBits))
  have hrep := IsPPTOn.replicate htrial (hR.comp hf)
  have hfind : ComputableInPolyTime
      (fun cands : List (KilianExtractedTable α) =>
        cands.find? (kilianTablePassesFrac V num den))
      (encList (encKilianExtractedTable enc)) (encOption (encKilianExtractedTable enc)) :=
    ComputableInPolyTime.findWithInput ComputableInPolyTime.id'
      ((computableInPolyTime_kilianTablePassesFrac hV hcoins num den).comp
        (ComputableInPolyTime.snd (encList (encKilianExtractedTable enc))
          (encKilianExtractedTable enc)))
  simpa only [kilianAmplifiedExtractor, bind_pure_comp, Functor.map, Function.comp_def] using
    (hrep.map hfind).isPPT

/-- **Exact failure amplification identity**: running `R n` independent extractor trials shrinks
the failure probability (`1 - Pr[extract]`) to the `(R n)`-th power of the single-trial failure
probability of `kilianExtractionFracGame`. -/
theorem failProbability_kilianAmplifiedExtractionGame
    (H : List Bool → List Bool → List Bool) (V : PCPVerifier α) (P : KilianProver α)
    (T R : ℕ → ℕ) (num den n : ℕ) :
    1 - (Game.succProbability (ProbComp.eval
      (kilianAmplifiedExtractionGame H V P T R num den n)) : ℝ) =
      (1 - (Game.succProbability (ProbComp.eval
        (kilianExtractionFracGame H V P T num den n)) : ℝ)) ^ R n := by
  let oneTrial : ProbComp (KilianExtractedTable α) := do
    let k ← BitString.sampleList n
    kilianTableExtractor H V P T n k
  have hamp_false :
      (ProbComp.eval (kilianAmplifiedExtractionGame H V P T R num den n)) false =
        (ProbComp.eval (OracleComp.replicate (R n) oneTrial)).toOuterMeasure
          {cands | ∀ ext ∈ cands, !(kilianTablePassesFrac V num den ext) = true} := by
    have hprog : kilianAmplifiedExtractionGame H V P T R num den n =
        (OracleComp.replicate (R n) oneTrial) >>= fun cands =>
          pure (cands.find? (kilianTablePassesFrac V num den)).isSome := by
      simp only [kilianAmplifiedExtractionGame, kilianAmplifiedExtractor, oneTrial, bind_assoc,
        pure_bind]
    have hmap : ProbComp.eval (kilianAmplifiedExtractionGame H V P T R num den n) =
        (ProbComp.eval (OracleComp.replicate (R n) oneTrial)).map
          (fun cands => (cands.find? (kilianTablePassesFrac V num den)).isSome) := by
      rw [hprog]
      simp only [ProbComp.eval_bind, ProbComp.eval_pure]
      rfl
    rw [hmap, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    have hpre : (fun cands : List (KilianExtractedTable α) =>
        (cands.find? (kilianTablePassesFrac V num den)).isSome) ⁻¹' {false} =
        {cands | ∀ ext ∈ cands, !(kilianTablePassesFrac V num den ext) = true} := by
      ext cands
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      rw [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, List.find?_eq_none]
      simp [Bool.not_eq_true]
    rw [hpre]
  have hone_false :
      (ProbComp.eval (kilianExtractionFracGame H V P T num den n)) false =
        (ProbComp.eval oneTrial).toOuterMeasure
          {ext | !(kilianTablePassesFrac V num den ext) = true} := by
    have hcongr : (fun ext : KilianExtractedTable α => PMF.pure (decide
        (num * 2 ^ V.coins ext.stmt <
          den * acceptCount (fun y => V.accepts y.1 (V.proofOfTable ext.stmt ext.table) y.2)
            ext.stmt (V.coins ext.stmt)))) =
        fun ext => PMF.pure (kilianTablePassesFrac V num den ext) := by
      funext ext
      congr 1
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using (kilianTablePassesFrac_eq_true_iff V num den ext).symm
    have hmap : ProbComp.eval (kilianExtractionFracGame H V P T num den n) =
        (ProbComp.eval oneTrial).map (kilianTablePassesFrac V num den) := by
      change ProbComp.eval (kilianExtractionFracGame H V P T num den n) =
          (ProbComp.eval oneTrial).bind (fun ext => PMF.pure (kilianTablePassesFrac V num den ext))
      simp only [kilianExtractionFracGame, oneTrial, ProbComp.eval_bind, ProbComp.eval_pure, hcongr]
      rw [PMF.bind_bind]
    rw [hmap, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    congr 1
    ext ext
    simp [Set.mem_ofPred_eq]
  have hpow_enn :
      (ProbComp.eval (kilianAmplifiedExtractionGame H V P T R num den n)) false =
        ((ProbComp.eval (kilianExtractionFracGame H V P T num den n)) false) ^ R n := by
    rw [hamp_false, hone_false]
    exact ProbComp.toOuterMeasure_replicate_forall oneTrial
      (fun ext => !(kilianTablePassesFrac V num den ext)) (R n)
  have hreal := congrArg ENNReal.toReal hpow_enn
  rw [ENNReal.toReal_pow] at hreal
  rw [PMF.toReal_false_eq_one_sub, PMF.toReal_false_eq_one_sub] at hreal
  simpa only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal] using hreal

/-! ### High-confidence asymptotic extraction bounds -/

/-- **Amplified strict-PPT compact-table extraction for Kilian's protocol**: for any
collision-resistant `HashFamily`, polynomial-time `O(log |enc x|)`-coin PCP verifier `V`, uniform
strict PPT prover `P`, strict coin threshold `num / den < 1`, and polynomial slack indices
`p, q : ℕ → ℕ`, there are polynomial-time budgets `T` and `R` such that:
1. `kilianAmplifiedExtractor H V P T R num den` runs in uniform strict PPT;
2. every `some ext` emitted by it passes `kilianTablePassesFrac V num den ext = true`; and
3. whenever `P` accepts with probability at least `(p n + 1)⁻¹ + (q n + 1)⁻¹ + ν n` (for a
   negligible function `ν`), the amplified extractor fails with probability at most `(1 / 2) ^ n`.
No NP witness `w` is extracted here; the output is a compact PCP bit table. -/
theorem HashFamily.kilianAmplifiedTableExtraction
    {H : List Bool → List Bool → List Bool} {V : PCPVerifier α} {enc : α ↪ List Bool} {c : ℕ}
    {P : KilianProver α} (hH : HashFamily H) (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hP : P.IsPPT enc) (p q : ℕ → ℕ)
    (hp : ComputableInPolyTime p encUnary encUnary)
    (hq : ComputableInPolyTime q encUnary encUnary)
    {num den : ℕ} (hnum : num < den) :
    ∃ T R : ℕ → ℕ,
      ComputableInPolyTime T encUnary encUnary ∧
      ComputableInPolyTime R encUnary encUnary ∧
      IsPPT (encOption (encKilianExtractedTable enc))
        (fun n _ => kilianAmplifiedExtractor H V P T R num den n) ∧
      (∀ (n : ℕ) (ext : KilianExtractedTable α),
        some ext ∈ (ProbComp.eval (kilianAmplifiedExtractor H V P T R num den n)).support →
          kilianTablePassesFrac V num den ext = true) ∧
      ∃ ν : ℕ → ℝ≥0, Negligible ν ∧
        ∀ n : ℕ,
          ((p n + 1 : ℕ) : ℝ≥0)⁻¹ + ((q n + 1 : ℕ) : ℝ≥0)⁻¹ + ν n ≤
            Game.succProbability (ProbComp.eval (kilianAcceptGame H V P n)) →
          1 - (Game.succProbability (ProbComp.eval
            (kilianAmplifiedExtractionGame H V P T R num den n)) : ℝ) ≤ (1 / 2 : ℝ) ^ n := by
  obtain ⟨T, hT, -, ν, hν, hweak⟩ :=
    hH.kilianTableExtraction hV hcoins hP p hp hnum
  let R : ℕ → ℕ := fun n => (q n + 1) * n
  have hR : ComputableInPolyTime R encUnary encUnary := by
    dsimp only [R]
    fun_prop
  have hExtPPT :=
    isPPT_kilianAmplifiedExtractor hH.polyTime hH.length_eq hV hcoins hP hT hR num den
  refine ⟨T, R, hT, hR, hExtPPT, fun _ _ hmem =>
    mem_support_kilianAmplifiedExtractor_passes hmem, ν, hν, fun n hacc => ?_⟩
  have hfrac_le := NNReal.coe_le_coe.mpr (hweak n)
  have hacc_real := NNReal.coe_le_coe.mpr hacc
  simp only [NNReal.coe_add, NNReal.coe_inv, NNReal.coe_natCast] at hfrac_le hacc_real
  have hfrac_real : (1 / ((q n + 1 : ℕ) : ℝ)) ≤
      (Game.succProbability (ProbComp.eval (kilianExtractionFracGame H V P T num den n)) : ℝ) := by
    rw [one_div]
    linarith
  have h1m : 0 ≤ 1 -
      (Game.succProbability (ProbComp.eval (kilianExtractionFracGame H V P T num den n)) : ℝ) :=
    sub_nonneg.mpr (NNReal.coe_le_one.mpr (Game.succProbability_le_one _))
  have hstep1 : 1 - (Game.succProbability (ProbComp.eval
      (kilianExtractionFracGame H V P T num den n)) : ℝ) ≤
      1 - (1 / ((q n + 1 : ℕ) : ℝ)) := by linarith
  have hstep2 : 1 - (1 / ((q n + 1 : ℕ) : ℝ)) ≤ Real.exp (-(1 / ((q n + 1 : ℕ) : ℝ))) :=
    Real.one_sub_le_exp_neg _
  have hprod : (-(1 / ((q n + 1 : ℕ) : ℝ))) * (R n : ℝ) = (n : ℝ) * (-1) := by
    dsimp only [R]
    push_cast
    field_simp
  have hpow : (1 - (Game.succProbability (ProbComp.eval
      (kilianExtractionFracGame H V P T num den n)) : ℝ)) ^ R n ≤
      (1 / 2 : ℝ) ^ n := by
    calc (1 - (Game.succProbability (ProbComp.eval
          (kilianExtractionFracGame H V P T num den n)) : ℝ)) ^ R n
        ≤ (Real.exp (-(1 / ((q n + 1 : ℕ) : ℝ)))) ^ R n :=
          pow_le_pow_left₀ h1m (hstep1.trans hstep2) (R n)
      _ = (Real.exp (-1)) ^ n := by
          rw [← Real.exp_nat_mul, mul_comm, hprod, Real.exp_nat_mul]
      _ ≤ (1 / 2 : ℝ) ^ n :=
          pow_le_pow_left₀ (Real.exp_pos (-1)).le Real.exp_neg_one_lt_half.le n
  rwa [failProbability_kilianAmplifiedExtractionGame]

/-- Single-run acceptance game for a raw prover verified by the bounded-prefix verifier
`kilianVerifyRawBounded`. -/
noncomputable def kilianRawAcceptGame (H : List Bool → List Bool → List Bool)
    (V : PCPVerifier α) (P : KilianRawProver α) (n : ℕ) : ProbComp Bool := do
  let k ← BitString.sampleList n
  let cm ← P.commit n k
  let ρs ← kilianChallenges V n cm.stmt
  let raw ← P.answer n cm.state ρs
  return kilianVerifyRawBounded H V ⟨k, cm.stmt, ρs⟩ (encPair encBits encBits (cm.rawRoot, raw))

/-- Every run accepted by `kilianVerifyRawBounded` in `kilianRawAcceptGame` also makes
`kilianAcceptGame` accept for `P.toKilianProver`. -/
theorem succProbability_kilianRawAcceptGame_le
    (H : List Bool → List Bool → List Bool) (V : PCPVerifier α)
    (P : KilianRawProver α) (n : ℕ) :
    Game.succProbability (ProbComp.eval (kilianRawAcceptGame H V P n)) ≤
      Game.succProbability (ProbComp.eval (kilianAcceptGame H V P.toKilianProver n)) := by
  have hacc_eq :
      ProbComp.eval (kilianAcceptGame H V P.toKilianProver n) =
        ProbComp.eval do
          let k ← BitString.sampleList n
          let cm ← P.commit n k
          let ρs ← kilianChallenges V n cm.stmt
          let raw ← P.answer n cm.state ρs
          return kilianVerify H V k cm.stmt cm.rawRoot ρs (kilianResponseDecoder.decode raw) := by
    simp [kilianAcceptGame, KilianRawProver.toKilianProver]
  have hle :
      (ProbComp.eval (kilianRawAcceptGame H V P n)) true ≤
        (ProbComp.eval (kilianAcceptGame H V P.toKilianProver n)) true := by
    rw [hacc_eq]
    simp only [kilianRawAcceptGame, ProbComp.eval_bind]
    refine Probability.PMF.bind_apply_mono_on_support _ _ fun k _ => ?_
    refine Probability.PMF.bind_apply_mono_on_support _ _ fun cm _ => ?_
    refine Probability.PMF.bind_apply_mono_on_support _ _ fun ρs _ => ?_
    refine Probability.PMF.bind_apply_mono_on_support _ _ fun rawResp _ => ?_
    have himpl :
        kilianVerifyRawBounded H V ⟨k, cm.stmt, ρs⟩
          (encPair encBits encBits (cm.rawRoot, rawResp)) = true →
        kilianVerify H V k cm.stmt cm.rawRoot ρs (kilianResponseDecoder.decode rawResp) = true := by
      simp only [kilianVerifyRawBounded, Bool.and_eq_true, kilianProverMsgDecoder_encPair_bits]
      exact fun h => h.2
    rcases hb1 : kilianVerifyRawBounded H V ⟨k, cm.stmt, ρs⟩
        (encPair encBits encBits (cm.rawRoot, rawResp)) with _ | _
    · simp [ProbComp.eval_pure]
    · rw [himpl hb1]
  exact ENNReal.toNNReal_mono (PMF.apply_lt_top _ _).ne hle

/-- **Amplified strict-PPT compact-table extraction from raw cheating provers**: for any uniform
strict PPT raw prover `P : KilianRawProver α` verified by `kilianVerifyRawBounded`, decoding `P`
via `P.toKilianProver` yields a uniform strict PPT extractor outputting compact PCP tables passing
`kilianTablePassesFrac V num den` with failure probability at most `2⁻ⁿ` whenever `P` passes
`kilianVerifyRawBounded` with probability at least `(p n + 1)⁻¹ + (q n + 1)⁻¹ + ν n`. No NP
witness `w` is extracted here. -/
theorem HashFamily.kilianRawAmplifiedExtraction
    {H : List Bool → List Bool → List Bool} {V : PCPVerifier α} {enc : α ↪ List Bool} {c : ℕ}
    {P : KilianRawProver α} (hH : HashFamily H) (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hP : P.IsPPT enc) (p q : ℕ → ℕ)
    (hp : ComputableInPolyTime p encUnary encUnary)
    (hq : ComputableInPolyTime q encUnary encUnary)
    {num den : ℕ} (hnum : num < den) :
    ∃ T R : ℕ → ℕ,
      ComputableInPolyTime T encUnary encUnary ∧
      ComputableInPolyTime R encUnary encUnary ∧
      IsPPT (encOption (encKilianExtractedTable enc))
        (fun n _ => kilianAmplifiedExtractor H V P.toKilianProver T R num den n) ∧
      (∀ (n : ℕ) (ext : KilianExtractedTable α),
        some ext ∈ (ProbComp.eval
          (kilianAmplifiedExtractor H V P.toKilianProver T R num den n)).support →
          kilianTablePassesFrac V num den ext = true) ∧
      ∃ ν : ℕ → ℝ≥0, Negligible ν ∧
        ∀ n : ℕ,
          ((p n + 1 : ℕ) : ℝ≥0)⁻¹ + ((q n + 1 : ℕ) : ℝ≥0)⁻¹ + ν n ≤
            Game.succProbability (ProbComp.eval (kilianRawAcceptGame H V P n)) →
          1 - (Game.succProbability (ProbComp.eval
            (kilianAmplifiedExtractionGame H V P.toKilianProver T R num den n)) : ℝ) ≤
            (1 / 2 : ℝ) ^ n := by
  obtain ⟨T, R, hT, hR, hExtPPT, hmem, ν, hν, hamp⟩ :=
    hH.kilianAmplifiedTableExtraction hV hcoins hP.toKilianProver p q hp hq hnum
  refine ⟨T, R, hT, hR, hExtPPT, hmem, ν, hν, fun n hraw => ?_⟩
  exact hamp n (hraw.trans (succProbability_kilianRawAcceptGame_le H V P n))

/-! ### Unified Kilian succinct argument with bounded-prefix verifier and table extraction -/

/-- **Kilian succinct NP argument with worst-case bounded-prefix verifier and amplified
compact-table extraction**: under any collision-resistant `HashFamily H`, every NP relation
`R : NPRelation enc` admits an `O(log n)`-coin constant-query PCP verifier `V` and polynomial-time
witness compiler `compile` giving:

* polynomial-time honest commitment and opening algorithms on NP witnesses `(x, w)`;
* perfect completeness for both structured `kilianHonestGame` and raw bounded-prefix
  `kilianHonestRawBoundedGame`;
* polylogarithmic communication `O(n² · (log₂ |enc x| + 1))`;
* one fixed binary `MultiTapeTM` computing `kilianVerifyRawBounded` in worst-case time and space
  polynomial in `n + |enc x|` uniformly over **all** arbitrary unbounded `rawProver : List Bool`;
* computational soundness against both structured (`KilianSound`) and raw (`KilianRawSound`)
  uniform strict PPT cheating provers; and
* high-confidence (`≤ 2⁻ⁿ` failure) strict-PPT extraction of a compact PCP table passing
  `kilianTablePassesFrac V 1 2` (`> 1 / 2` of PCP coins) from any structured or raw uniform strict
  PPT prover with acceptance probability at least `(p n + 1)⁻¹ + (q n + 1)⁻¹ + ν n`. No NP witness
  `w` is extracted constructively by `kilianAmplifiedExtractor`; the conclusion `∃ w, R.IsWitness
  ext.stmt w` is an existential PCP-soundness consequence of `ext.stmt ∈ R.language`. -/
theorem exists_kilianSuccinctTableExtractionArgument_of_npRelation
    {H : List Bool → List Bool → List Bool} (hH : HashFamily H)
    (enc : α ↪ List Bool) (R : NPRelation enc) :
    ∃ (V : PCPVerifier α) (compile : α × List Bool → List Bool) (c d : ℕ),
      V.PolyTime enc ∧
      (∀ x, V.coins x ≤ c * (Nat.log 2 (enc x).length + 1)) ∧
      (∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d) ∧
      ComputableInPolyTime compile (encPair enc encBits) encBits ∧
      ComputableInPolyTime
        (fun p : List Bool × α × List Bool =>
          let (key, state) := p
          let (x, w) := state
          kilianCommit H V key x (compile (x, w)))
        (encPair encBits (encPair enc encBits)) encBits ∧
      ComputableInPolyTime
        (fun p : (List Bool × α × List Bool) × List (List Bool) =>
          let (proverIn, ρs) := p
          let (key, state) := proverIn
          let (x, w) := state
          kilianRespond H V key x (compile (x, w)) ρs)
        (encPair (encPair encBits (encPair enc encBits)) (encList encBits))
        encKilianResponse ∧
      (∀ x, x ∈ R.language ↔ ∃ table, V.tableVerifier (x, table) = true) ∧
      (∀ x w, R.IsWitness x w → V.tableVerifier (x, compile (x, w)) = true) ∧
      (∀ x w, R.IsWitness x w → ∀ n,
        ProbComp.eval (kilianHonestRawBoundedGame H V x (compile (x, w)) n) = PMF.pure true ∧
        ProbComp.eval (kilianHonestGame H V x (compile (x, w)) n) = PMF.pure true) ∧
      (∃ C : ℕ, ∀ (n : ℕ) (k : List Bool) (x : α) (table : List Bool) (ρs : List (List Bool)),
        k.length = n → ρs.length = n → (∀ ρ ∈ ρs, ρ.length = V.coins x) →
          kilianCommunication k (kilianCommit H V k x table) ρs
            (kilianRespond H V k x table ρs) ≤
          C * (n + 1) ^ 2 * (Nat.log 2 (enc x).length + 1)) ∧
      (∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State)
        (t s tBound sBound : ℕ → ℕ),
        PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
        PolynomiallyBounded tBound ∧ PolynomiallyBounded sBound ∧
        tm.ComputesFunInTimeAndSpace (encPair (encKilianChallengeInput enc) encBits) encBool
          (fun p => kilianVerifyRawBounded H V p.1 p.2)
          (fun p => t (encKilianChallengeInput enc p.1).length)
          (fun p => s (encKilianChallengeInput enc p.1).length) ∧
        (∀ (n : ℕ) (ch : KilianChallengeInput α) (rawProver : List Bool),
          ch.key.length ≤ n → ch.challenges.length ≤ n →
          (∀ ρ ∈ ch.challenges, ρ.length ≤ V.coins ch.stmt) →
            tm.ComputesInTimeAndSpace
              (encPair (encKilianChallengeInput enc) encBits (ch, rawProver))
              (encBool (kilianVerifyRawBounded H V ch rawProver))
              (tBound (n + (enc ch.stmt).length))
              (sBound (n + (enc ch.stmt).length)))) ∧
      KilianSound H V enc R.language ∧
      KilianRawSound H V enc R.language ∧
      (∀ ext : KilianExtractedTable α,
        kilianTablePassesFrac V 1 2 ext = true → ∃ w, R.IsWitness ext.stmt w) ∧
      (∀ (P : KilianProver α), P.IsPPT enc →
        ∀ p q : ℕ → ℕ,
          ComputableInPolyTime p encUnary encUnary →
          ComputableInPolyTime q encUnary encUnary →
          ∃ T R_rep : ℕ → ℕ,
            ComputableInPolyTime T encUnary encUnary ∧
            ComputableInPolyTime R_rep encUnary encUnary ∧
            IsPPT (encOption (encKilianExtractedTable enc))
              (fun n _ => kilianAmplifiedExtractor H V P T R_rep 1 2 n) ∧
            (∀ (n : ℕ) (ext : KilianExtractedTable α),
              some ext ∈ (ProbComp.eval
                (kilianAmplifiedExtractor H V P T R_rep 1 2 n)).support →
                kilianTablePassesFrac V 1 2 ext = true ∧ ∃ w, R.IsWitness ext.stmt w) ∧
            ∃ ν : ℕ → ℝ≥0, Negligible ν ∧
              ∀ n : ℕ,
                ((p n + 1 : ℕ) : ℝ≥0)⁻¹ + ((q n + 1 : ℕ) : ℝ≥0)⁻¹ + ν n ≤
                  Game.succProbability (ProbComp.eval (kilianAcceptGame H V P n)) →
                1 - (Game.succProbability (ProbComp.eval
                  (kilianAmplifiedExtractionGame H V P T R_rep 1 2 n)) : ℝ) ≤
                  (1 / 2 : ℝ) ^ n) ∧
      (∀ (P : KilianRawProver α), P.IsPPT enc →
        ∀ p q : ℕ → ℕ,
          ComputableInPolyTime p encUnary encUnary →
          ComputableInPolyTime q encUnary encUnary →
          ∃ T R_rep : ℕ → ℕ,
            ComputableInPolyTime T encUnary encUnary ∧
            ComputableInPolyTime R_rep encUnary encUnary ∧
            IsPPT (encOption (encKilianExtractedTable enc))
              (fun n _ => kilianAmplifiedExtractor H V P.toKilianProver T R_rep 1 2 n) ∧
            (∀ (n : ℕ) (ext : KilianExtractedTable α),
              some ext ∈ (ProbComp.eval
                (kilianAmplifiedExtractor H V P.toKilianProver T R_rep 1 2 n)).support →
                kilianTablePassesFrac V 1 2 ext = true ∧ ∃ w, R.IsWitness ext.stmt w) ∧
            ∃ ν : ℕ → ℝ≥0, Negligible ν ∧
              ∀ n : ℕ,
                ((p n + 1 : ℕ) : ℝ≥0)⁻¹ + ((q n + 1 : ℕ) : ℝ≥0)⁻¹ + ν n ≤
                  Game.succProbability (ProbComp.eval (kilianRawAcceptGame H V P n)) →
                1 - (Game.succProbability (ProbComp.eval
                  (kilianAmplifiedExtractionGame H V P.toKilianProver T R_rep 1 2 n)) : ℝ) ≤
                  (1 / 2 : ℝ) ^ n) := by
  obtain ⟨V, compile, c, d, hV, hpcp, hcompile, hacc⟩ := exists_pcpVerifier_of_npRelation enc R
  have hq : ∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d := fun x ρ hρ => by
    simpa using hpcp.length_queries_le x ρ hρ
  have hwit_fn : ∀ ext : KilianExtractedTable α,
      kilianTablePassesFrac V 1 2 ext = true → ∃ w, R.IsWitness ext.stmt w := fun ext hpass =>
    (R.mem_language).mp (kilianExtract_mem_of_isPCP hpcp ext
      ((kilianTablePassesFrac_eq_true_iff V 1 2 ext).mp hpass))
  let E_in := encPair encBits (encPair enc encBits)
  have hk : ComputableInPolyTime (fun p : List Bool × α × List Bool => p.1) E_in encBits :=
    ComputableInPolyTime.fst _ _
  have hsnd := ComputableInPolyTime.snd encBits (encPair enc encBits)
  have hx : ComputableInPolyTime (fun p : List Bool × α × List Bool => p.2.1) E_in enc :=
    (ComputableInPolyTime.fst _ _).comp hsnd
  have hin : ComputableInPolyTime
      (fun p : List Bool × α × List Bool =>
        ({ key := p.1, stmt := p.2.1, table := compile p.2 } : KilianProverInput α))
      E_in (encKilianProverInput enc) :=
    encKilianProverInput_mk_polyTime enc hk hx (hcompile.comp hsnd)
  have hcommit_raw :=
    (computableInPolyTime_kilianCommit hH.polyTime hH.length_eq hV hpcp.coins_le).comp hin
  have hcommit : ComputableInPolyTime
      (fun p : List Bool × α × List Bool =>
        let (key, state) := p
        let (x, w) := state
        kilianCommit H V key x (compile (x, w)))
      (encPair encBits (encPair enc encBits)) encBits := by
    convert hcommit_raw using 1
    funext p
    rcases p with ⟨key, ⟨x, w⟩⟩
    rfl
  have hrespond_raw :=
    (computableInPolyTime_kilianRespond hH.polyTime hH.length_eq hV hpcp.coins_le).comp
      ((hin.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _))
  have hrespond : ComputableInPolyTime
      (fun p : (List Bool × α × List Bool) × List (List Bool) =>
        let (proverIn, ρs) := p
        let (key, state) := proverIn
        let (x, w) := state
        kilianRespond H V key x (compile (x, w)) ρs)
      (encPair (encPair encBits (encPair enc encBits)) (encList encBits))
      encKilianResponse := by
    convert hrespond_raw using 1
    funext p
    rcases p with ⟨⟨key, ⟨x, w⟩⟩, ρs⟩
    rfl
  refine ⟨V, compile, c, d, hV, hpcp.coins_le, hq, hcompile, hcommit, hrespond,
    hpcp.mem_iff_exists_tableVerifier, hacc,
    fun x w hw n =>
      ⟨eval_kilianHonestRawBoundedGame hH.length_eq (hacc x w hw) n,
       eval_kilianHonestGame H V hH.length_eq (hacc x w hw) n⟩,
    ⟨_, fun n k x table ρs hklen hn hρs =>
      kilianCommunication_honest_le_log hH.length_eq hklen hn hρs (fun ρ hρ => hq x ρ hρ)
        (hpcp.coins_le x)⟩,
    computableInTimeAndSpace_kilianVerifyRawBounded_of_params hH.polyTime hH.length_eq hV
      hpcp.coins_le,
    hH.kilianSound hV hpcp,
    hH.kilianRawSound hV hpcp,
    hwit_fn,
    ?_, ?_⟩
  · intro P hP p q hp hq_pb
    obtain ⟨T, R_rep, hT, hR, hExtPPT, hmem, ν, hν, hamp⟩ :=
      hH.kilianAmplifiedTableExtraction hV hpcp.coins_le hP p q hp hq_pb
        (by norm_num : (1 : ℕ) < 2)
    exact ⟨T, R_rep, hT, hR, hExtPPT, fun n ext hex =>
      ⟨hmem n ext hex, hwit_fn ext (hmem n ext hex)⟩, ν, hν, hamp⟩
  · intro P hP p q hp hq_pb
    obtain ⟨T, R_rep, hT, hR, hExtPPT, hmem, ν, hν, hamp⟩ :=
      hH.kilianRawAmplifiedExtraction hV hpcp.coins_le hP p q hp hq_pb
        (by norm_num : (1 : ℕ) < 2)
    exact ⟨T, R_rep, hT, hR, hExtPPT, fun n ext hex =>
      ⟨hmem n ext hex, hwit_fn ext (hmem n ext hex)⟩, ν, hν, hamp⟩

end Cslib.Crypto
