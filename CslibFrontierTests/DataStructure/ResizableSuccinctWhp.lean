/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: local-only (test)

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
import CslibFrontier.Probability.PMF.Map
import Mathlib.Tactic.Linarith

public section

namespace CslibFrontierTests.DataStructure.ResizableSuccinctWhp

open Cslib Cslib.WordRAM Cslib.WordRAM.Resizable Cslib.Probability
open Cslib.DataStructure
open Cslib.DataStructure.WordRAM.Resizable
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.Dynamic
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
open scoped ENNReal

/-!
# End-to-End Deamortized WHP Resizable Succinct Dictionary Tests

Exercises the ordinary `public import` API (`0` `import all`) of
`CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp`:
1. Width-independence (`¬ReadsWidth`) of `initCodeWhp`, `opCodeWhp`, `subroutineCodeWhp`, and
   `subroutineCodeWhpStandard`.
2. Concrete 9-operation sequential lifecycle (`insert` with full-word maximum value `2 ^ 64 - 1`,
   hit and miss `query`, and `delete`) at `(c, U, V, w, base) = (2, 64, 2 ^ 64, 64, 100)` with
   caller-prefix sentinel `mem 42 = 777`, `1 · OPT` bit-space bounds, and flat-program demonic
   adversary halting (`ExecRCodeSteps.one_sub_le_evalRandDemonic_program`).
3. `Basis.standard` (`seq_whp_succinct_standard`) and compiled flat-`RProgram`
   (`HighProbObliviousImpl.seq_toExecWhpProgramSteps`) instantiation.
4. Non-vacuous large-universe hashed-regime instantiation at `U = whpThreshold 2`,
   `w = whpThreshold 2 + 64`, `V = 2 ^ w`, `base = 100`, confirming `stepFailureProbWhp` evaluates
   to the non-zero `(whpThreshold 2)⁻¹ ^ 2` bound while `seq_whp_succinct` holds.
5. `.halt`-stub rejection (`not_execWhpProgramSteps_halt`) confirming `[.halt rOutFlag]` cannot
   satisfy `ExecWhpProgramSteps` for `[.query k0]` after `[.insert k0 42]`.
-/

/-! ### Test 1: Width-independence (`¬ReadsWidth`) -/

theorem test_not_readsWidth (c U V w : ℕ) :
    ¬(initCodeWhp c U V w).ReadsWidth ∧
    ¬opCodeWhp.ReadsWidth ∧
    ¬(subroutineCodeWhp c U V w).ReadsWidth ∧
    ¬(subroutineCodeWhpStandard c U V w).ReadsWidth :=
  ⟨not_readsWidth_initCodeWhp c U V w,
   not_readsWidth_opCodeWhp,
   not_readsWidth_subroutineCodeWhp c U V w,
   not_readsWidth_subroutineCodeWhpStandard c U V w⟩

/-! ### Test 2: Concrete 64-bit lifecycle, `1 · OPT` bit bounds, and demonic `initCodeWhp` -/

abbrev k0 : Fin 64 := ⟨0, by decide⟩
abbrev k1 : Fin 64 := ⟨1, by decide⟩
abbrev k2 : Fin 64 := ⟨2, by decide⟩
abbrev k9 : Fin 64 := ⟨9, by decide⟩

/-- 9-operation sequence exercising `insert`, full-word overwrite (`2 ^ 64 - 1`), hit/miss `query`,
and `delete` at `(c, U, V, w, base) = (2, 64, 2 ^ 64, 64, 100)`. -/
def whpLifecycleOps : List (Dynamic.Op 64) :=
  [ .insert k0 100
  , .insert k1 200
  , .insert k2 (2 ^ 64 - 1)
  , .insert k0 42
  , .query k0
  , .query k2
  , .query k9
  , .delete k0
  , .query k0 ]

/-- Caller state at `base = 100` storing sentinel value `777` at caller address `42 < 100`. -/
def testWhpInit : RData rWhp where
  regs := fun _ => 0
  mem := fun a => if a = 42 then 777 else 0
  frontier := 100

theorem testWhpInit_bounded : testWhpInit.Bounded 64 := by
  refine ⟨⟨fun _ => show Fits 64 0 by decide, fun a => ?_⟩,
    show Fits 64 100 by decide, fun a ha => ?_⟩
  · dsimp only [testWhpInit, RData.toData]; split_ifs <;> decide
  · change (if a = 42 then 777 else 0) = 0
    have hne : a ≠ 42 := by change 100 ≤ a at ha; omega
    simp [hne]

private def allInsertsLt {U : ℕ} (V : ℕ) : List (Dynamic.Op U) → Bool
  | [] => true
  | .insert _ v :: tl => decide (v < V) && allInsertsLt V tl
  | _ :: tl => allInsertsLt V tl

private theorem validHistory_of_allInsertsLt {U V : ℕ} (s : Dictionary.State U)
    (ops : List (Dynamic.Op U)) (h : allInsertsLt V ops = true) :
    (Dynamic.spec U V U).ValidHistory s ops := by
  induction ops generalizing s with
  | nil => trivial
  | cons o tl ih =>
    cases o with
    | query u => exact ⟨trivial, ih _ h⟩
    | delete u => exact ⟨trivial, ih _ h⟩
    | insert u v =>
      simp only [allInsertsLt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨(Dynamic.valid_insert_iff_of_le le_rfl s u v).mpr h.1, ih _ h.2⟩

theorem validHistory_whpLifecycleOps :
    (Dynamic.spec 64 (2 ^ 64) 64).ValidHistory (Dictionary.empty 64) whpLifecycleOps :=
  validHistory_of_allInsertsLt (Dictionary.empty 64) whpLifecycleOps (by decide)

private theorem fits_whpSuccinct_of_le_three {m : ℕ} (hm : m ≤ 3) :
    Fits 64 (100 + Dynamic.succinctWords (whpResizableSpaceFactor 2) whpResizableSpaceConst
      64 (2 ^ 64) 64 m) := by
  have hm_cases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hm_cases with rfl | rfl | rfl | rfl <;> decide

private def cardsLeThree (st : Dictionary.State 64) : List (Dynamic.Op 64) → Bool
  | [] => true
  | o :: tl =>
    let st' := ((Dynamic.spec 64 (2 ^ 64) 64).stepFn st o).1
    decide ((Dictionary.dom st).card ≤ 3) &&
      decide ((Dictionary.dom st').card ≤ 3) &&
      cardsLeThree st' tl

private theorem peakFitsHistory_of_cardsLeThree {s : Dictionary.State 64}
    {ops : List (Dynamic.Op 64)} (h : cardsLeThree s ops = true) :
    PeakFitsHistory (D := Dynamic.spec 64 (2 ^ 64) 64) 64 100
      (stepSuccinctPeakWordsWhp 2 (2 ^ 64) 64) s ops := by
  induction ops generalizing s with
  | nil => trivial
  | cons o tl ih =>
    simp only [cardsLeThree, Bool.and_eq_true, decide_eq_true_eq] at h
    have hpeak : stepSuccinctPeakWordsWhp 2 (2 ^ 64) 64 s o ≤
        max (Dynamic.succinctWords (whpResizableSpaceFactor 2) whpResizableSpaceConst
              64 (2 ^ 64) 64 (Dictionary.dom s).card)
            (Dynamic.succinctWords (whpResizableSpaceFactor 2) whpResizableSpaceConst
              64 (2 ^ 64) 64
              (Dictionary.dom ((Dynamic.spec 64 (2 ^ 64) 64).stepFn s o).1).card) := le_rfl
    have hfit1 := fits_whpSuccinct_of_le_three h.1.1
    have hfit2 := fits_whpSuccinct_of_le_three h.1.2
    have hfit_max : Fits 64 (100 + stepSuccinctPeakWordsWhp 2 (2 ^ 64) 64 s o) := by
      unfold Fits at hfit1 hfit2 ⊢
      rcases max_cases
        (Dynamic.succinctWords (whpResizableSpaceFactor 2) whpResizableSpaceConst
          64 (2 ^ 64) 64 (Dictionary.dom s).card)
        (Dynamic.succinctWords (whpResizableSpaceFactor 2) whpResizableSpaceConst
          64 (2 ^ 64) 64
          (Dictionary.dom ((Dynamic.spec 64 (2 ^ 64) 64).stepFn s o).1).card)
        with ⟨heq, _⟩ | ⟨heq, _⟩ <;> omega
    exact ⟨hfit_max, ih h.2⟩

theorem peakFitsHistory_whpLifecycleOps :
    PeakFitsHistory (D := Dynamic.spec 64 (2 ^ 64) 64) 64 100
      (stepSuccinctPeakWordsWhp 2 (2 ^ 64) 64) (Dictionary.empty 64) whpLifecycleOps :=
  peakFitsHistory_of_cardsLeThree (by decide)

theorem fits_init_whp :
    Fits 64 (100 + spaceBoundWhp 2 (2 ^ 64) 64 (Dictionary.empty 64)) := by
  change Fits 64 (100 + Dynamic.succinctWords (whpResizableSpaceFactor 2) whpResizableSpaceConst
    64 (2 ^ 64) 64 (Dictionary.dom (Dictionary.empty 64)).card)
  have hc0 : (Dictionary.dom (Dictionary.empty 64)).card = 0 := by decide
  rw [hc0]
  exact fits_whpSuccinct_of_le_three (Nat.zero_le 3)

/-- End-to-end check of `seq_whp_succinct`, `w_mul_spaceBoundWhp_le_bits`, caller `[0, base)`
preservation (`tr.data.mem 42 = 777`), exact transcript, and `evalRandDemonic` halting of
`initCodeWhp` against every adaptive `.grow` adversary `adv : RAdv rWhp`. -/
theorem test_seq_whp_succinct_and_demonic_init (adv : RAdv rWhp) :
    let C := highProbImpl (c := 2) (U := 64) (V := 2 ^ 64) (w := 64) (base := 100)
      (by decide) (by decide) (by decide) (by decide) le_rfl
    let s_fin := ((Dynamic.spec 64 (2 ^ 64) 64).run (Dictionary.empty 64) whpLifecycleOps).1
    let failSum := totalFailureProb
      (fun pref o =>
        stepFailureProbWhp 2 ((Dynamic.spec 64 (2 ^ 64) 64).run (Dictionary.empty 64) pref).1 o)
      [] whpLifecycleOps
    (64 * spaceBoundWhp 2 (2 ^ 64) 64 s_fin ≤
      Dynamic.optBits 64 (2 ^ 64) 2 +
        whpResizableSpaceFactor 2 * 2 * Dynamic.logLogFactor 2 +
        (whpResizableSpaceConst + 1) * 64) ∧
    (1 ≤ (evalRandDemonic 64 adv ((initCodeWhp 2 64 (2 ^ 64) 64).program rOutFlag)
      (initStepsWhp + 1) ⟨0, testWhpInit⟩).toOuterMeasure
      {cfg | ∃ y, cfg = .halted (y.regs rOutFlag) y ∧ y.mem 42 = 777}) ∧
    ∃ (ν₀ : PMF (LatentRState (DualLatent 2 64 (2 ^ 64)) rWhp))
      (τ_final : PMF (WhpSeqROutcome (DualLatent 2 64 (2 ^ 64)) (Dynamic.Op.Result (U := 64))
        rWhp)),
      C.Steps whpLifecycleOps (ν₀.map WhpSeqROutcome.ofLatentRState) τ_final ∧
      (∀ tr ∈ τ_final.support,
        tr.data.Bounded 64 ∧
        tr.data.frontier ≤ 100 + spaceBoundWhp 2 (2 ^ 64) 64 s_fin ∧
        tr.data.regs mBaseWhp = 100 ∧
        tr.data.mem 42 = 777 ∧
        tr.transcript =
          [ ⟨.insert k0 100, ()⟩
          , ⟨.insert k1 200, ()⟩
          , ⟨.insert k2 (2 ^ 64 - 1), ()⟩
          , ⟨.insert k0 42, ()⟩
          , ⟨.query k0, some 42⟩
          , ⟨.query k2, some (2 ^ 64 - 1)⟩
          , ⟨.query k9, none⟩
          , ⟨.delete k0, ()⟩
          , ⟨.query k0, none⟩ ]) ∧
      1 - failSum ≤ τ_final.toOuterMeasure {tr | tr.allWithinBudget = true} := by
  intro C s_fin failSum
  have hcard_fin : (Dictionary.dom s_fin).card = 2 := by decide
  have hbits : 64 * spaceBoundWhp 2 (2 ^ 64) 64 s_fin ≤
      Dynamic.optBits 64 (2 ^ 64) 2 +
        whpResizableSpaceFactor 2 * 2 * Dynamic.logLogFactor 2 +
        (whpResizableSpaceConst + 1) * 64 := by
    simpa only [hcard_fin] using w_mul_spaceBoundWhp_le_bits 2 (2 ^ 64) 64 s_fin
  obtain ⟨ν₀, τ_final, he_init, hcaller₀, hex, hfin, _, hsucc⟩ :=
    seq_whp_succinct 2 whpLifecycleOps (by decide) (by decide) (by decide) (by decide) le_rfl
      testWhpInit_bounded rfl fits_init_whp validHistory_whpLifecycleOps
      peakFitsHistory_whpLifecycleOps
  have hdemonic :
      1 ≤ (evalRandDemonic 64 adv ((initCodeWhp 2 64 (2 ^ 64) 64).program rOutFlag)
        (initStepsWhp + 1) ⟨0, testWhpInit⟩).toOuterMeasure
        {cfg | ∃ y, cfg = .halted (y.regs rOutFlag) y ∧ y.mem 42 = 777} := by
    have h0 : 1 - (0 : ℝ≥0∞) ≤ _ :=
      he_init.one_sub_le_evalRandDemonic_program (Q := fun y => y.mem 42 = 777) (δ := 0)
        rOutFlag initStepsWhp adv
        (fun z hz => by
          rw [PMF.mem_support_map_iff] at hz
          obtain ⟨t, ht, rfl⟩ := hz
          exact hcaller₀ t ht 42 (by decide))
        (by
          rw [PMF.toOuterMeasure_apply, tsum_eq_zero_iff.mpr fun z => by
            by_cases hm : z ∈ {z' : RCodeStepOutcome rWhp | ¬z'.WithinBudget initStepsWhp}
            · rw [Set.indicator_of_mem hm]
              by_contra hne
              have hz : z ∈ (ν₀.map fun t => (⟨t.data, initStepsWhp, true⟩ :
                  RCodeStepOutcome rWhp)).support := (PMF.mem_support_iff _ _).mpr hne
              rw [PMF.mem_support_map_iff] at hz
              obtain ⟨t, _, rfl⟩ := hz
              exact hm ⟨rfl, le_rfl⟩
            · exact Set.indicator_of_notMem hm _])
    simpa only [tsub_zero] using h0
  have hrun_out :
      ((Dynamic.spec 64 (2 ^ 64) 64).run (Dictionary.empty 64) whpLifecycleOps).2 =
        [ ⟨.insert k0 100, ()⟩, ⟨.insert k1 200, ()⟩, ⟨.insert k2 (2 ^ 64 - 1), ()⟩,
          ⟨.insert k0 42, ()⟩, ⟨.query k0, some 42⟩, ⟨.query k2, some (2 ^ 64 - 1)⟩,
          ⟨.query k9, none⟩, ⟨.delete k0, ()⟩, ⟨.query k0, none⟩ ] := rfl
  refine ⟨hbits, hdemonic, ν₀, τ_final, hex, fun tr htr => ?_, hsucc⟩
  obtain ⟨hbdd, ⟨_, hhi, hreg⟩, hmem, htr_eq⟩ := hfin tr htr
  rw [hrun_out] at htr_eq
  exact ⟨hbdd, hhi, hreg, hmem 42 (by decide), htr_eq⟩

/-! ### Test 3: `Basis.standard` and compiled flat-`RProgram` (`seq_toExecWhpProgramSteps`) -/

theorem test_standard_and_program_whp_lifecycle :
    let C_std := highProbImplStandard (c := 2) (U := 64) (V := 2 ^ 64) (w := 64) (base := 100)
      (by decide) (by decide) (by decide) (by decide) le_rfl
    (∃ (ν₀ : PMF (LatentRState (DualLatent 2 64 (2 ^ 64)) rWhp))
       (τ_final : PMF (WhpSeqROutcome (DualLatent 2 64 (2 ^ 64))
         (Dynamic.Op.Result (U := 64)) rWhp)),
       C_std.Steps whpLifecycleOps (ν₀.map WhpSeqROutcome.ofLatentRState) τ_final) ∧
    (∃ (ν₀ : PMF (LatentRState (DualLatent 2 64 (2 ^ 64)) rWhp))
       (τ_final : PMF (WhpSeqROutcome (DualLatent 2 64 (2 ^ 64))
         (Dynamic.Op.Result (U := 64)) rWhp)),
       C_std.ProgramSteps ((subroutineCodeWhpStandard 2 64 (2 ^ 64) 64).opProg rOutFlag) rOutFlag
         whpLifecycleOps (ν₀.map WhpSeqROutcome.ofLatentRState) τ_final) := by
  intro C_std
  have hv_seq :
      ((Dynamic.spec 64 (2 ^ 64) 64).toObliviousSequenceSpec (Dictionary.empty 64)).ValidOpSeq
        whpLifecycleOps :=
    ((Dynamic.spec 64 (2 ^ 64) 64).validOpSeq_iff_validHistory (Dictionary.empty 64)
      whpLifecycleOps).mpr validHistory_whpLifecycleOps
  have hob_fit : ObliviousPeakFits 64 100 C_std.peakSpaceBound [] whpLifecycleOps :=
    obliviousPeakFits_of_succinctWords peakFitsHistory_whpLifecycleOps
  have hfit₀ : Fits 64 (100 + C_std.spaceBound []) := by
    change Fits 64 (100 + spaceBoundWhp 2 (2 ^ 64) 64
      ((Dynamic.spec 64 (2 ^ 64) 64).run (Dictionary.empty 64) []).1)
    rw [(Dynamic.spec 64 (2 ^ 64) 64).run_nil]
    exact fits_init_whp
  obtain ⟨ν₀, τ_final, _, _, hex, _, _, _⟩ :=
    seq_whp_succinct_standard 2 whpLifecycleOps (by decide) (by decide) (by decide) (by decide)
      le_rfl testWhpInit_bounded rfl fits_init_whp validHistory_whpLifecycleOps
      peakFitsHistory_whpLifecycleOps
  obtain ⟨ν₀', τ_final', _, _, hprog, _, _, _⟩ :=
    C_std.seq_toExecWhpProgramSteps rOutFlag whpLifecycleOps testWhpInit_bounded rfl
      (fun j => Fin.elim0 j) hfit₀ hv_seq hob_fit
  exact ⟨⟨ν₀, τ_final, hex⟩, ⟨ν₀', τ_final', hprog⟩⟩

/-! ### Test 4: Non-vacuous large-universe hashed-regime instances (`whpThreshold c ≤ U`) -/

private theorem c100_lt_pow64 : 100 < 2 ^ 64 := by decide
private theorem c42_lt_pow64 : 42 < 2 ^ 64 := by decide
private theorem c1124_lt_pow64 : 1124 < 2 ^ 64 := by decide
private theorem c_pow63_le_pow64 : (2 ^ 63 : ℕ) ≤ 2 ^ 64 := by decide
private theorem whpSpaceFactor1_lt : whpResizableSpaceFactor 1 + 1130 < 2 ^ 63 := by decide

private theorem large_universe_hashed_aux (U V w : ℕ)
    (hU : U = whpThreshold 2) (hw : w = U + 64) (hV : V = 2 ^ w) :
    ∃ (kL : Fin U) (_ν₀ : PMF (LatentRState (DualLatent 2 U V) rWhp))
      (τ_final : PMF (WhpSeqROutcome (DualLatent 2 U V) (Dynamic.Op.Result (U := U)) rWhp)),
      stepFailureProbWhp 2 (Dictionary.empty U) (.query kL) =
        (((whpThreshold 2 : ℕ) : ℝ≥0∞)⁻¹ ^ 2) ∧
      (∀ tr ∈ τ_final.support, tr.transcript = [⟨.query kL, none⟩]) ∧
      1 - (((whpThreshold 2 : ℕ) : ℝ≥0∞)⁻¹ ^ 2) ≤
        τ_final.toOuterMeasure {tr | tr.allWithinBudget = true} := by
  have hU0 : 0 < U := hU ▸ whpThreshold_pos 2
  let kL : Fin U := ⟨0, hU0⟩
  let opsL : List (Dynamic.Op U) := [.query kL]
  have hnot_lt : ¬(U < whpThreshold 2) := hU ▸ lt_irrefl U
  have hdom0 : (Dictionary.dom (Dictionary.empty U)).card = 0 := by
    rw [Dictionary.dom_empty, Finset.card_empty]
  have hf_eq : stepFailureProbWhp 2 (Dictionary.empty U) (.query kL) =
      (((whpThreshold 2 : ℕ) : ℝ≥0∞)⁻¹ ^ 2) := by
    unfold stepFailureProbWhp
    rw [ite_eq_right hnot_lt, hdom0, Nat.zero_max]
  clear hU hnot_lt
  have hw11 : 11 ≤ w := by omega
  have hUw : Fits w U :=
    Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hV0 : 0 < V := hV ▸ Nat.two_pow_pos w
  have hVw : V ≤ 2 ^ w := hV.le
  let xL : RData rWhp := { regs := fun _ => 0, mem := fun _ => 0, frontier := 100 }
  have hpow64 : 2 ^ 64 ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
  have hxL_bdd : xL.Bounded w :=
    ⟨⟨fun _ => fits_zero w, fun _ => fits_zero w⟩,
     lt_of_lt_of_le c100_lt_pow64 hpow64, fun _ _ => rfl⟩
  have hsb0 : spaceBoundWhp 2 V w (Dictionary.empty U) = 1024 := by
    unfold spaceBoundWhp Dynamic.succinctWords whpResizableSpaceConst
    rw [hdom0, Dynamic.optBits_zero_right, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
      Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hfit0 : Fits w (100 + spaceBoundWhp 2 V w (Dictionary.empty U)) := by
    rw [Fits, hsb0]; exact lt_of_lt_of_le c1124_lt_pow64 hpow64
  have hpeak : PeakFitsHistory (D := Dynamic.spec U V U) w 100
      (stepSuccinctPeakWordsWhp 2 V w) (Dictionary.empty U) opsL := by
    refine ⟨?_, trivial⟩
    unfold stepSuccinctPeakWordsWhp
    change Fits w (100 + max (spaceBoundWhp 2 V w (Dictionary.empty U))
      (spaceBoundWhp 2 V w (Dictionary.empty U)))
    rw [max_self]; exact hfit0
  obtain ⟨ν₀, τ_final, _, _, _, hfin, _, hsucc⟩ :=
    seq_whp_succinct 2 opsL hw11 hU0 hUw hV0 hVw hxL_bdd rfl hfit0 ⟨trivial, trivial⟩ hpeak
  refine ⟨kL, ν₀, τ_final, hf_eq, fun tr htr => (hfin tr htr).2.2.2, ?_⟩
  have htot : totalFailureProb
      (fun pref o => stepFailureProbWhp 2 ((Dynamic.spec U V U).run (Dictionary.empty U) pref).1 o)
      [] opsL = (((whpThreshold 2 : ℕ) : ℝ≥0∞)⁻¹ ^ 2) := by
    dsimp only [opsL, totalFailureProb]
    rw [(Dynamic.spec U V U).run_nil, hf_eq, add_zero]
  rwa [htot] at hsucc

/-- Confirms that at `U = whpThreshold 2`, `w = U + 64`, `V = 2 ^ w`, `base = 100`,
`stepFailureProbWhp` takes the non-zero hashed-regime value `((whpThreshold 2) : ℝ≥0∞)⁻¹ ^ 2`
while all hypotheses of `seq_whp_succinct` hold simultaneously. -/
theorem test_large_universe_hashed_regime :
    ∃ (U V : ℕ) (kL : Fin U)
      (_ν₀ : PMF (LatentRState (DualLatent 2 U V) rWhp))
      (τ_final : PMF (WhpSeqROutcome (DualLatent 2 U V) (Dynamic.Op.Result (U := U)) rWhp)),
      U = whpThreshold 2 ∧
      stepFailureProbWhp 2 (Dictionary.empty U) (.query kL) =
        (((whpThreshold 2 : ℕ) : ℝ≥0∞)⁻¹ ^ 2) ∧
      (∀ tr ∈ τ_final.support, tr.transcript = [⟨.query kL, none⟩]) ∧
      1 - (((whpThreshold 2 : ℕ) : ℝ≥0∞)⁻¹ ^ 2) ≤
        τ_final.toOuterMeasure {tr | tr.allWithinBudget = true} := by
  obtain ⟨kL, ν₀, τ_final, hf, htr, hsucc⟩ :=
    large_universe_hashed_aux (whpThreshold 2) (2 ^ (whpThreshold 2 + 64)) (whpThreshold 2 + 64)
      rfl rfl rfl
  exact ⟨_, _, kL, ν₀, τ_final, rfl, hf, htr, hsucc⟩

private theorem run_map_insert_not_mem {U V : ℕ} {k : Fin U} (val : ℕ)
    {l : List (Fin U)} (hnot : k ∉ l) (s : Dictionary.State U) :
    ((Dynamic.spec U V U).run s (l.map fun i => Dynamic.Op.insert i val)).1 k = s k := by
  induction l generalizing s with
  | nil => rfl
  | cons a tl ih =>
    have hne : k ≠ a := fun h => hnot (h ▸ List.mem_cons_self)
    have hnot_tl : k ∉ tl := fun h => hnot (List.mem_cons_of_mem a h)
    rw [List.map_cons, StateTransitionSpec.run_cons]
    exact (ih hnot_tl _).trans (Function.update_of_ne hne (some val) s)

private theorem run_map_insert_mem {U V : ℕ} {k : Fin U} (val : ℕ)
    {l : List (Fin U)} (hmem : k ∈ l) (s : Dictionary.State U) :
    ((Dynamic.spec U V U).run s (l.map fun i => Dynamic.Op.insert i val)).1 k = some val := by
  induction l generalizing s with
  | nil => nomatch hmem
  | cons a tl ih =>
    rw [List.map_cons, StateTransitionSpec.run_cons]
    by_cases hktl : k ∈ tl
    · exact ih hktl _
    · have hka : k = a := (List.mem_cons.mp hmem).resolve_right hktl
      subst hka
      exact (run_map_insert_not_mem val hktl _).trans (Function.update_self k (some val) s)

private theorem validHistory_map_insert {U V : ℕ} {val : ℕ} (hval : val < V)
    (l : List (Fin U)) (s : Dictionary.State U) :
    (Dynamic.spec U V U).ValidHistory s (l.map fun i => Dynamic.Op.insert i val) := by
  induction l generalizing s with
  | nil => trivial
  | cons a tl ih =>
    exact ⟨(Dynamic.valid_insert_iff_of_le le_rfl s a val).mpr hval, ih _⟩

private theorem clog2_le_self (m : ℕ) : Nat.clog 2 m ≤ m :=
  (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr Nat.lt_two_pow_self.le

private theorem fits_whpSuccinct_all_states_aux {U V w : ℕ}
    (hw : w = U + 64) (hV : V = 2 ^ w) (s : Dictionary.State U) :
    Fits w (100 + spaceBoundWhp 1 V w s) := by
  set n := (Dictionary.dom s).card
  have hw_pos : 0 < w := by omega
  have hn_le : n ≤ U := Dynamic.card_dom_le_univ s
  have hbits := w_mul_spaceBoundWhp_le_bits 1 V w s
  have hclog_ch : Nat.clog 2 (U.choose n) ≤ U :=
    (Nat.clog_mono_right 2 (Nat.choose_le_two_pow U n)).trans
      (by rw [Nat.clog_pow 2 U Nat.one_lt_two])
  have hclog_V : Nat.clog 2 V = w := by rw [hV, Nat.clog_pow 2 w Nat.one_lt_two]
  have hopt_le : Dynamic.optBits U V n ≤ w + U * w := by
    unfold Dynamic.optBits
    rw [hclog_V]
    have h1 : Nat.clog 2 (U.choose n) ≤ w := by omega
    have h2 : n * w ≤ U * w := Nat.mul_le_mul_right w hn_le
    omega
  have hll_le : Dynamic.logLogFactor n ≤ w := by
    unfold Dynamic.logLogFactor
    have hc1 : Nat.clog 2 (Nat.clog 2 (max n 4)) ≤ max n 4 :=
      (clog2_le_self _).trans (clog2_le_self _)
    omega
  have hterm : whpResizableSpaceFactor 1 * n * Dynamic.logLogFactor n ≤
      (whpResizableSpaceFactor 1 * U) * w := by
    calc whpResizableSpaceFactor 1 * n * Dynamic.logLogFactor n
        ≤ whpResizableSpaceFactor 1 * U * Dynamic.logLogFactor n :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn_le)
      _ ≤ (whpResizableSpaceFactor 1 * U) * w := Nat.mul_le_mul_left _ hll_le
  have hmul_le : w * spaceBoundWhp 1 V w s ≤
      w * (whpResizableSpaceFactor 1 * U + U + 1026) := by
    dsimp only [whpResizableSpaceConst] at hbits
    nlinarith
  have hsb_le : spaceBoundWhp 1 V w s ≤ whpResizableSpaceFactor 1 * U + U + 1026 :=
    Nat.le_of_mul_le_mul_left hmul_le hw_pos
  have hU_lt_pow : U + 1 ≤ 2 ^ U := Nat.lt_two_pow_self
  unfold Fits
  calc 100 + spaceBoundWhp 1 V w s
      ≤ (whpResizableSpaceFactor 1 + 1130) * (U + 1) := by nlinarith
    _ < 2 ^ 63 * (U + 1) := (Nat.mul_lt_mul_right (by omega)).mpr whpSpaceFactor1_lt
    _ ≤ 2 ^ 64 * 2 ^ U := by nlinarith [c_pow63_le_pow64]
    _ = 2 ^ w := by rw [hw, Nat.add_comm U 64, Nat.pow_add]

private theorem large_nt_hashed_aux (U V w : ℕ)
    (hU : U = whpThreshold 1) (hw : w = U + 64) (hV : V = 2 ^ w) :
    ∃ (opsBig : List (Dynamic.Op U))
      (hw11 : 11 ≤ w) (hU0 : 0 < U) (hUw : Fits w U) (hV0 : 0 < V) (hVw : V ≤ 2 ^ w)
      (ν₀ : PMF (LatentRState (DualLatent 1 U V) rWhp))
      (τ_final : PMF (WhpSeqROutcome (DualLatent 1 U V) (Dynamic.Op.Result (U := U)) rWhp)),
      whpThreshold 1 ≤
        (Dictionary.dom ((Dynamic.spec U V U).run (Dictionary.empty U) opsBig).1).card ∧
      (highProbImplStandard (c := 1) (U := U) (V := V) (w := w) (base := 100)
        hw11 hU0 hUw hV0 hVw).Steps
        opsBig (ν₀.map WhpSeqROutcome.ofLatentRState) τ_final ∧
      ∀ tr ∈ τ_final.support,
        tr.transcript = ((Dynamic.spec U V U).run (Dictionary.empty U) opsBig).2 := by
  have hU0 : 0 < U := hU ▸ whpThreshold_pos 1
  have hw11 : 11 ≤ w := by omega
  have hUw : Fits w U :=
    Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hV0 : 0 < V := hV ▸ Nat.two_pow_pos w
  have hVw : V ≤ 2 ^ w := hV.le
  let k0L : Fin U := ⟨0, hU0⟩
  let opsBig : List (Dynamic.Op U) :=
    (List.finRange U).map (fun i => Dynamic.Op.insert i 42) ++ [.query k0L]
  let s_fin := ((Dynamic.spec U V U).run (Dictionary.empty U) opsBig).1
  have hs_fin_val : ∀ k : Fin U, s_fin k = some 42 := fun k => by
    dsimp only [s_fin, opsBig]
    rw [StateTransitionSpec.run_append]
    exact run_map_insert_mem (V := V) 42 (List.mem_finRange k) (Dictionary.empty U)
  have hdom_eq : Dictionary.dom s_fin = Finset.univ := by
    unfold Dictionary.dom
    rw [Finset.filter_eq_self]
    intro k _; rw [hs_fin_val k]; rfl
  have hcard_ge : whpThreshold 1 ≤ (Dictionary.dom s_fin).card := by
    rw [hdom_eq, Finset.card_univ, Fintype.card_fin, hU]
  let xL : RData rWhp := { regs := fun _ => 0, mem := fun _ => 0, frontier := 100 }
  have hpow64 : 2 ^ 64 ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
  have hxL_bdd : xL.Bounded w :=
    ⟨⟨fun _ => fits_zero w, fun _ => fits_zero w⟩,
     lt_of_lt_of_le c100_lt_pow64 hpow64, fun _ _ => rfl⟩
  have h42 : 42 < V := hV ▸ lt_of_lt_of_le c42_lt_pow64 hpow64
  have hvh : (Dynamic.spec U V U).ValidHistory (Dictionary.empty U) opsBig := by
    have hv1 := validHistory_map_insert (U := U) (V := V) h42 (List.finRange U)
      (Dictionary.empty U)
    have h_app : ∀ (l : List (Dynamic.Op U)) (s : Dictionary.State U),
        (Dynamic.spec U V U).ValidHistory s l →
        (Dynamic.spec U V U).ValidHistory s (l ++ [.query k0L]) := fun l => by
      induction l with
      | nil => intro _ _; exact ⟨trivial, trivial⟩
      | cons o tl ih => intro s ⟨ho, htl⟩; exact ⟨ho, ih _ htl⟩
    exact h_app _ _ hv1
  have hpeak : ∀ (l : List (Dynamic.Op U)) (s : Dictionary.State U),
      PeakFitsHistory (D := Dynamic.spec U V U) w 100
        (stepSuccinctPeakWordsWhp 1 V w) s l := fun l => by
    induction l with
    | nil => intro _; trivial
    | cons o tl ih =>
      intro s
      refine ⟨?_, ih _⟩
      unfold stepSuccinctPeakWordsWhp Fits
      have hf1 : 100 + spaceBoundWhp 1 V w s < 2 ^ w := fits_whpSuccinct_all_states_aux hw hV s
      have hf2 : 100 + spaceBoundWhp 1 V w ((Dynamic.spec U V U).stepFn s o).1 < 2 ^ w :=
        fits_whpSuccinct_all_states_aux hw hV _
      rcases max_cases (spaceBoundWhp 1 V w s)
        (spaceBoundWhp 1 V w ((Dynamic.spec U V U).stepFn s o).1) with
        ⟨heq, _⟩ | ⟨heq, _⟩ <;> omega
  obtain ⟨ν₀, τ_final, _, _, hex, hfin, _, _⟩ :=
    seq_whp_succinct_standard 1 opsBig hw11 hU0 hUw hV0 hVw hxL_bdd rfl
      (fits_whpSuccinct_all_states_aux hw hV _) hvh (hpeak opsBig _)
  exact ⟨opsBig, hw11, hU0, hUw, hV0, hVw, ν₀, τ_final, hcard_ge, hex,
    fun tr htr => (hfin tr htr).2.2.2⟩

/-- Non-vacuity at **large `n_t ≥ whpThreshold 1`**: inserting all `whpThreshold 1` keys reaches a
live state `s_fin` with `#(dom s_fin) ≥ whpThreshold 1` in the hashed epoch regime while satisfying
every hypothesis of `seq_whp_succinct` and `seq_whp_succinct_standard`. -/
theorem test_large_nt_hashed_regime :
    ∃ (U V w : ℕ) (opsBig : List (Dynamic.Op U))
      (hw11 : 11 ≤ w) (hU0 : 0 < U) (hUw : Fits w U) (hV0 : 0 < V) (hVw : V ≤ 2 ^ w)
      (ν₀ : PMF (LatentRState (DualLatent 1 U V) rWhp))
      (τ_final : PMF (WhpSeqROutcome (DualLatent 1 U V) (Dynamic.Op.Result (U := U)) rWhp)),
      U = whpThreshold 1 ∧
      whpThreshold 1 ≤
        (Dictionary.dom ((Dynamic.spec U V U).run (Dictionary.empty U) opsBig).1).card ∧
      (highProbImplStandard (c := 1) (U := U) (V := V) (w := w) (base := 100)
        hw11 hU0 hUw hV0 hVw).Steps
        opsBig (ν₀.map WhpSeqROutcome.ofLatentRState) τ_final ∧
      ∀ tr ∈ τ_final.support,
        tr.transcript = ((Dynamic.spec U V U).run (Dictionary.empty U) opsBig).2 := by
  obtain ⟨opsBig, hw11, hU0, hUw, hV0, hVw, ν₀, τ_final, hcard, hex, htr⟩ :=
    large_nt_hashed_aux (whpThreshold 1) (2 ^ (whpThreshold 1 + 64)) (whpThreshold 1 + 64)
      rfl rfl rfl
  exact ⟨_, _, _, opsBig, hw11, hU0, hUw, hV0, hVw, ν₀, τ_final, rfl, hcard, hex, htr⟩

/-! ### Test 5: `.halt`-rejection soundness check (`not_execWhpProgramSteps_halt`) -/

/-- Soundness check: a 1-instruction `[.halt rOutFlag]` no-op stub cannot satisfy
`ExecWhpProgramSteps` for `[.query k0]` after `[.insert k0 42]` from any state distribution `τ`
with `tr.data.regs rOutFlag = 0`, because `prepare` preserves `rOutFlag = 0` (`whpInput rOutFlag =
false`), decoding `none` whereas `Contract` requires `some 42`. -/
theorem test_halt_stub_rejected
    (τ : PMF (WhpSeqROutcome (DualLatent 2 64 (2 ^ 64)) (Dynamic.Op.Result (U := 64)) rWhp))
    (τ_final : PMF (WhpSeqROutcome (DualLatent 2 64 (2 ^ 64)) (Dynamic.Op.Result (U := 64)) rWhp))
    (ht_tr : ∀ tr ∈ τ.support,
      tr.transcript = [⟨.insert k0 42, ()⟩] ∧ tr.data.regs rOutFlag = 0)
    (hcontract :
      ((Dynamic.spec 64 (2 ^ 64) 64).toObliviousSequenceSpec (Dictionary.empty 64)).Contract
        [.insert k0 42, .query k0] (τ_final.map WhpSeqROutcome.transcript)) :
    let C := highProbImpl (c := 2) (U := 64) (V := 2 ^ 64) (w := 64) (base := 100)
      (by decide) (by decide) (by decide) (by decide) le_rfl
    ¬ExecWhpProgramSteps (subroutineCodeWhp 2 64 (2 ^ 64) 64)
      ((Dynamic.spec 64 (2 ^ 64) 64).toObliviousSequenceSpec (Dictionary.empty 64))
      (DualLatent 2 64 (2 ^ 64)) 64 100 C.spaceBound C.peakSpaceBound C.worstCaseTime
      whpEncode (whpDecode (V := 2 ^ 64)) [.halt rOutFlag] rOutFlag
      [.insert k0 42] [.query k0] τ τ_final := by
  intro C
  obtain ⟨tr, htr⟩ := τ.support_nonempty
  obtain ⟨htr_hist, htr_flag⟩ := ht_tr tr htr
  apply not_execWhpProgramSteps_halt (out := rOutFlag) htr
  intro a hdec _ _ u hu hpref
  have ha_none : a = none := by
    have hflag0 :
        ((subroutineCodeWhp 2 64 (2 ^ 64) 64).prepare whpEncode (.query k0) tr.data).regs
          rOutFlag = 0 := by
      dsimp only [Cslib.DataStructure.WordRAM.Resizable.SubroutineCode.prepare,
        Cslib.DataStructure.WordRAM.Resizable.SubroutineCode.prepareRegs]
      have hin_false : (subroutineCodeWhp 2 64 (2 ^ 64) 64).input rOutFlag = false := rfl
      rw [hin_false]; exact htr_flag
    have hdec' : whpDecode (V := 2 ^ 64) (.query k0)
        ((subroutineCodeWhp 2 64 (2 ^ 64) 64).prepare whpEncode (.query k0) tr.data).regs =
        some none := by
      unfold whpDecode
      dsimp only
      rw [hflag0, ite_eq_left rfl]
    exact Option.some.inj (hdec.symm.trans hdec')
  have hv_hist : (Dynamic.spec 64 (2 ^ 64) 64).ValidHistory (Dictionary.empty 64)
      [.insert k0 42, .query k0] :=
    validHistory_of_allInsertsLt (Dictionary.empty 64) [.insert k0 42, .query k0] (by decide)
  rw [(Dynamic.spec 64 (2 ^ 64) 64).toObliviousSequenceSpec_contract_iff_of_hasStepFn
    (Dictionary.empty 64) hv_hist] at hcontract
  have hu_tr : u.transcript = [⟨.insert k0 42, ()⟩, ⟨.query k0, some 42⟩] :=
    hcontract u.transcript ((PMF.mem_support_map_iff _ _ _).mpr ⟨u, hu, rfl⟩)
  rw [htr_hist, ha_none, hu_tr] at hpref
  obtain ⟨_, heq⟩ := hpref
  injection heq with _ htail
  injection htail with hhd _
  cases hhd

end CslibFrontierTests.DataStructure.ResizableSuccinctWhp

end
