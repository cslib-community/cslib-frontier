/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: local-only (test)

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct

public section

namespace CslibFrontierTests.DataStructure.ResizableSuccinct

open Cslib Cslib.WordRAM Cslib.WordRAM.Resizable Cslib.Probability
open Cslib.DataStructure
open Cslib.DataStructure.WordRAM.Resizable
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.Dynamic
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open scoped ENNReal

/-!
# End-to-End Resizable Succinct Dynamic Dictionary Tests

Exercises the ordinary `public import` API of
`CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct`:
1. Width-independence (`¬ReadsWidth`) of `initCode`, `subroutineCode`, and `subroutineCodeStandard`.
2. Concrete 15-operation sequential lifecycle (`0 → 1` creation, two capacity-doubling migrations
   `2 → 4 → 8`, in-place value overwrite, hit and miss queries, in-epoch deletions,
   capacity-halving migration `8 → 4`, and `1 → 0` singleton collapse) at `(U, V, w, base) =
   (64, 2 ^ 64, 64, 100)` with full-word `V = 2 ^ w` values and non-zero caller memory below `base`,
   instantiating `obliviousImpl`, `obliviousImplStandard`, `seq_expected_amortized`,
   `seq_expected_amortized_standard`, and `ObliviousSequenceImpl.seq_toExecRProgramDist`.
3. `.halt`-rejection soundness check (`Randomized.not_execProgramSteps_halt`) proving that a
   1-instruction `[.halt mOutTag]` stub cannot satisfy `ExecProgramSteps` on
   `[.insert k0 42, .query k0]`.
-/

/-! ### Test 1: Width-independence (`¬ReadsWidth`) -/

theorem test_not_readsWidth (U V w : ℕ) :
    ¬(initCode U V w).ReadsWidth ∧
    ¬(subroutineCode U V w).ReadsWidth ∧
    ¬(subroutineCodeStandard U V w).ReadsWidth :=
  ⟨not_readsWidth_initCode U V w,
   not_readsWidth_subroutineCode U V w,
   not_readsWidth_subroutineCodeStandard U V w⟩

/-! ### Test 2: Full lifecycle trace (`0 → 1`, doubling `2 → 4 → 8`, halving `8 → 4`, `1 → 0`) -/

abbrev k0 : Fin 64 := ⟨0, by decide⟩
abbrev k1 : Fin 64 := ⟨1, by decide⟩
abbrev k2 : Fin 64 := ⟨2, by decide⟩
abbrev k3 : Fin 64 := ⟨3, by decide⟩
abbrev k4 : Fin 64 := ⟨4, by decide⟩
abbrev k9 : Fin 64 := ⟨9, by decide⟩

/-- 15-operation sequence exercising `0 → 1` epoch creation, two capacity-doubling rebuilds
(`cap`: `0 → 2 → 4 → 8`), in-place overwrite with full-word maximum value `2 ^ 64 - 1`, hit/miss
queries, in-epoch deletions, capacity-halving rebuild (`cap`: `8 → 4` at `n = 2`), and `1 → 0`
collapse back to `cap = 0`. -/
def lifecycleOps : List (Dynamic.Op 64) :=
  [ .insert k0 100
  , .insert k1 200
  , .insert k2 300
  , .insert k3 400
  , .insert k4 500
  , .insert k0 (2 ^ 64 - 1)
  , .query k0
  , .query k4
  , .query k9
  , .delete k4
  , .delete k3
  , .delete k2
  , .delete k1
  , .delete k0
  , .query k0 ]

/-- Check that `EpochState.run` visits `cap = 2`, `4`, `8` (doubling), `4` (halving), and `0`
(empty collapse) along `lifecycleOps`. -/
theorem test_lifecycle_capacities :
    (EpochState.run (2 ^ 64) (EpochState.empty 64) (lifecycleOps.take 1)).cap = 2 ∧
    (EpochState.run (2 ^ 64) (EpochState.empty 64) (lifecycleOps.take 3)).cap = 4 ∧
    (EpochState.run (2 ^ 64) (EpochState.empty 64) (lifecycleOps.take 5)).cap = 8 ∧
    (EpochState.run (2 ^ 64) (EpochState.empty 64) (lifecycleOps.take 13)).cap = 4 ∧
    (EpochState.run (2 ^ 64) (EpochState.empty 64) lifecycleOps).cap = 0 := by
  decide

/-- Concrete caller state at `base = 100` storing sentinel value `777` at caller address `42 < 100`.
-/
def testInitState : RData rResize where
  regs := fun _ => 0
  mem := fun a => if a = 42 then 777 else 0
  frontier := 100

theorem testInitState_bounded : testInitState.Bounded 64 := by
  refine ⟨⟨fun _ => show Fits 64 0 by decide, fun a => ?_⟩,
    show Fits 64 100 by decide, fun a ha => ?_⟩
  · dsimp only [testInitState, RData.toData]; split_ifs <;> decide
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

theorem validHistory_lifecycleOps :
    (Dynamic.spec 64 (2 ^ 64) 64).ValidHistory (Dictionary.empty 64) lifecycleOps :=
  validHistory_of_allInsertsLt (Dictionary.empty 64) lifecycleOps (by decide)

private theorem fits_succinctPeak_of_le_five {m : ℕ} (hm : m ≤ 5) :
    Fits 64 (100 + Dynamic.succinctWords 2699 888 64 (2 ^ 64) 64 m) := by
  have hm_cases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases hm_cases with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private def cardsLeFive (st : Dictionary.State 64) : List (Dynamic.Op 64) → Bool
  | [] => true
  | o :: tl =>
    let st' := ((Dynamic.spec 64 (2 ^ 64) 64).stepFn st o).1
    decide ((Dictionary.dom st).card ≤ 5) &&
      decide ((Dictionary.dom st').card ≤ 5) &&
      cardsLeFive st' tl

private theorem peakFitsHistory_of_cardsLeFive {s : Dictionary.State 64}
    {ops : List (Dynamic.Op 64)} (h : cardsLeFive s ops = true) :
    PeakFitsHistory (D := Dynamic.spec 64 (2 ^ 64) 64) 64 100
      (stepSuccinctPeakWords (2 ^ 64) 64) s ops := by
  induction ops generalizing s with
  | nil => trivial
  | cons o tl ih =>
    simp only [cardsLeFive, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fits_succinctPeak_of_le_five (max_le h.1.1 h.1.2), ih h.2⟩

theorem peakFitsHistory_lifecycleOps :
    PeakFitsHistory (D := Dynamic.spec 64 (2 ^ 64) 64) 64 100
      (stepSuccinctPeakWords (2 ^ 64) 64) (Dictionary.empty 64) lifecycleOps :=
  peakFitsHistory_of_cardsLeFive (by decide)

/-- End-to-end verification of `seq_expected_amortized` and `seq_expected_amortized_standard` across
`lifecycleOps`, checking caller memory preservation (`t.data.mem 42 = 777`), resting `1 · OPT`
space, `O(1)` amortized instruction bound, and exact query outputs (`some (2 ^ 64 - 1)`,
`some 500`, `none`, `none`). -/
theorem test_seq_expected_amortized_lifecycle :
    let C := obliviousImpl (U := 64) (V := 2 ^ 64) (w := 64) (base := 100)
      (by decide) (by decide) (by decide) (by decide) le_rfl
    ∃ (ν₀ : PMF (LatentRState (LatentSeed 64) rResize))
      (ν_final : PMF (SeqROutcome (LatentSeed 64) (Dynamic.Op.Result (U := 64)) rResize))
      (T_ops : ℝ≥0∞),
      ExecRCodeDist 64 (initCode 64 (2 ^ 64) 64) testInitState
        (ν₀.map LatentRState.data) initSteps 108 ∧
      C.Steps lifecycleOps (ν₀.map SeqROutcome.ofLatentRState) ν_final T_ops ∧
      (∀ t ∈ ν_final.support,
        t.data.Bounded 64 ∧
        t.data.frontier ≤ 100 + Dynamic.succinctWords 1355 441 64 (2 ^ 64) 64 0 ∧
        t.data.regs mBase = 100 ∧
        t.data.mem 42 = 777 ∧
        t.transcript =
          [ ⟨.insert k0 100, ()⟩
          , ⟨.insert k1 200, ()⟩
          , ⟨.insert k2 300, ()⟩
          , ⟨.insert k3 400, ()⟩
          , ⟨.insert k4 500, ()⟩
          , ⟨.insert k0 (2 ^ 64 - 1), ()⟩
          , ⟨.query k0, some (2 ^ 64 - 1)⟩
          , ⟨.query k4, some 500⟩
          , ⟨.query k9, none⟩
          , ⟨.delete k4, ()⟩
          , ⟨.delete k3, ()⟩
          , ⟨.delete k2, ()⟩
          , ⟨.delete k1, ()⟩
          , ⟨.delete k0, ()⟩
          , ⟨.query k0, none⟩ ]) ∧
      (initSteps : ℝ≥0∞) + T_ops ≤
        (initSteps : ℝ≥0∞) + ((15 * resizableCharge : ℕ) : ℝ≥0∞) := by
  intro C
  obtain ⟨ν₀, ν_final, T_ops, he_init, _, hex, hfin, hcost⟩ :=
    seq_expected_amortized (U := 64) (V := 2 ^ 64) (w := 64) (base := 100)
      lifecycleOps (by decide) (by decide) (by decide) (by decide) le_rfl
      testInitState_bounded rfl (by decide) validHistory_lifecycleOps peakFitsHistory_lifecycleOps
  have hcard_fin :
      (Dictionary.dom ((Dynamic.spec 64 (2 ^ 64) 64).run (Dictionary.empty 64) lifecycleOps).1).card
        = 0 := by decide
  have hrun_out :
      ((Dynamic.spec 64 (2 ^ 64) 64).run (Dictionary.empty 64) lifecycleOps).2 =
        [ ⟨.insert k0 100, ()⟩, ⟨.insert k1 200, ()⟩, ⟨.insert k2 300, ()⟩,
          ⟨.insert k3 400, ()⟩, ⟨.insert k4 500, ()⟩, ⟨.insert k0 (2 ^ 64 - 1), ()⟩,
          ⟨.query k0, some (2 ^ 64 - 1)⟩, ⟨.query k4, some 500⟩, ⟨.query k9, none⟩,
          ⟨.delete k4, ()⟩, ⟨.delete k3, ()⟩, ⟨.delete k2, ()⟩,
          ⟨.delete k1, ()⟩, ⟨.delete k0, ()⟩, ⟨.query k0, none⟩ ] := rfl
  refine ⟨ν₀, ν_final, T_ops, he_init, hex, fun t ht => ?_, hcost⟩
  obtain ⟨hbdd, ⟨_, hhi, hreg⟩, hmem, htr⟩ := hfin t ht
  rw [hcard_fin] at hhi
  rw [hrun_out] at htr
  exact ⟨hbdd, hhi, hreg, hmem 42 (by decide), htr⟩

/-- Standard-basis (`Basis.standard`) and compiled flat-`RProgram` (`seq_toExecRProgramDist`)
instantiation check on `lifecycleOps`. -/
theorem test_standard_and_program_lifecycle :
    let C_std := obliviousImplStandard (U := 64) (V := 2 ^ 64) (w := 64) (base := 100)
      (by decide) (by decide) (by decide) (by decide) le_rfl
    (∃ (ν₀ : PMF (LatentRState (LatentSeed 64) rResize))
       (ν_final : PMF (SeqROutcome (LatentSeed 64) (Dynamic.Op.Result (U := 64)) rResize))
       (T_ops : ℝ≥0∞),
       C_std.Steps lifecycleOps (ν₀.map SeqROutcome.ofLatentRState) ν_final T_ops) ∧
    (∃ (ν₀ : PMF (LatentRState (LatentSeed 64) rResize))
       (ν_final : PMF (SeqROutcome (LatentSeed 64) (Dynamic.Op.Result (U := 64)) rResize))
       (T_prog : ℝ≥0∞),
       C_std.ProgramSteps ((subroutineCodeStandard 64 (2 ^ 64) 64).opProg mOutTag) mOutTag
         lifecycleOps (ν₀.map SeqROutcome.ofLatentRState) ν_final T_prog) := by
  intro C_std
  have hv_seq :
      ((Dynamic.spec 64 (2 ^ 64) 64).toObliviousSequenceSpec (Dictionary.empty 64)).ValidOpSeq
        lifecycleOps :=
    ((Dynamic.spec 64 (2 ^ 64) 64).validOpSeq_iff_validHistory (Dictionary.empty 64)
      lifecycleOps).mpr validHistory_lifecycleOps
  have hob_fit : ObliviousPeakFits 64 100 C_std.peakSpaceBound [] lifecycleOps :=
    obliviousPeakFits_of_succinctWords (by decide) (by decide) (by decide) (by decide)
      validHistory_lifecycleOps peakFitsHistory_lifecycleOps
  have hfit₀ : Fits 64 (100 + C_std.spaceBound []) := by
    change Fits 64 (100 + epochSpaceBound 64 (2 ^ 64) 64 [])
    rw [epochSpaceBound_nil]; decide
  obtain ⟨ν₀, ν_final, T_ops, _, _, hex, _, _⟩ :=
    seq_expected_amortized_standard (U := 64) (V := 2 ^ 64) (w := 64) (base := 100)
      lifecycleOps (by decide) (by decide) (by decide) (by decide) le_rfl
      testInitState_bounded rfl (by decide) validHistory_lifecycleOps peakFitsHistory_lifecycleOps
  obtain ⟨ν₀', ν_final', T_prog, _, _, hprog, _, _, _⟩ :=
    C_std.seq_toExecRProgramDist mOutTag lifecycleOps testInitState_bounded rfl
      (fun j => Fin.elim0 j) hfit₀ hv_seq hob_fit
  exact ⟨⟨ν₀, ν_final, T_ops, hex⟩, ⟨ν₀', ν_final', T_prog, hprog⟩⟩

/-! ### Test 3: `.halt`-rejection soundness check (`not_execProgramSteps_halt`) -/

/-- Soundness check: a 1-instruction `[.halt mOutTag]` no-op stub cannot satisfy `ExecProgramSteps`
for `[.query k0]` on any distribution `ν_final` satisfying `Contract` after `[.insert k0 42]`,
because `prepare` sets `mOutTag := 0` (`resizableDecode` decodes `none`) whereas `Contract`
requires `some 42`. -/
theorem test_halt_stub_rejected
    (ν : PMF (SeqROutcome (LatentSeed 64) (Dynamic.Op.Result (U := 64)) rResize))
    (ν_final : PMF (SeqROutcome (LatentSeed 64) (Dynamic.Op.Result (U := 64)) rResize))
    (T_prog : ℝ≥0∞)
    (ht_tr : ∀ t ∈ ν.support, t.transcript = [⟨.insert k0 42, ()⟩])
    (hcontract :
      ((Dynamic.spec 64 (2 ^ 64) 64).toObliviousSequenceSpec (Dictionary.empty 64)).Contract
        [.insert k0 42, .query k0] (ν_final.map SeqROutcome.transcript)) :
    ¬ExecProgramSteps (subroutineCode 64 (2 ^ 64) 64)
      ((Dynamic.spec 64 (2 ^ 64) 64).toObliviousSequenceSpec (Dictionary.empty 64))
      (LatentSeed 64) 64 100 (epochSpaceBound 64 (2 ^ 64) 64) (epochPeakSpaceBound 64 (2 ^ 64) 64)
      resizableEncode resizableDecode [.halt mOutTag] mOutTag
      [.insert k0 42] [.query k0] ν ν_final T_prog := by
  obtain ⟨t, ht⟩ := ν.support_nonempty
  apply not_execProgramSteps_halt (out := mOutTag) ht
  intro a hdec _ _ u hu hpref
  have ha_none : a = none := by
    have htag_in : (subroutineCode 64 (2 ^ 64) 64).input mOutTag = true := by
      simp [subroutineCode, resizableInput, mOutTag]
    have htag0 : ((subroutineCode 64 (2 ^ 64) 64).prepare resizableEncode (.query k0) t.data).regs
        mOutTag = 0 := by
      dsimp only [Cslib.DataStructure.WordRAM.Resizable.SubroutineCode.prepare,
        Cslib.DataStructure.WordRAM.Resizable.SubroutineCode.prepareRegs]
      rw [htag_in]
      simp [resizableEncode,
        show mOutTag ≠ mTag from mReg_ne (by decide),
        show mOutTag ≠ mArgU from mReg_ne (by decide)]
    have hdec' : resizableDecode (.query k0)
        ((subroutineCode 64 (2 ^ 64) 64).prepare resizableEncode (.query k0) t.data).regs =
        some none := by
      unfold resizableDecode decode
      change (if ((subroutineCode 64 (2 ^ 64) 64).prepare resizableEncode (.query k0) t.data).regs
          (epochEmb rOutTag) = 0 then some none else _) = some none
      rw [epochEmb_rOutTag, htag0]; rfl
    exact Option.some.inj (hdec.symm.trans hdec')
  have hv_hist : (Dynamic.spec 64 (2 ^ 64) 64).ValidHistory (Dictionary.empty 64)
      [.insert k0 42, .query k0] :=
    validHistory_of_allInsertsLt (Dictionary.empty 64) [.insert k0 42, .query k0] (by decide)
  rw [(Dynamic.spec 64 (2 ^ 64) 64).toObliviousSequenceSpec_contract_iff_of_hasStepFn
    (Dictionary.empty 64) hv_hist] at hcontract
  have hu_tr : u.transcript = [⟨.insert k0 42, ()⟩, ⟨.query k0, some 42⟩] :=
    hcontract u.transcript ((PMF.mem_support_map_iff _ _ _).mpr ⟨u, hu, rfl⟩)
  rw [ht_tr t ht, ha_none, hu_tr] at hpref
  obtain ⟨_, heq⟩ := hpref
  injection heq with _ htail
  injection htail with hhd _
  cases hhd

end CslibFrontierTests.DataStructure.ResizableSuccinct
