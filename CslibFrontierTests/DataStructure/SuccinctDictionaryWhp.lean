/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhp
import CslibFrontier.Computability.WordRAM.Width

/-!
# High-Probability Fixed-Capacity Succinct Dynamic Dictionary Tests

Ordinary-import `module` client exercising `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp`
across both parameter regimes (`< whpThreshold c` and `≥ whpThreshold c`):

1. **Width independence (`¬ReadsWidth`)**:
   - `not_readsWidth_subroutineCode` on `initFresh`, `initClear`, and `code`, lifted to
     `Basis.standard` (`.toStandard`) and to flat `Program`s (`Code.not_readsWidth_program`).
2. **Small-regime (`< whpThreshold c`) parameter, space, and end-to-end lifecycle tests**:
   - Concrete evaluation of `whpSpace c (2 ^ 32) (2 ^ 16) 64 16 = 51`, `Fits`, `impl`,
     `implStandard`, and `initTime_impl_le` at `(c, U, V, w, n_max, base) = (1, 2 ^ 32, 2 ^ 16, 64,
     16, 100)`.
   - Sequential 7-operation lifecycle (`insert → insert → overwrite → query → delete → query →
     query`) exercising `seq_whp` (including exact transcript `[(), (), (), some 300, (), none,
     some 200]` and `Modifies` preservation of caller memory outside `[100, 151)`),
     `poly_seq_whp`, and `reachable_step_whp` (clocked `evalRand` at horizon
     `worstCaseTimeWhp 1 + 1`).
3. **Large-regime (`≥ whpThreshold 1`) parameter, `Fits`, and end-to-end lifecycle tests**:
   - Non-vacuous instantiation at `(c, U, V, w, n_max, base) = (1, whpThreshold 1, 2 ^ 16,
     3 * bMinWhp 1 + 64, whpThreshold 1, 100)` exercising the two-stage double-tabulation + SWAR
     B+-tree + `BufTrie` regime (`impl`, `implStandard`, `initTime_impl_le`, `seq_whp`, and
     `reachable_step_whp`) on the 7-operation lifecycle.
4. **Negative `[.halt outReg]` clocked `evalRand` rejection**:
   - Proves `evalRand_halt_succ`, `not_halt_program_reachable_step_whp`, and
     `subroutineCode_program_ne_halt`: a flat `[.halt outReg]` program cannot satisfy the clocked
     `evalRand` correctness postcondition across empty-dictionary `.query` (`none`) and post-insert
     `.query` (`some 100`) from states agreeing outside `input`, and the compiled operation program
     is distinct from `[.halt outReg]`.
-/

@[expose] public section

namespace CslibFrontierTests.DataStructure.SuccinctDictionaryWhp

open Cslib Cslib.WordRAM Cslib.Probability
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open scoped ENNReal

/-! ## 1. Width Independence (`¬ReadsWidth`) -/

theorem not_readsWidth_programs (c U V w n_max : ℕ) :
    ¬((subroutineCode c U V w n_max).initFresh.program outReg).ReadsWidth ∧
    ¬((subroutineCode c U V w n_max).initClear.program outReg).ReadsWidth ∧
    ¬((subroutineCode c U V w n_max).code.program outReg).ReadsWidth ∧
    ¬(subroutineCode c U V w n_max).toStandard.initFresh.ReadsWidth ∧
    ¬(subroutineCode c U V w n_max).toStandard.code.ReadsWidth := by
  obtain ⟨hf, hc, hop⟩ := not_readsWidth_subroutineCode c U V w n_max
  refine ⟨Code.not_readsWidth_program hf outReg,
    Code.not_readsWidth_program hc outReg,
    Code.not_readsWidth_program hop outReg, ?_, ?_⟩
  · intro hr
    apply hf
    simp only [SubroutineCode.toStandard, SubroutineCode.initFresh, SubroutineCode.mapSimulates,
      Code.ReadsWidth] at hr ⊢
    rcases hr with hr1 | hr2
    · exact Or.inl (Code.readsWidth_of_mapSimulates _ hr1)
    · exact Or.inr (Code.readsWidth_of_mapSimulates _ hr2)
  · exact fun hr => hop (Code.readsWidth_of_mapSimulates _ hr)

/-! ## 2. Shared 7-Operation Dictionary Lifecycle (`insert → overwrite → query → delete → query`) -/

/-- Test key `3 : Fin U` for `16 ≤ U`. -/
abbrev k3Of (U : ℕ) (hU16 : 16 ≤ U) : Fin U := ⟨3, by omega⟩

/-- Test key `7 : Fin U` for `16 ≤ U`. -/
abbrev k7Of (U : ℕ) (hU16 : 16 ≤ U) : Fin U := ⟨7, by omega⟩

/-- Generic 7-operation lifecycle on `Fin U` (`16 ≤ U`):
insert `3 ↦ 100`, insert `7 ↦ 200`, overwrite `3 ↦ 300`, query `3` (`some 300`), delete `3`,
query `3` (`none`), and query `7` (`some 200`). -/
def sampleOpsOf (U : ℕ) (hU16 : 16 ≤ U) : List (Dynamic.Op U) :=
  [ .insert (k3Of U hU16) 100
  , .insert (k7Of U hU16) 200
  , .insert (k3Of U hU16) 300
  , .query (k3Of U hU16)
  , .delete (k3Of U hU16)
  , .query (k3Of U hU16)
  , .query (k7Of U hU16) ]

/-- Expected 7-element transcript of `sampleOpsOf U hU16`. -/
def sampleTranscriptOf (U : ℕ) (hU16 : 16 ≤ U) :
    List (Sigma (Dynamic.spec U 1 1).Result) :=
  [ ⟨.insert (k3Of U hU16) 100, ()⟩
  , ⟨.insert (k7Of U hU16) 200, ()⟩
  , ⟨.insert (k3Of U hU16) 300, ()⟩
  , ⟨.query (k3Of U hU16), some 300⟩
  , ⟨.delete (k3Of U hU16), ()⟩
  , ⟨.query (k3Of U hU16), none⟩
  , ⟨.query (k7Of U hU16), some 200⟩ ]

theorem length_sampleOpsOf (U : ℕ) (hU16 : 16 ≤ U) :
    (sampleOpsOf U hU16).length = 7 :=
  rfl

theorem validHistory_sampleOpsOf {U V n_max : ℕ} (hU16 : 16 ≤ U) (hV : 301 ≤ V)
    (hn : 2 < n_max) :
    (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) (sampleOpsOf U hU16) := by
  have hne : k3Of U hU16 ≠ k7Of U hU16 := by
    intro h; have := congrArg Fin.val h; dsimp only [k3Of, k7Of] at this; omega
  have hcard0 : (Dictionary.dom (Dictionary.empty U)).card < n_max := by simp; omega
  have hcard1 :
      (Dictionary.dom (Function.update (Dictionary.empty U) (k3Of U hU16) (some 100))).card <
        n_max := by
    have hle := Dictionary.card_dom_insert_le (Dictionary.empty U) (k3Of U hU16) 100
    simp only [Dictionary.dom_empty, Finset.card_empty, zero_add] at hle
    omega
  have hisSome2 :
      (Function.update
        (Function.update (Dictionary.empty U) (k3Of U hU16) (some 100))
        (k7Of U hU16) (some 200) (k3Of U hU16)).isSome := by
    rw [Function.update_of_ne hne, Function.update_self]
    rfl
  dsimp only [sampleOpsOf, Dynamic.spec, StateTransitionSpec.ValidHistory,
    StateTransitionSpec.ofFn, Dynamic.valid, Dynamic.step]
  exact ⟨⟨Or.inl hcard0, by omega⟩,
    ⟨Or.inl hcard1, by omega⟩,
    ⟨Or.inr hisSome2, by omega⟩,
    trivial, trivial, trivial, trivial, trivial⟩

theorem run_sampleOpsOf {U V n_max : ℕ} (hU16 : 16 ≤ U) :
    ((Dynamic.spec U V n_max).run (Dictionary.empty U) (sampleOpsOf U hU16)).1 (k3Of U hU16) =
      none ∧
    ((Dynamic.spec U V n_max).run (Dictionary.empty U) (sampleOpsOf U hU16)).1 (k7Of U hU16) =
      some 200 ∧
    ((Dynamic.spec U V n_max).run (Dictionary.empty U) (sampleOpsOf U hU16)).2 =
      [ ⟨.insert (k3Of U hU16) 100, ()⟩
      , ⟨.insert (k7Of U hU16) 200, ()⟩
      , ⟨.insert (k3Of U hU16) 300, ()⟩
      , ⟨.query (k3Of U hU16), some 300⟩
      , ⟨.delete (k3Of U hU16), ()⟩
      , ⟨.query (k3Of U hU16), none⟩
      , ⟨.query (k7Of U hU16), some 200⟩ ] := by
  have hne37 : k3Of U hU16 ≠ k7Of U hU16 := by
    intro h; have := congrArg Fin.val h; dsimp only [k3Of, k7Of] at this; omega
  have hne73 : k7Of U hU16 ≠ k3Of U hU16 := hne37.symm
  dsimp only [sampleOpsOf, Dynamic.spec, StateTransitionSpec.run, StateTransitionSpec.ofFn,
    Dynamic.step, Dictionary.empty]
  refine ⟨Function.update_self _ _ _, ?_, ?_⟩
  · rw [Function.update_of_ne hne73, Function.update_of_ne hne73, Function.update_self]
  · simp only [Function.update_self, Function.update_of_ne hne73]

/-- Initial machine data with `frontierReg = 100` and caller sentinel `mem 42 = 999` outside
`[100, 100 + whpSpace ...)`. -/
noncomputable def sampleInitData : Data rWhp :=
  ⟨Function.update (fun _ => 0) frontierReg 100, Function.update (fun _ => 0) 42 999⟩

theorem mem_sampleInitData_42 : sampleInitData.mem 42 = 999 := by
  unfold sampleInitData
  simp

theorem regs_sampleInitData_frontier : sampleInitData.regs frontierReg = 100 := by
  unfold sampleInitData
  simp

theorem bounded_sampleInitData {w : ℕ} (hw10 : 10 ≤ w) : sampleInitData.Bounded w := by
  have h1000 : 1000 ≤ 2 ^ w :=
    (by decide : 1000 ≤ 2 ^ 10).trans (Nat.pow_le_pow_right (by decide) hw10)
  refine ⟨fun i => ?_, fun a => ?_⟩
  · dsimp only [sampleInitData, Fits]
    by_cases hi : i = frontierReg
    · subst hi; rw [Function.update_self]; omega
    · rw [Function.update_of_ne hi]; omega
  · dsimp only [sampleInitData, Fits]
    by_cases ha : a = 42
    · subst ha; rw [Function.update_self]; omega
    · rw [Function.update_of_ne ha]; omega

theorem zero_footprint_sampleInitData (sp : ℕ) :
    ∀ a ∈ (Block.mk 100 sp).footprint, sampleInitData.mem a = 0 := by
  intro a ha
  simp only [Block.mem_footprint, Block.Owns] at ha
  have hne : a ≠ 42 := by omega
  dsimp only [sampleInitData]
  exact Function.update_of_ne hne 999 (fun _ => 0)

/-! ## 3. Small-Regime (`< whpThreshold c`) Concrete Space and Lifecycle Execution -/

theorem sixteen_lt_whpThreshold (c : ℕ) : 16 < whpThreshold c := by
  rw [whpThreshold_eq]
  have hbm := le_bMinWhp c
  calc 16 < 2 ^ 5 := by decide
    _ ≤ 2 ^ bMinWhp c := Nat.pow_le_pow_right (by decide) (by omega)

theorem small_whpSpace_eq (c : ℕ) :
    whpSpace c (2 ^ 32) (2 ^ 16) 64 16 = 51 := by
  unfold whpSpace
  rw [ite_eq_left (sixteen_lt_whpThreshold c)]
  decide

theorem hfit_small_whp (c : ℕ) :
    Fits 64 (100 + whpSpace c (2 ^ 32) (2 ^ 16) 64 16) := by
  dsimp only [Fits]
  rw [small_whpSpace_eq c]
  decide

/-- Concrete `Basis.exact` certificate in the small regime
`(c, U, V, w, n_max, base) = (1, 2 ^ 32, 2 ^ 16, 64, 16, 100)`. -/
noncomputable abbrev smallWhpImpl :
    HighProbStateTransitionImpl (subroutineCode 1 (2 ^ 32) (2 ^ 16) 64 16)
      (Dynamic.spec (2 ^ 32) (2 ^ 16) 16) 64 100 Fin.elim0 (Dictionary.empty (2 ^ 32)) :=
  impl (by decide) (by decide) (by decide) (by decide) (by decide) (hfit_small_whp 1)

/-- Concrete `Basis.standard` certificate in the small regime. -/
noncomputable abbrev smallWhpImplStandard :
    HighProbStateTransitionImpl (subroutineCode 1 (2 ^ 32) (2 ^ 16) 64 16).toStandard
      (Dynamic.spec (2 ^ 32) (2 ^ 16) 16) 64 100 Fin.elim0 (Dictionary.empty (2 ^ 32)) :=
  implStandard (by decide) (by decide) (by decide) (by decide) (by decide) (hfit_small_whp 1)

example :
    smallWhpImpl.space = 51 ∧
    smallWhpImpl.initTime = 4 ∧
    smallWhpImpl.initTime ≤ initTimeLinearFactor * 16 + initTimeLinearConst := by
  obtain ⟨heq, hle⟩ :=
    initTime_impl_le (by decide) (by decide) (by decide) (by decide) (by decide) (hfit_small_whp 1)
  refine ⟨small_whpSpace_eq 1, ?_, heq.trans_le hle⟩
  rw [heq]
  unfold initSetupSteps
  rw [ite_eq_left (sixteen_lt_whpThreshold 1)]

/-- Concrete `Basis.exact` certificate in the small regime (`c = 2`, for `poly_seq_whp` at
`c = 1, c₀ = 1`). -/
noncomputable abbrev smallWhpImpl2 :
    HighProbStateTransitionImpl (subroutineCode 2 (2 ^ 32) (2 ^ 16) 64 16)
      (Dynamic.spec (2 ^ 32) (2 ^ 16) 16) 64 100 Fin.elim0 (Dictionary.empty (2 ^ 32)) :=
  impl (by decide) (by decide) (by decide) (by decide) (by decide) (hfit_small_whp 2)

/-- Whole-sequence `seq_whp` check on the 7-operation lifecycle in the small regime, verifying
`evalRand` initialization coupling, `ExecWhpSteps`, caller sentinel preservation (`mem 42 = 999`)
via `Modifies` on both `ν₀` and `τ_final`, and the exact 7-step specification transcript. -/
theorem small_regime_seq_whp :
    let h16 : 16 ≤ 2 ^ 32 := by decide
    let ops := sampleOpsOf (2 ^ 32) h16
    ∃ (ν₀ : PMF (SeedWhp 1 (2 ^ 32) 16 × Data rWhp))
      (τ_final : PMF (WhpSeqOutcome (SeedWhp 1 (2 ^ 32) 16)
        (Dynamic.spec (2 ^ 32) (2 ^ 16) 16) rWhp)),
      RandHaltsWithin 64 ((subroutineCode 1 (2 ^ 32) (2 ^ 16) 64 16).initFresh.program outReg)
        ⟨0, sampleInitData⟩ (smallWhpImpl.initTime + 1) ∧
      evalRand 64 ((subroutineCode 1 (2 ^ 32) (2 ^ 16) 64 16).initFresh.program outReg)
        (smallWhpImpl.initTime + 1) ⟨0, sampleInitData⟩ =
        ν₀.map (fun p => RandCfg.halted (p.2.regs outReg) p.2) ∧
      smallWhpImpl.ExecWhpSteps outReg ops
        (ν₀.map fun p => WhpSeqOutcome.ofCoupled ⟨p.1, Dictionary.empty (2 ^ 32), p.2⟩) τ_final ∧
      (∀ p ∈ ν₀.support, p.2.mem 42 = 999) ∧
      (∀ tr ∈ τ_final.support,
        tr.current.data.mem 42 = 999 ∧ tr.transcript = sampleTranscriptOf (2 ^ 32) h16) ∧
      1 - (7 : ℝ≥0∞) * (16 : ℝ≥0∞)⁻¹ ≤
        τ_final.toOuterMeasure
          {tr | tr.maxSteps ≤ worstCaseTimeWhp 1 ∧
            tr.transcript = sampleTranscriptOf (2 ^ 32) h16} := by
  intro h16 ops
  have hv := validHistory_sampleOpsOf (U := 2 ^ 32) (V := 2 ^ 16) (n_max := 16)
    h16 (by decide) (by decide)
  obtain ⟨ν₀, τ_final, hhalts, heval₀, hsupp₀, hex, hsupp_fin, _, hprob⟩ :=
    seq_whp (c := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
      (hfit_small_whp 1) ops
      (bounded_sampleInitData (by decide)) regs_sampleInitData_frontier
      (zero_footprint_sampleInitData _) hv
  have h42 : 42 ∉ (Block.mk 100 (whpSpace 1 (2 ^ 32) (2 ^ 16) 64 16)).footprint := by
    simp [Block.mem_footprint, Block.Owns]
  obtain ⟨_, _, htr_eq⟩ := run_sampleOpsOf (U := 2 ^ 32) (V := 2 ^ 16) (n_max := 16) h16
  have htr' : ((Dynamic.spec (2 ^ 32) (2 ^ 16) 16).run (Dictionary.empty (2 ^ 32)) ops).2 =
      sampleTranscriptOf (2 ^ 32) h16 := htr_eq
  refine ⟨ν₀, τ_final, hhalts, heval₀, hex, fun p hp => ?_, fun tr htr => ?_, ?_⟩
  · exact ((hsupp₀ p hp).2.2.2 42 h42).trans mem_sampleInitData_42
  · obtain ⟨_, htrans, _, hmod_fin⟩ := hsupp_fin tr htr
    exact ⟨(hmod_fin 42 h42).trans mem_sampleInitData_42, htrans.trans htr'⟩
  · have hmax16 : (max ((16 : ℕ) : ℝ≥0∞) 1)⁻¹ ^ 1 = (16 : ℝ≥0∞)⁻¹ := by
      rw [max_eq_left (by norm_num), pow_one, Nat.cast_ofNat]
    have hlen : (ops.length : ℝ≥0∞) = 7 := by dsimp only [ops]; rw [length_sampleOpsOf]; norm_num
    rw [htr', hlen, hmax16] at hprob
    exact hprob

/-- Polynomial-horizon `poly_seq_whp` check (`c = 1, c₀ = 1`, `7 ≤ 16 ^ 1`) in the small regime,
retaining `evalRand` initialization coupling, `ExecWhpSteps`, and `Modifies` sentinel preservation.
-/
theorem small_regime_poly_seq_whp :
    let h16 : 16 ≤ 2 ^ 32 := by decide
    let ops := sampleOpsOf (2 ^ 32) h16
    ∃ (ν₀ : PMF (SeedWhp 2 (2 ^ 32) 16 × Data rWhp))
      (τ_final : PMF (WhpSeqOutcome (SeedWhp 2 (2 ^ 32) 16)
        (Dynamic.spec (2 ^ 32) (2 ^ 16) 16) rWhp)),
      RandHaltsWithin 64 ((subroutineCode 2 (2 ^ 32) (2 ^ 16) 64 16).initFresh.program outReg)
        ⟨0, sampleInitData⟩ (smallWhpImpl2.initTime + 1) ∧
      evalRand 64 ((subroutineCode 2 (2 ^ 32) (2 ^ 16) 64 16).initFresh.program outReg)
        (smallWhpImpl2.initTime + 1) ⟨0, sampleInitData⟩ =
        ν₀.map (fun p => RandCfg.halted (p.2.regs outReg) p.2) ∧
      smallWhpImpl2.ExecWhpSteps outReg ops
        (ν₀.map fun p => WhpSeqOutcome.ofCoupled ⟨p.1, Dictionary.empty (2 ^ 32), p.2⟩) τ_final ∧
      (∀ tr ∈ τ_final.support,
        tr.current.data.mem 42 = 999 ∧ tr.transcript = sampleTranscriptOf (2 ^ 32) h16) ∧
      1 - (16 : ℝ≥0∞)⁻¹ ≤
        τ_final.toOuterMeasure
          {tr | tr.maxSteps ≤ worstCaseTimeWhp 2 ∧
            tr.transcript = sampleTranscriptOf (2 ^ 32) h16} := by
  intro h16 ops
  have hv := validHistory_sampleOpsOf (U := 2 ^ 32) (V := 2 ^ 16) (n_max := 16)
    h16 (by decide) (by decide)
  obtain ⟨ν₀, τ_final, hhalts, heval₀, _, hex, hsupp_fin, _, hprob⟩ :=
    poly_seq_whp (c := 1) (c₀ := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
      (hfit_small_whp 2) ops (by decide)
      (bounded_sampleInitData (by decide)) regs_sampleInitData_frontier
      (zero_footprint_sampleInitData _) hv
  have h42 : 42 ∉ (Block.mk 100 (whpSpace 2 (2 ^ 32) (2 ^ 16) 64 16)).footprint := by
    simp [Block.mem_footprint, Block.Owns]
  obtain ⟨_, _, htr_eq⟩ := run_sampleOpsOf (U := 2 ^ 32) (V := 2 ^ 16) (n_max := 16) h16
  have htr' : ((Dynamic.spec (2 ^ 32) (2 ^ 16) 16).run (Dictionary.empty (2 ^ 32)) ops).2 =
      sampleTranscriptOf (2 ^ 32) h16 := htr_eq
  have hmax16 : (max ((16 : ℕ) : ℝ≥0∞) 1)⁻¹ ^ 1 = (16 : ℝ≥0∞)⁻¹ := by
    rw [max_eq_left (by norm_num), pow_one, Nat.cast_ofNat]
  rw [htr', hmax16] at hprob
  refine ⟨ν₀, τ_final, hhalts, heval₀, hex, fun tr htr => ?_, hprob⟩
  obtain ⟨_, htrans, _, hmod_fin⟩ := hsupp_fin tr htr
  exact ⟨(hmod_fin 42 h42).trans mem_sampleInitData_42, htrans.trans htr'⟩

/-- Per-operation `reachable_step_whp` check after the 7-operation prefix in the small regime:
starting from `sampleInitData` via `initFresh` (`evalRand`) and `ExecWhpSteps`, running `.query k7`
halts in clocked `evalRand` within `worstCaseTimeWhp 1 + 1` instructions, decoding `some (some 200)`
and preserving caller memory relative to both `p.2.mem` and `sampleInitData.mem` (`Modifies`), with
probability `≥ 1 - (16 : ℝ≥0∞)⁻¹`. -/
theorem small_regime_reachable_step_whp :
    let h16 : 16 ≤ 2 ^ 32 := by decide
    let ops := sampleOpsOf (2 ^ 32) h16
    let k7 := k7Of (2 ^ 32) h16
    ∃ (ν₀ : PMF (SeedWhp 1 (2 ^ 32) 16 × Data rWhp))
      (τ_pref : PMF (WhpSeqOutcome (SeedWhp 1 (2 ^ 32) 16)
        (Dynamic.spec (2 ^ 32) (2 ^ 16) 16) rWhp)),
      RandHaltsWithin 64 ((subroutineCode 1 (2 ^ 32) (2 ^ 16) 64 16).initFresh.program outReg)
        ⟨0, sampleInitData⟩ (smallWhpImpl.initTime + 1) ∧
      evalRand 64 ((subroutineCode 1 (2 ^ 32) (2 ^ 16) 64 16).initFresh.program outReg)
        (smallWhpImpl.initTime + 1) ⟨0, sampleInitData⟩ =
        ν₀.map (fun p => RandCfg.halted (p.2.regs outReg) p.2) ∧
      smallWhpImpl.ExecWhpSteps outReg ops
        (ν₀.map fun p => WhpSeqOutcome.ofCoupled ⟨p.1, Dictionary.empty (2 ^ 32), p.2⟩) τ_pref ∧
      1 - (16 : ℝ≥0∞)⁻¹ ≤
        ((τ_pref.map fun tr => (tr.current.seed, tr.current.data)).bind fun p =>
          evalRand 64 ((subroutineCode 1 (2 ^ 32) (2 ^ 16) 64 16).code.program outReg)
            (worstCaseTimeWhp 1 + 1) ⟨0, smallWhpImpl.prepare (.query k7) p.2⟩).toOuterMeasure
          {cfg | ∃ (p q : SeedWhp 1 (2 ^ 32) 16 × Data rWhp),
            p ∈ (τ_pref.map fun tr => (tr.current.seed, tr.current.data)).support ∧
            cfg = .halted (q.2.regs outReg) q.2 ∧
            WordRAM.SuccinctWhp.decode (.query k7) q.2.regs = some (some 200) ∧
            Modifies (Block.mk 100 51).footprint p.2.mem q.2.mem ∧
            Modifies (Block.mk 100 51).footprint sampleInitData.mem q.2.mem ∧
            q.2.mem 42 = 999} := by
  intro h16 ops k7
  have hv := validHistory_sampleOpsOf (U := 2 ^ 32) (V := 2 ^ 16) (n_max := 16)
    h16 (by decide) (by decide)
  obtain ⟨_, hk7_eq, _⟩ := run_sampleOpsOf (U := 2 ^ 32) (V := 2 ^ 16) (n_max := 16) h16
  obtain ⟨ν₀, τ_pref, hhalts, heval₀, _, hex, _, hprob⟩ :=
    reachable_step_whp (c := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
      (hfit_small_whp 1) ops (.query k7)
      (bounded_sampleInitData (by decide)) regs_sampleInitData_frontier
      (zero_footprint_sampleInitData _) hv trivial
  refine ⟨ν₀, τ_pref, hhalts, heval₀, hex, ?_⟩
  have hmax16 : (max ((16 : ℕ) : ℝ≥0∞) 1)⁻¹ ^ 1 = (16 : ℝ≥0∞)⁻¹ := by
    rw [max_eq_left (by norm_num), pow_one, Nat.cast_ofNat]
  rw [hmax16] at hprob
  have h42 : 42 ∉ (Block.mk 100 51).footprint := by simp [Block.mem_footprint, Block.Owns]
  refine hprob.trans ((_ : PMF _).toOuterMeasure.mono fun cfg hcfg => ?_)
  obtain ⟨p, q, hp, hcfg_eq, hdec, _, _, hmod_pq, hmod_x⟩ := hcfg
  have hstep_res :
      ((Dynamic.spec (2 ^ 32) (2 ^ 16) 16).stepFn
        ((Dynamic.spec (2 ^ 32) (2 ^ 16) 16).run (Dictionary.empty (2 ^ 32)) ops).1
        (.query k7)).2 = some 200 := hk7_eq
  rw [hstep_res] at hdec
  rw [small_whpSpace_eq 1] at hmod_pq hmod_x
  exact ⟨p, q, hp, hcfg_eq, hdec, hmod_pq, hmod_x, (hmod_x 42 h42).trans mem_sampleInitData_42⟩

/-! ## 4. Large-Regime (`≥ whpThreshold 1`) Space Witness and End-to-End Lifecycle Execution -/

/-- Large-regime test capacity `whpThreshold 1 = 2 ^ bMinWhp 1`. -/
abbrev nLarge : ℕ := whpThreshold 1

/-- Large-regime word width `3 * bMinWhp 1 + 64`. -/
abbrev wLarge : ℕ := 3 * bMinWhp 1 + 64

theorem hU_large_whp : Fits wLarge nLarge := by
  dsimp only [Fits, nLarge, wLarge]
  rw [whpThreshold_eq]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

theorem hV_large_whp : Fits wLarge (2 ^ 16) := by
  dsimp only [Fits, wLarge]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

theorem hfit_large_whp :
    Fits wLarge (100 + whpSpace 1 nLarge (2 ^ 16) wLarge nLarge) := by
  dsimp only [Fits]
  have hbm := le_bMinWhp 1
  have hbm_lt_N : bMinWhp 1 < nLarge := by
    dsimp only [nLarge]
    rw [whpThreshold_eq]
    exact @Nat.lt_two_pow_self (bMinWhp 1)
  have hfac_le : whpSpaceFactor 1 ≤ 2 * nLarge := by
    unfold whpSpaceFactor
    omega
  have hw_le : wLarge ≤ 4 * nLarge := by
    unfold wLarge
    omega
  have hell_le_N : Dynamic.logLogFactor nLarge ≤ nLarge := by
    have hlog := log_ge_mul_ell (le_rfl : whpThreshold 1 ≤ nLarge)
    have hlog_eq : Nat.log 2 (whpThreshold 1) = bMinWhp 1 := by
      rw [whpThreshold_eq]
      exact Nat.log_pow Nat.one_lt_two _
    dsimp only [nLarge] at hbm_lt_N hlog ⊢
    omega
  have hsp_le : whpSpace 1 nLarge (2 ^ 16) wLarge nLarge ≤
      Dynamic.succinctWords (whpSpaceFactor 1) whpSpaceConst nLarge (2 ^ 16) wLarge nLarge :=
    whpSpace_le_succinctWords le_rfl
  have hopt : Dynamic.optBits nLarge (2 ^ 16) nLarge = 16 * nLarge := by
    unfold Dynamic.optBits
    have hc1 : Nat.clog 2 (nLarge.choose nLarge) = 0 := by rw [Nat.choose_self]; decide
    have hc2 : Nat.clog 2 (2 ^ 16) = 16 := by decide
    rw [hc1, hc2, Nat.zero_add, Nat.mul_comm]
  have hN_pos : 1 ≤ nLarge := by omega
  let N3 := nLarge * nLarge * nLarge
  have hN_le_N3 : nLarge ≤ N3 := by
    dsimp only [N3]
    calc nLarge ≤ nLarge * nLarge := Nat.le_mul_of_pos_right nLarge hN_pos
      _ ≤ nLarge * nLarge * nLarge := Nat.le_mul_of_pos_right _ hN_pos
  have hN3_pos : 1 ≤ N3 := hN_pos.trans hN_le_N3
  have hdiv :
      (Dynamic.optBits nLarge (2 ^ 16) nLarge +
        whpSpaceFactor 1 * nLarge * Dynamic.logLogFactor nLarge + wLarge - 1) / wLarge ≤
      16 * nLarge + whpSpaceFactor 1 * nLarge * Dynamic.logLogFactor nLarge + wLarge := by
    rw [hopt]
    exact (Nat.div_le_self _ _).trans (by omega)
  have hterm2 : whpSpaceFactor 1 * nLarge * Dynamic.logLogFactor nLarge ≤ 2 * N3 := by
    dsimp only [N3]
    calc whpSpaceFactor 1 * nLarge * Dynamic.logLogFactor nLarge
        ≤ (2 * nLarge) * nLarge * nLarge :=
          Nat.mul_le_mul (Nat.mul_le_mul_right nLarge hfac_le) hell_le_N
      _ = 2 * (nLarge * nLarge * nLarge) := by ring
  have hsucc_lt :
      100 + Dynamic.succinctWords (whpSpaceFactor 1) whpSpaceConst nLarge (2 ^ 16) wLarge nLarge <
        512 * N3 := by
    unfold Dynamic.succinctWords whpSpaceConst
    omega
  have h512_le : 512 * N3 ≤ 2 ^ wLarge := by
    have hpow64 : 512 ≤ 2 ^ 64 := by decide
    have hpow_eq : 2 ^ 64 * N3 = 2 ^ wLarge := by
      dsimp only [N3, nLarge, wLarge]
      rw [whpThreshold_eq, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
      congr 1
      ring
    rw [← hpow_eq]
    exact Nat.mul_le_mul_right N3 hpow64
  exact lt_of_le_of_lt (Nat.add_le_add_left hsp_le 100) (lt_of_lt_of_le hsucc_lt h512_le)

/-- Concrete `Basis.exact` certificate in the large regime (`n_max = whpThreshold 1`). -/
noncomputable abbrev largeWhpImpl :
    HighProbStateTransitionImpl (subroutineCode 1 nLarge (2 ^ 16) wLarge nLarge)
      (Dynamic.spec nLarge (2 ^ 16) nLarge) wLarge 100 Fin.elim0 (Dictionary.empty nLarge) :=
  impl (by decide) (by unfold wLarge; omega) le_rfl hU_large_whp hV_large_whp hfit_large_whp

/-- Concrete `Basis.standard` certificate in the large regime (`n_max = whpThreshold 1`). -/
noncomputable abbrev largeWhpImplStandard :
    HighProbStateTransitionImpl (subroutineCode 1 nLarge (2 ^ 16) wLarge nLarge).toStandard
      (Dynamic.spec nLarge (2 ^ 16) nLarge) wLarge 100 Fin.elim0 (Dictionary.empty nLarge) :=
  implStandard (by decide) (by unfold wLarge; omega) le_rfl hU_large_whp hV_large_whp hfit_large_whp

example :
    largeWhpImpl.space = largeSpaceWhp 1 nLarge (2 ^ 16) wLarge nLarge ∧
    largeWhpImpl.initTime ≤ initTimeLinearFactor * nLarge + initTimeLinearConst := by
  obtain ⟨heq, hle⟩ :=
    initTime_impl_le (by decide) (by unfold wLarge; omega) le_rfl
      hU_large_whp hV_large_whp hfit_large_whp
  refine ⟨?_, heq.trans_le hle⟩
  change whpSpace 1 nLarge (2 ^ 16) wLarge nLarge = _
  simp [whpSpace, nLarge]

/-- End-to-end `seq_whp` and `reachable_step_whp` verification on the 7-operation lifecycle in the
large (`BitPackedDoubleTabulation` + SWAR B+-tree + `BufTrie`) regime at `n_max = whpThreshold 1`,
retaining `evalRand` initialization coupling, `ExecWhpSteps`, and `Modifies` sentinel preservation.
-/
theorem large_regime_end_to_end_whp :
    let h16 : 16 ≤ nLarge := (sixteen_lt_whpThreshold 1).le
    let ops := sampleOpsOf nLarge h16
    let k7 := k7Of nLarge h16
    (∃ (ν₀ : PMF (SeedWhp 1 nLarge nLarge × Data rWhp))
       (τ_final : PMF (WhpSeqOutcome (SeedWhp 1 nLarge nLarge)
         (Dynamic.spec nLarge (2 ^ 16) nLarge) rWhp)),
      RandHaltsWithin wLarge
        ((subroutineCode 1 nLarge (2 ^ 16) wLarge nLarge).initFresh.program outReg)
        ⟨0, sampleInitData⟩ (largeWhpImpl.initTime + 1) ∧
      evalRand wLarge
        ((subroutineCode 1 nLarge (2 ^ 16) wLarge nLarge).initFresh.program outReg)
        (largeWhpImpl.initTime + 1) ⟨0, sampleInitData⟩ =
        ν₀.map (fun p => RandCfg.halted (p.2.regs outReg) p.2) ∧
      largeWhpImpl.ExecWhpSteps outReg ops
        (ν₀.map fun p => WhpSeqOutcome.ofCoupled ⟨p.1, Dictionary.empty nLarge, p.2⟩) τ_final ∧
      (∀ p ∈ ν₀.support, p.2.mem 42 = 999) ∧
      (∀ tr ∈ τ_final.support,
        tr.current.data.mem 42 = 999 ∧ tr.transcript = sampleTranscriptOf nLarge h16) ∧
      1 - (7 : ℝ≥0∞) * (nLarge : ℝ≥0∞)⁻¹ ≤
        τ_final.toOuterMeasure
          {tr | tr.maxSteps ≤ worstCaseTimeWhp 1 ∧
            tr.transcript = sampleTranscriptOf nLarge h16}) ∧
    (∃ (ν₀ : PMF (SeedWhp 1 nLarge nLarge × Data rWhp))
       (τ_pref : PMF (WhpSeqOutcome (SeedWhp 1 nLarge nLarge)
         (Dynamic.spec nLarge (2 ^ 16) nLarge) rWhp)),
      RandHaltsWithin wLarge
        ((subroutineCode 1 nLarge (2 ^ 16) wLarge nLarge).initFresh.program outReg)
        ⟨0, sampleInitData⟩ (largeWhpImpl.initTime + 1) ∧
      evalRand wLarge
        ((subroutineCode 1 nLarge (2 ^ 16) wLarge nLarge).initFresh.program outReg)
        (largeWhpImpl.initTime + 1) ⟨0, sampleInitData⟩ =
        ν₀.map (fun p => RandCfg.halted (p.2.regs outReg) p.2) ∧
      largeWhpImpl.ExecWhpSteps outReg ops
        (ν₀.map fun p => WhpSeqOutcome.ofCoupled ⟨p.1, Dictionary.empty nLarge, p.2⟩) τ_pref ∧
      1 - (nLarge : ℝ≥0∞)⁻¹ ≤
        ((τ_pref.map fun tr => (tr.current.seed, tr.current.data)).bind fun p =>
          evalRand wLarge ((subroutineCode 1 nLarge (2 ^ 16) wLarge nLarge).code.program outReg)
            (worstCaseTimeWhp 1 + 1) ⟨0, largeWhpImpl.prepare (.query k7) p.2⟩).toOuterMeasure
          {cfg | ∃ (p q : SeedWhp 1 nLarge nLarge × Data rWhp),
            p ∈ (τ_pref.map fun tr => (tr.current.seed, tr.current.data)).support ∧
            cfg = .halted (q.2.regs outReg) q.2 ∧
            WordRAM.SuccinctWhp.decode (.query k7) q.2.regs = some (some 200) ∧
            Modifies (Block.mk 100 (whpSpace 1 nLarge (2 ^ 16) wLarge nLarge)).footprint
              p.2.mem q.2.mem ∧
            Modifies (Block.mk 100 (whpSpace 1 nLarge (2 ^ 16) wLarge nLarge)).footprint
              sampleInitData.mem q.2.mem ∧
            q.2.mem 42 = 999}) := by
  intro h16 ops k7
  have hw_pos : 0 < wLarge := by unfold wLarge; omega
  have hw10 : 10 ≤ wLarge := by unfold wLarge; omega
  have hv := validHistory_sampleOpsOf (U := nLarge) (V := 2 ^ 16) (n_max := nLarge)
    h16 (by decide) (by omega)
  obtain ⟨_, hk7_eq, htr_eq⟩ := run_sampleOpsOf (U := nLarge) (V := 2 ^ 16) (n_max := nLarge) h16
  have htr' : ((Dynamic.spec nLarge (2 ^ 16) nLarge).run (Dictionary.empty nLarge) ops).2 =
      sampleTranscriptOf nLarge h16 := htr_eq
  have hmaxN : (max (nLarge : ℝ≥0∞) 1)⁻¹ ^ 1 = (nLarge : ℝ≥0∞)⁻¹ := by
    have h1 : (1 : ℝ≥0∞) ≤ (nLarge : ℝ≥0∞) := by norm_cast; omega
    rw [max_eq_left h1, pow_one]
  have h42 : 42 ∉ (Block.mk 100 (whpSpace 1 nLarge (2 ^ 16) wLarge nLarge)).footprint := by
    simp [Block.mem_footprint, Block.Owns]
  refine ⟨?_, ?_⟩
  · obtain ⟨ν₀, τ_final, hhalts, heval₀, hsupp₀, hex, hsupp_fin, _, hprob⟩ :=
      seq_whp (c := 1) (by decide) hw_pos le_rfl hU_large_whp hV_large_whp hfit_large_whp ops
        (bounded_sampleInitData hw10) regs_sampleInitData_frontier
        (zero_footprint_sampleInitData _) hv
    refine ⟨ν₀, τ_final, hhalts, heval₀, hex, fun p hp => ?_, fun tr htr => ?_, ?_⟩
    · exact ((hsupp₀ p hp).2.2.2 42 h42).trans mem_sampleInitData_42
    · obtain ⟨_, htrans, _, hmod_fin⟩ := hsupp_fin tr htr
      exact ⟨(hmod_fin 42 h42).trans mem_sampleInitData_42, htrans.trans htr'⟩
    · have hlen : (ops.length : ℝ≥0∞) = 7 := by dsimp only [ops]; rw [length_sampleOpsOf]; norm_num
      rw [htr', hlen, hmaxN] at hprob
      exact hprob
  · obtain ⟨ν₀, τ_pref, hhalts, heval₀, _, hex, _, hprob⟩ :=
      reachable_step_whp (c := 1) (by decide) hw_pos le_rfl hU_large_whp hV_large_whp
        hfit_large_whp ops (.query k7)
        (bounded_sampleInitData hw10) regs_sampleInitData_frontier
        (zero_footprint_sampleInitData _) hv trivial
    refine ⟨ν₀, τ_pref, hhalts, heval₀, hex, ?_⟩
    rw [hmaxN] at hprob
    refine hprob.trans ((_ : PMF _).toOuterMeasure.mono fun cfg hcfg => ?_)
    obtain ⟨p, q, hp, hcfg_eq, hdec, _, _, hmod_pq, hmod_x⟩ := hcfg
    have hstep_res :
        ((Dynamic.spec nLarge (2 ^ 16) nLarge).stepFn
          ((Dynamic.spec nLarge (2 ^ 16) nLarge).run (Dictionary.empty nLarge) ops).1
          (.query k7)).2 = some 200 := hk7_eq
    rw [hstep_res] at hdec
    exact ⟨p, q, hp, hcfg_eq, hdec, hmod_pq, hmod_x, (hmod_x 42 h42).trans mem_sampleInitData_42⟩

/-! ## 5. Negative `[.halt outReg]` Clocked `evalRand` Rejection -/

/-- A 1-instruction flat `[.halt out]` program halts at step `1` and remains absorbed in
`.halted (d.regs out) d` at every clocked horizon `T + 1`, leaving `d` completely unchanged. -/
theorem evalRand_halt_succ {B : Basis} {r : ℕ} (w : ℕ) (out : Fin r) (d : Data r) (T : ℕ) :
    evalRand w ([.halt out] : Program B r) (T + 1) ⟨0, d⟩ =
      PMF.pure (.halted (d.regs out) d) := by
  induction T with
  | zero =>
    rw [evalRand, runRand_succ, stepRand_halt (i := out) rfl]
    simp only [pure_bind, runRand_zero, ProbComp.eval_pure]
  | succ T ih =>
    have hstep :
        evalRand w ([.halt out] : Program B r) (T + 1 + 1) ⟨0, d⟩ =
          (evalRand w ([.halt out] : Program B r) (T + 1) ⟨0, d⟩).bind
            (fun cfg => (stepRand w ([.halt out] : Program B r) cfg).eval) := by
      rw [evalRand, runRand_add w ([.halt out] : Program B r) (T + 1) 1, ProbComp.eval_bind]
      simp only [evalRand, runRand_succ, runRand_zero, bind_pure]
    rw [hstep, ih, PMF.pure_bind, stepRand_halted, ProbComp.eval_pure]

/-- **Negative `[.halt outReg]` non-vacuity check (`not_halt_program_reachable_step_whp`)**:
Running the 1-instruction `[.halt outReg]` program in clocked `evalRand` at any horizon `T₀ + 1`,
`T₁ + 1` cannot assign positive probability to halting with decoded specification outputs on both
`.query k3` from `Dictionary.empty (2 ^ 32)` (`none`) and `.query k3` after `[.insert k3 100]`
(`some 100`) starting from any machine states `d₀, d₁ : Data rWhp` whose non-input registers agree
(`∀ i, input i = false → d₁.regs i = d₀.regs i`). -/
theorem not_halt_program_reachable_step_whp (T₀ T₁ : ℕ) (d₀ d₁ : Data rWhp)
    (hregs : ∀ i, (subroutineCode 1 (2 ^ 32) (2 ^ 16) 64 16).input i = false →
      d₁.regs i = d₀.regs i) :
    let k3 : Fin (2 ^ 32) := ⟨3, by decide⟩
    let haltProg : Program .exact rWhp := [.halt outReg]
    ¬ (0 < (evalRand 64 haltProg (T₀ + 1) ⟨0, smallWhpImpl.prepare (.query k3) d₀⟩).toOuterMeasure
          {cfg | ∃ q : Data rWhp,
            cfg = .halted (q.regs outReg) q ∧
            WordRAM.SuccinctWhp.decode (.query k3) q.regs =
              some ((Dynamic.spec (2 ^ 32) (2 ^ 16) 16).stepFn
                (Dictionary.empty (2 ^ 32)) (.query k3)).2} ∧
       0 < (evalRand 64 haltProg (T₁ + 1) ⟨0, smallWhpImpl.prepare (.query k3) d₁⟩).toOuterMeasure
          {cfg | ∃ q : Data rWhp,
            cfg = .halted (q.regs outReg) q ∧
            WordRAM.SuccinctWhp.decode (.query k3) q.regs =
              some ((Dynamic.spec (2 ^ 32) (2 ^ 16) 16).stepFn
                ((Dynamic.spec (2 ^ 32) (2 ^ 16) 16).run (Dictionary.empty (2 ^ 32))
                  [.insert k3 100]).1 (.query k3)).2}) := by
  intro k3 haltProg ⟨h0, h1⟩
  rw [evalRand_halt_succ, PMF.toOuterMeasure_pure_apply] at h0 h1
  have hm0 : ∃ q : Data rWhp,
      (RandCfg.halted ((smallWhpImpl.prepare (.query k3) d₀).regs outReg)
        (smallWhpImpl.prepare (.query k3) d₀) : RandCfg rWhp) = .halted (q.regs outReg) q ∧
      WordRAM.SuccinctWhp.decode (.query k3) q.regs = some none := by
    have hstep0 :
        ((Dynamic.spec (2 ^ 32) (2 ^ 16) 16).stepFn (Dictionary.empty (2 ^ 32)) (.query k3)).2 =
          none := rfl
    rw [hstep0] at h0
    split_ifs at h0 with hm
    · exact hm
    · exact absurd h0 (lt_irrefl 0)
  have hm1 : ∃ q : Data rWhp,
      (RandCfg.halted ((smallWhpImpl.prepare (.query k3) d₁).regs outReg)
        (smallWhpImpl.prepare (.query k3) d₁) : RandCfg rWhp) = .halted (q.regs outReg) q ∧
      WordRAM.SuccinctWhp.decode (.query k3) q.regs = some (some 100) := by
    have hstep1 :
        ((Dynamic.spec (2 ^ 32) (2 ^ 16) 16).stepFn
          ((Dynamic.spec (2 ^ 32) (2 ^ 16) 16).run (Dictionary.empty (2 ^ 32))
            [.insert k3 100]).1 (.query k3)).2 = some 100 := by
      dsimp only [Dynamic.spec, StateTransitionSpec.run, StateTransitionSpec.ofFn, Dynamic.step]
      simp [Function.update_self]
    rw [hstep1] at h1
    split_ifs at h1 with hm
    · exact hm
    · exact absurd h1 (lt_irrefl 0)
  obtain ⟨q₀, hq₀, hdec₀⟩ := hm0
  obtain ⟨q₁, hq₁, hdec₁⟩ := hm1
  injection hq₀ with _ hq₀_eq
  injection hq₁ with _ hq₁_eq
  subst hq₀_eq
  subst hq₁_eq
  obtain ⟨hnot_in_tag, hnot_in_val⟩ :=
    input_resRegs_eq_false 1 (2 ^ 32) (2 ^ 16) 64 16
  have htag_eq :
      (smallWhpImpl.prepare (.query k3) d₁).regs resTagReg =
        (smallWhpImpl.prepare (.query k3) d₀).regs resTagReg := by
    rw [smallWhpImpl.prepare_regs_of_not_input hnot_in_tag,
      smallWhpImpl.prepare_regs_of_not_input hnot_in_tag]
    exact hregs resTagReg hnot_in_tag
  have hval_eq :
      (smallWhpImpl.prepare (.query k3) d₁).regs resValReg =
        (smallWhpImpl.prepare (.query k3) d₀).regs resValReg := by
    rw [smallWhpImpl.prepare_regs_of_not_input hnot_in_val,
      smallWhpImpl.prepare_regs_of_not_input hnot_in_val]
    exact hregs resValReg hnot_in_val
  dsimp only [WordRAM.SuccinctWhp.decode] at hdec₀ hdec₁
  rw [htag_eq, hval_eq] at hdec₁
  rw [hdec₀] at hdec₁
  cases hdec₁

/-- Neither `code.program outReg` nor `initFresh.program outReg` of `subroutineCode` can equal the
trivial 1-instruction `[.halt outReg]` stub. -/
theorem subroutineCode_program_ne_halt (c U V w n_max : ℕ) :
    (subroutineCode c U V w n_max).code.program outReg ≠ [.halt outReg] ∧
    (subroutineCode c U V w n_max).initFresh.program outReg ≠ [.halt outReg] := by
  have hpos : ∀ t : Code .exact rWhp, 1 ≤ t.size := by
    intro t
    induction t with
    | seq _ _ ih _ => simp only [Code.size]; omega
    | _ => simp only [Code.size]; omega
  have h_ne : ∀ s : Code .exact rWhp, s.program outReg ≠ [.halt outReg] := by
    intro s heq
    have hlen := congrArg List.length heq
    have hs := hpos s
    simp only [Code.program, List.length_append, Code.length_assemble, List.length_singleton]
      at hlen
    omega
  exact ⟨h_ne _, h_ne _⟩

end CslibFrontierTests.DataStructure.SuccinctDictionaryWhp

end
