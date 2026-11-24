/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick.Common
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick.EpochTick
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick.FastInsert

/-!
# Insertion, Global Epoch Ticks, and Sequence Refinement for the Pure WHP Succinct Dictionary

This module completes the deterministic step-correctness proofs for `SuccinctWhpModel`
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]).

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidFastState.fastInsert_spec`: fast-mode insertion
  / overwrite refines `Dynamic.step dict (.insert u v)` and yields `CoreFastInv`,
  `OvermarsBucketInv`, and `ValidEpochStage` whenever `fastInsert` returns `some fs'`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.epochTick_spec`: global deamortization across Stages
  `0 .. 5` and epoch rollover restores full `ValidFastState` from `CoreFastInv` +
  `OvermarsBucketInv` + `ValidEpochStagePreTick` whenever `epochTick` returns `some fs'`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidFastState.fastStepPure_spec`,
  `whpStepPure_spec`, `whpRunFrom_spec`, `whpRunPure_spec`: exact `Dynamic.step` / `Dynamic.run`
  refinement for **every** static seed `θ` across all modes (`.small`, `.fast`, `.fallback`, and
  seamless `fastToCsr` / `trySelfHeal` transitions).

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset
open scoped BigOperators

/-! ## Section 3: `fastStepPure_spec`, `whpStepPure_spec`, `whpRunFrom_spec`, `whpRunPure_spec` -/

/-- Whenever `fastStepPure` returns `some (fs', res)`, `fs'` satisfies `ValidFastState` for
`(Dynamic.step dict op).1` and `res = opResultOpt op (Dynamic.step dict op).2`. -/
theorem ValidFastState.fastStepPure_spec {c U V n_max : ℕ} (hnU : n_max ≤ U)
    {θ : SeedWhp c U n_max} {fs fs' : FastState} {dict : State U} {res : Option ℕ}
    (hv : ValidFastState c U V n_max θ fs dict)
    {op : Dynamic.Op U} (hvalid : Dynamic.valid V n_max dict op)
    (hstep : fastStepPure c U n_max θ fs op = some (fs', res)) :
    ValidFastState c U V n_max θ fs' (Dynamic.step dict op).1 ∧
    res = opResultOpt op (Dynamic.step dict op).2 := by
  cases op with
  | query u =>
    dsimp only [fastStepPure] at hstep
    cases ht : epochTick c U n_max θ fs with
    | none => rw [ht] at hstep; cases hstep
    | some fs1 =>
      rw [ht] at hstep; injection hstep with hp; injection hp with hfs1 hres
      rw [← hfs1, ← hres]
      exact ⟨epochTick_spec hv.toCore hv.overmars_valid hv.stage_valid.toPreTick ht,
        hv.fastQuery_spec u⟩
  | delete u =>
    dsimp only [fastStepPure] at hstep
    obtain ⟨hc1, hom1, hpre1, _⟩ := hv.fastDelete_spec u
    cases ht : epochTick c U n_max θ (fastDelete c U n_max θ fs u) with
    | none => rw [ht] at hstep; cases hstep
    | some fs2 =>
      rw [ht] at hstep; injection hstep with hp; injection hp with hfs2 hres
      rw [← hfs2, ← hres]
      exact ⟨epochTick_spec hc1 hom1 hpre1 ht, rfl⟩
  | insert u v =>
    dsimp only [fastStepPure] at hstep
    cases hi : fastInsert c U n_max θ fs u v with
    | none => rw [hi] at hstep; cases hstep
    | some fs1 =>
      rw [hi] at hstep
      dsimp only at hstep
      obtain ⟨hc1, hom1, hst1, _⟩ := hv.fastInsert_spec hnU hvalid hi
      cases ht : epochTick c U n_max θ fs1 with
      | none => rw [ht] at hstep; cases hstep
      | some fs2 =>
        rw [ht] at hstep; injection hstep with hp; injection hp with hfs2 hres
        rw [← hfs2, ← hres]
        exact ⟨epochTick_spec hc1 hom1 hst1.toPreTick ht, rfl⟩

/-- Exact single-step `Dynamic.step` refinement of `whpStepPure` for **every** static seed `θ`
across `.small`, `.fast` (both hit and fallback), and `.fallback` (including `trySelfHeal`). -/
theorem whpStepPure_spec {c U V n_max : ℕ} (hnU : n_max ≤ U)
    (θ : SeedWhp c U n_max) {st : WhpDictState} {dict : State U}
    (hv : ValidWhpState c U V n_max θ st dict)
    {op : Dynamic.Op U} (hvalid : Dynamic.valid V n_max dict op) :
    let (st', res) := whpStepPure c U n_max θ st op
    ValidWhpState c U V n_max θ st' (Dynamic.step dict op).1 ∧
    res = opResultOpt op (Dynamic.step dict op).2 := by
  cases st with
  | small sm =>
    obtain ⟨hlt, hsm⟩ := hv
    cases op with
    | query u => exact ⟨⟨hlt, hsm⟩, smallQuery_spec hsm u⟩
    | delete u => exact ⟨⟨hlt, smallDelete_spec hsm u⟩, rfl⟩
    | insert u v => exact ⟨⟨hlt, smallInsert_spec hsm hvalid⟩, rfl⟩
  | fast fs =>
    dsimp only [whpStepPure]
    cases hf : fastStepPure c U n_max θ fs op with
    | some p =>
      rcases p with ⟨fs', res⟩
      exact hv.fastStepPure_spec hnU hvalid hf
    | none =>
      dsimp only
      obtain ⟨hcsr0, hqv0⟩ := hv.fastToCsr_spec
      obtain ⟨hcsr1, hres1, hqv1⟩ := csrStepOp_spec hnU θ.1 hcsr0 hqv0 hvalid
      exact ⟨(trySelfHeal_spec hv.hth hcsr1 hqv1).1, hres1⟩
  | fallback csr0 =>
    obtain ⟨hth, hcsr0, hqv0⟩ := hv
    dsimp only [whpStepPure]
    obtain ⟨hcsr1, hres1, hqv1⟩ := csrStepOp_spec hnU θ.1 hcsr0 hqv0 hvalid
    exact ⟨(trySelfHeal_spec hth hcsr1 hqv1).1, hres1⟩

/-- Multi-step sequence refinement from any `ValidWhpState`. -/
theorem whpRunFrom_spec {c U V n_max : ℕ} (hnU : n_max ≤ U)
    (θ : SeedWhp c U n_max) {st : WhpDictState} {dict : State U}
    (hv : ValidWhpState c U V n_max θ st dict)
    {ops : List (Dynamic.Op U)}
    (hvh : (Dynamic.spec U V n_max).ValidHistory dict ops) :
    ValidWhpState c U V n_max θ (whpRunFrom c U n_max θ st ops)
      ((Dynamic.spec U V n_max).run dict ops).1 := by
  induction ops generalizing st dict with
  | nil => exact hv
  | cons op rest ih =>
    obtain ⟨hval, hvh_rest⟩ := hvh
    exact ih (whpStepPure_spec hnU θ hv hval).1 hvh_rest

/-- Multi-step sequence refinement starting from `whpInitPure c n_max` (`Dictionary.empty U`). -/
theorem whpRunPure_spec {c U V n_max : ℕ} (hnU : n_max ≤ U)
    (θ : SeedWhp c U n_max) {ops : List (Dynamic.Op U)}
    (hvh : (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    ValidWhpState c U V n_max θ (whpRunPure c U n_max θ ops)
      ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).1 :=
  whpRunFrom_spec hnU θ (whpInitPure_spec c U V n_max θ) hvh

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
