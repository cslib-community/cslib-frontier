/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch

/-!
# Overflow-Free Runtime `targetCap` Evaluator (`computeTargetCapProg`)

Provides `computeTargetCapProg`, a parameter-free (`¬ReadsWidth`) `Memory.Prog` evaluator computing
`targetCap U n = if n = 0 then 0 else min (2 * n) U` from word `0` (`U - 1`) of the root header in
at most `1` memory operation without intermediate `2 * n` word overflow, together with its
`RealizesBounded .exact` certificate (`realizesBounded_computeTargetCap`) and functional
specification (`computeTargetCapProg_spec`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.computeTargetCapProg`,
  `ComputeTargetCapPre`: parameter-free `Memory.Prog` evaluator for `targetCap U n` and its
  word-width precondition.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_computeTargetCap`,
  `computeTargetCapProg_spec`: `RealizesBounded .exact` certificate and functional specification.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read

/-- Evaluate `targetCap U n = if n = 0 then 0 else min (2 * n) U` from `[hdrBase]` (`= U - 1`)
without intermediate `2 * n` overflow (`¬ReadsWidth`). -/
def computeTargetCapProg : ℕ × ℕ → Memory.Prog ℕ
  | (hdrBase, n) => do
    let z0 ← pure 0
    if n = z0 then pure 0
    else do
      let uSub1 ← Memory.read hdrBase
      let uVal ← pure (uSub1 + 1)
      let rem ← pure (uVal - n)
      if rem < n then pure uVal else pure (n + n)

/-- Precondition for `computeTargetCapProg`. -/
@[expose] def ComputeTargetCapPre (w : ℕ) : ℕ × ℕ → Memory.State → Prop
  | (hdrBase, n), s =>
    hdrBase < s.frontier ∧ Fits w (s.mem hdrBase + 1) ∧ n ≤ s.mem hdrBase + 1 ∧ Fits w 1

/-- `computeTargetCapProg` compiles via `RealizesBounded .exact` without reading `w`. -/
theorem realizesBounded_computeTargetCap :
    RealizesBounded .exact computeTargetCapProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      ComputeTargetCapPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨hdrBase, n⟩
    obtain ⟨hfr, hU, hnU, h1⟩ := h
    dsimp only at *)
  all_goals try omega
  exact hU.of_le (by omega)

/-- Functional specification and `≤ 1`-read cost bound for `computeTargetCapProg`. -/
theorem computeTargetCapProg_spec {w U V N_old n_hdr n_init_hdr hdrBase n : ℕ} {s : Memory.State}
    (hhdr : RootHeaderValid U V w N_old n_hdr n_init_hdr hdrBase s.mem)
    (hfr : hdrBase < s.frontier) (hnU : n ≤ U) (hfit1 : Fits w 1) :
    ComputeTargetCapPre w (hdrBase, n) s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (computeTargetCapProg (hdrBase, n))) ∧
    (Memory.spec 0).clientState s (computeTargetCapProg (hdrBase, n)) = s ∧
    (Memory.spec 0).clientResult s (computeTargetCapProg (hdrBase, n)) = targetCap U n ∧
    memoryCost (computeTargetCapProg (hdrBase, n)) s ≤ 1 := by
  have hu_eq : s.mem hdrBase + 1 = U := by have := hhdr.pos_U; rw [hhdr.hdr_U]; omega
  have hpre : ComputeTargetCapPre w (hdrBase, n) s :=
    ⟨hfr, hu_eq.symm ▸ hhdr.fits_U, hu_eq.symm ▸ hnU, hfit1⟩
  refine ⟨hpre, ?_, ?_, ?_, ?_⟩
  · dsimp only [computeTargetCapProg]; simp only [pure_bind]
    split_ifs with hn0
    · trivial
    · rw [validHistory_bind']; refine ⟨⟨hfr, trivial⟩, ?_⟩
      simp only [prog_clientResult_read, StateTransitionSpec.clientState, prog_runClient_state_read]
      by_cases hlt : s.mem hdrBase + 1 - n < n <;> simp only [hlt, ↓reduceIte] <;> trivial
  · dsimp only [computeTargetCapProg]; simp only [pure_bind]
    split_ifs with hn0
    · rfl
    · rw [StateTransitionSpec.clientState_bind, prog_clientResult_read]
      have hs0 : (Memory.spec 0).clientState s (Memory.read hdrBase) = s := rfl
      rw [hs0]
      split_ifs <;> rfl
  · dsimp only [computeTargetCapProg, targetCap]; simp only [pure_bind]
    split_ifs with hn0
    · rfl
    · simp only [prog_clientResult_bind, prog_clientResult_read, StateTransitionSpec.clientState,
        prog_runClient_state_read, hu_eq]
      split_ifs with hlt <;> simp only [prog_clientResult_pure]
      · exact (Nat.min_eq_right (by omega)).symm
      · rw [Nat.min_eq_left (by omega)]; omega
  · dsimp only [computeTargetCapProg]; simp only [pure_bind]
    split_ifs with hn0
    · exact Nat.zero_le 1
    · simp only [Realization.memoryCost_bind', prog_memoryCost_read,
        StateTransitionSpec.clientState, prog_runClient_state_read]
      split_ifs <;> exact le_rfl

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
