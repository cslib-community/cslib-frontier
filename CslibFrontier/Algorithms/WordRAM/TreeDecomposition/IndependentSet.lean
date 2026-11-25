/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.Model
public import CslibFrontier.Computability.WordRAM.Function
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.Runner
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard

/-!
# Maximum-weight independent set over a tree decomposition on the Word-RAM

This module realizes the fixed-parameter dynamic program `mwisFPT`
(`CslibFrontier.Algorithms.Lean.TreeDecomposition.IndependentSetFPT`) for maximum-weight
independent set over an array-encoded rooted tree decomposition on the exact-basis Word-RAM
(`Cslib.WordRAM.Basis.exact`). `Basis.exact` supplies unit-cost multiplication, division, and
remainder for `2`-power table sizing, bit-mask extraction (`m % 2`, `m / 2`), and row-major
adjacency-matrix indexing (`adjPtr + u * numVerts + v`) while certifying non-underflowing
subtraction and non-zero divisors in the machine semantics.

Every phase of the algorithm is executed in word-addressed memory and charged by the machine:
* parsing variable-length bag lists into 4-word node descriptors and zero-allocating all `n + 1`
  node DP tables (`initNodesProg`),
* pairwise bag independence tests via row-major adjacency-matrix reads (`noAdjScanProg`,
  `indepBagProg`),
* linear bag scans computing parent-bag masks, parent-mask restrictions, and forgotten-vertex
  weight sums (`selMemBagProg`, `keyMaskProg`, `restrictMaskProg`, `forgetWeightProg`),
* child-pass scratch-array materialization (`Memory.alloc`), in-place parent-table accumulation,
  bottom-up node traversal `n, n - 1, …, 1`, and final root maximization (`childPassProg`,
  `parentPassProg`, `processNodesProg`, `rootPassProg`).

Because every nonroot node `j ≥ 1` has `parents[j] < j`, a telescoping prefix-sum invariant over
unprocessed node tables bounds all intermediate and final table entries by
`(numNodes + 1) * maxBagLen * maxWeight`, so logarithmic word width suffices (no `2 ^ numNodes`
value growth). On any rooted tree decomposition `R : G.RootedTreeDecomposition n` of width `≤ k`,
one fixed Word-RAM program computes `mwisValue R wt` in
`O((n + 1) · 2 ^ (k + 1) · (k + 1) ^ 2)` instructions.

The implementation is factored under
`CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet` into `Instance` (flat
encoding and width-`k` complexity bounds), `InstDP` (private `ℕ`-indexed DP helpers), `Model`
(`MWISInstance.result` and `mwisFPT` / `mwisValue` bridge; publicly re-exported alongside
`Instance`), parallel scan modules `IndepScan`, `MaskOps`, and `WeightScan`, parallel DP passes
`ChildPass`, `ParentPass`, `RootPass`, and `NodeLayout`, bottom-up loop `ProcessNodes`, and `Runner`
(imported privately so the top-level interface stays minimal).

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.encodeBag`: length-prefixed bag word list.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance`: flat word-serializable instance bundle
  with `MWISInstance.encode`, `MWISInstance.result`, `MWISInstance.maxBagLen`,
  `MWISInstance.maxWeight`, `MWISInstance.wordBound`, `MWISInstance.stepBound`, and
  `MWISInstance.ofRooted`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.mwisFPTBound`: closed-form width-`k` step bound
  `6 + (n + 1) * (2 ^ (k + 1) * (5 * (k + 1) ^ 2 + 6 * (k + 1) + 32))`.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance.result_ofRooted`:
  `MWISInstance.ofRooted` computes `mwisValue R wt` (`= mwisFPT R wt L`).
* `Cslib.Algorithms.WordRAM.TreeDecomposition.exists_program_mwis_treeDecomposition`: one fixed
  `Basis.exact` Word-RAM program computes `MWISInstance.result` in `O(inst.stepBound + 1)`
  instructions at every word width `w` satisfying `Fits w inst.wordBound` and
  `InputFits w inst.encode`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.uniformComputableInTime_mwis_treeDecomposition`:
  `UniformComputableInTime .exact` certificate for `MWISInstance.result`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.exists_program_mwis_rooted`: FPT Word-RAM bound
  `O(mwisFPTBound n k + 1)` computing `mwisValue R wt` for any `R : G.RootedTreeDecomposition n` of
  width `R.width ≤ k`.

## References

* [M. Cygan et al., *Parameterized Algorithms*, Section 7.3.1][CyganEtAl2015]
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open SimpleGraph
open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-- One fixed exact-basis Word-RAM program computes maximum-weight independent set
`MWISInstance.result` in `≤ C * (inst.stepBound + 1) + 1` instructions for every word width `w`
satisfying `Fits w inst.wordBound` and `InputFits w inst.encode`. -/
theorem exists_program_mwis_treeDecomposition :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      prog.ComputesInTime
        (fun _ inst => inst.encode)
        (fun inst _ => C * (inst.stepBound + 1) + 1)
        (fun inst w => Fits w inst.wordBound)
        MWISInstance.result := by
  obtain ⟨r, C, pc, prog, _, _, hexec⟩ :=
    runMWISProg_realizes.exists_standard_init_program_state_from_words (0 : Fin 1)
  refine ⟨r, C, prog, fun inst w hw hin => ?_⟩
  have hf_len : Fits w (inst.encode.length + 1) :=
    hw.of_le (by unfold MWISInstance.wordBound; dsimp only; omega)
  obtain ⟨hval, hres, hcost⟩ := runMWISProg_spec inst hw
  obtain ⟨y, n, hruns, hhalt, _, _, hn_le⟩ :=
    hexec w () inst.encode (fun i => Fin.elim0 i) (Nat.zero_le _) hf_len hin
      ⟨inst, rfl, hw⟩ hval
  rw [clientResult_width, hres] at hhalt
  refine ⟨n + 1, ⟨⟨pc, y⟩, n, hruns, hhalt, rfl⟩, ?_⟩
  have hmul : C * (memoryCost (runMWISProg ()) (Memory.State.init inst.encode) + 0 + 1) + 1 ≤
      C * (inst.stepBound + 1) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left C (by omega)) 1
  exact hn_le.trans hmul

/-- Uniform exact-basis Word-RAM computability certificate for `MWISInstance.result`. -/
theorem uniformComputableInTime_mwis_treeDecomposition :
    ∃ C : ℕ,
      UniformComputableInTime .exact
        MWISInstance.result
        (fun _ inst => inst.encode)
        (fun inst _ => C * (inst.stepBound + 1) + 1)
        (fun inst w => Fits w inst.wordBound) := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_mwis_treeDecomposition
  refine ⟨C, r, prog, hcomp, fun inst => ?_⟩
  obtain ⟨w, hw_le, hin⟩ := InputFits.exists_width inst.encode inst.wordBound
  exact ⟨w, (fits_self inst.wordBound).mono hw_le, hin⟩

/-- **FPT Word-RAM Maximum-Weight Independent Set.** One fixed exact-basis Word-RAM program
computes `mwisValue R wt` on any graph `G` (`e : V ≃ Fin m`), rooted tree decomposition
`R : G.RootedTreeDecomposition n` of width `R.width ≤ k`, vertex weights `wt : V → ℕ`, and bag
orderings `L` (`IsBagOrder R L`) within `C * (mwisFPTBound n k + 1) + 1` instructions
(`O((n + 1) · 2 ^ (k + 1) · (k + 1) ^ 2)`). -/
theorem exists_program_mwis_rooted :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      ∀ {V : Type*} {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
        {m n k : ℕ} (e : V ≃ Fin m) (R : G.RootedTreeDecomposition n) (wt : V → ℕ)
        (L : Fin (n + 1) → List V),
        IsBagOrder R L →
        R.width ≤ k →
        ∀ w : ℕ,
          let inst := MWISInstance.ofRooted e R wt L
          Fits w inst.wordBound →
          InputFits w inst.encode →
          ∃ steps,
            Executes w prog (.init inst.encode) (mwisValue R wt) steps ∧
            steps ≤ C * (mwisFPTBound n k + 1) + 1 := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_mwis_treeDecomposition
  refine ⟨r, C, prog, fun {V G _ _ m n k} e R wt L hL hk w hw hin => ?_⟩
  let inst := MWISInstance.ofRooted e R wt L
  obtain ⟨steps, hexec, hsteps⟩ := hcomp inst w hw hin
  rw [MWISInstance.result_ofRooted e R wt hL] at hexec
  have hbound := MWISInstance.stepBound_ofRooted_le e R wt hL hk
  exact ⟨steps, hexec, hsteps.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left C (Nat.add_le_add_right hbound 1)) 1)⟩

end Cslib.Algorithms.WordRAM.TreeDecomposition
