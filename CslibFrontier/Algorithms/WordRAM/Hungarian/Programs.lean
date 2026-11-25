/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Hungarian.Core
public import CslibFrontier.Algorithms.WordRAM.Hungarian.Instance
public import CslibFrontier.Algorithms.WordRAM.Hungarian.Regs
import CslibFrontier.Algorithms.WordRAM.Hungarian.InputSteps
import CslibFrontier.Algorithms.WordRAM.Hungarian.MemLayout
import Mathlib.Tactic.Linarith

/-!
# End-to-end `O(n³)` Word-RAM Hungarian programs (`assignmentProgram`, `minCostProgram`)

Combines `InputSteps` and `coreCode` into `inputCode`, `assignmentProgram`, and `minCostProgram`,
establishing `executesList_assignment`, `computesListInTime_assignment`, `executes_minCost`, and
`computesInTime_minCost` within `hungarianTime n = O(n³)` instructions.
-/

public section

namespace Cslib.Algorithms.WordRAM.Hungarian

open Cslib.WordRAM
open Cslib.Algorithms.Lean.MaxFlow
open Reg

/-- Complete structured Hungarian algorithm from `Data.init inst.encode`: computes both
`outputList mem outBase = inst.assignment` and `regs acc = inst.encodedMinCost`. -/
def inputCode : Code .standard 28 :=
  .seq setupCode (.seq scanMaxCode (.seq fillCCode (.seq coreCode sumCostCode)))

/-- Fixed standard-basis Word-RAM program returning the optimal assignment list via
`ExecutesList`. -/
def assignmentProgram : Program .standard 28 := inputCode.program outBase

/-- Fixed standard-basis Word-RAM program returning `Signed.encode` of the minimum matching cost. -/
def minCostProgram : Program .standard 28 := inputCode.program acc

/-- Total instruction bound (including the final `halt`) for `assignmentProgram` and
`minCostProgram`: `99 n³ + 91 n² + 58 n + 52 = O(n³)`. -/
@[expose] def hungarianTime (n : ℕ) : ℕ :=
  99 * n ^ 3 + 91 * n ^ 2 + 58 * n + 52


private theorem exec_inputCode {w : ℕ} (inst : Instance) (hw : Fits w inst.wordBound) :
    ∃ y, ExecWithin w inputCode (Data.init inst.encode) y (hungarianTime inst.n - 1) ∧
      outputList y.mem (y.regs outBase) = inst.assignment ∧
      Fits w (y.regs outBase + inst.assignment.length) ∧
      y.regs acc = inst.encodedMinCost := by
  obtain ⟨y₁, he_setup, hb₁, hmem₁⟩ := exec_setupCode inst hw
  obtain ⟨y₂, he_scan, hb₂, hmem₂, hM_le, hM_ge⟩ := exec_scanMaxCode inst hw y₁ hb₁ hmem₁
  let M := y₂.regs rM
  let C : Fin inst.n × Fin inst.n → ℕ := fun p => (inst.cost p + (M : ℤ)).toNat
  have hC_cast : ∀ p : Fin inst.n × Fin inst.n, (C p : ℤ) = inst.cost p + (M : ℤ) :=
    fun ⟨u, v⟩ => by have := hM_ge u v; simp only [C]; omega
  have hC_le : ∀ u v : Fin inst.n, C (u, v) ≤ 2 * M :=
    fun u v => by have := hM_ge u v; simp only [C]; omega
  obtain ⟨y₃, he_fill, hb₃, hC₃⟩ := exec_fillCCode inst hw hM_le hM_ge y₂ hb₂ hmem₂
  have hfit_core :
      Fits w ((2 + inst.n * inst.n) + inst.n * inst.n + 8 * inst.n + 2 * (2 * M) + 2) :=
    hw.of_le (by unfold Instance.wordBound; nlinarith)
  obtain ⟨y₄, he_core, hr₄, _, _, hout_len, hrow_match, hf₄⟩ :=
    core_exec hC_le y₃ hb₃ hC₃ hfit_core
  have hb₄ : BaseRegs inst.n (2 + inst.n * inst.n) M y₄ := hb₃.of_eq hr₄
  have hC₄ : CostMem (2 + inst.n * inst.n) C y₄.mem := hC₃.of_outside fun a ha => hf₄ a (.inl ha)
  have hm_shift : (hungarian fun p => (C p : ℤ)).matching = (hungarian inst.cost).matching := by
    rw [funext hC_cast]; exact (hungarian_add_const inst.cost (M : ℤ)).1
  have hrm_eq : ∀ u : Fin inst.n,
      y₄.mem ((2 + inst.n * inst.n) + inst.n * inst.n + 7 * inst.n + 1 + u.val) =
        (inst.assignedCol u).val := fun u => by
    obtain ⟨v, hv_mem, hv_in⟩ := hrow_match u
    rw [hv_mem, inst.assignedCol_eq_of_mem (hm_shift ▸ hv_in)]
  obtain ⟨y₆, he_sum, hb₆, hmem₆, hacc₆⟩ :=
    exec_sumCostCode inst hw hM_le hC_cast hC_le y₄ hb₄ hC₄ hrm_eq
  have hout_list : outputList y₆.mem (y₆.regs outBase) = inst.assignment := by
    rw [hb₆.houtBase, hmem₆]
    unfold outputList
    rw [hout_len]
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    have hi : i < inst.n := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    rw [hrm_eq ⟨i, hi⟩, inst.getElem_assignment ⟨i, hi⟩]
  have hf_final : Fits w (y₆.regs outBase + inst.assignment.length) := by
    rw [hb₆.houtBase, inst.length_assignment]
    exact hw.of_le (by unfold Instance.wordBound; nlinarith)
  refine ⟨y₆, (he_setup.seq (he_scan.seq (he_fill.seq (he_core.seq he_sum)))).mono ?_,
    hout_list, hf_final, hacc₆⟩
  unfold hungarianTime coreTime; rw [Nat.add_sub_assoc (by decide : 1 ≤ 52)]; nlinarith

/-- **`O(n³)` Word-RAM minimum-cost perfect matching (`ExecutesList`).** On any `n × n` integer
assignment instance `inst` and word width `w` satisfying `Fits w inst.wordBound`,
`assignmentProgram` halts within `hungarianTime inst.n = 99 n³ + 91 n² + 58 n + 52` instructions
returning `inst.assignment` (`IsMinCostPerfectMatching`). -/
theorem executesList_assignment {w : ℕ} (inst : Instance) (hw : Fits w inst.wordBound) :
    ∃ steps, ExecutesList w assignmentProgram (.init inst.encode) inst.assignment steps ∧
      steps ≤ hungarianTime inst.n := by
  obtain ⟨y, ⟨t, ht, hex⟩, hout, hfit, _⟩ := exec_inputCode inst hw
  exact ⟨t + 1, hout ▸ hex.executesList outBase (by rwa [hout]),
    by unfold hungarianTime at ht ⊢; omega⟩

/-- **`Program.ComputesListInTime` form of `executesList_assignment`.** -/
theorem computesListInTime_assignment :
    assignmentProgram.ComputesListInTime (fun _ inst => inst.encode)
      (fun inst _ => hungarianTime inst.n) (fun inst w => Fits w inst.wordBound)
      Instance.assignment :=
  fun inst _ hw _ => executesList_assignment inst hw

/-- **`O(n³)` Word-RAM minimum matching cost (`Executes`).** On any `n × n` integer assignment
instance `inst` and word width `w` satisfying `Fits w inst.wordBound`, `minCostProgram` halts
within `hungarianTime inst.n = 99 n³ + 91 n² + 58 n + 52` instructions returning
`Signed.encode (matchingCost inst.cost (hungarian inst.cost).matching)`. -/
theorem executes_minCost {w : ℕ} (inst : Instance) (hw : Fits w inst.wordBound) :
    ∃ steps, Executes w minCostProgram (.init inst.encode) inst.encodedMinCost steps ∧
      steps ≤ hungarianTime inst.n := by
  obtain ⟨y, ⟨t, ht, hex⟩, _, _, hacc⟩ := exec_inputCode inst hw
  exact ⟨t + 1, hacc ▸ hex.executes acc, by unfold hungarianTime at ht ⊢; omega⟩

/-- **`Program.ComputesInTime` form of `executes_minCost`.** -/
theorem computesInTime_minCost :
    minCostProgram.ComputesInTime (fun _ inst => inst.encode)
      (fun inst _ => hungarianTime inst.n) (fun inst w => Fits w inst.wordBound)
      Instance.encodedMinCost :=
  fun inst _ hw _ => executes_minCost inst hw


end Cslib.Algorithms.WordRAM.Hungarian
