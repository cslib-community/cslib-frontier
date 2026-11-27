/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.BoundedTermination
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting
import CslibFrontier.Computability.Complexity.Classes.Inclusions
import CslibFrontier.Computability.Complexity.Classes.EXP.Decidable

/-!
# NP-hardness of the halting problem

[Arora and Barak, Chapter 2, Exercise 3][AroraBarak07] (2007-01-08 draft,
printed p. 62 / PDF p. 78) asks whether HALT is NP-complete. It is NP-hard, but not in NP.
Here HALT uses native finite-state binary multitape machine descriptions paired with inputs.
Partializing a decider for bounded termination gives a fixed machine that halts exactly on
positive instances. Pairing its constant description with the original input is polynomial-time;
EXP-hardness of bounded termination and `NP ⊆ EXP` then give NP-hardness of HALT.
-/

public section

namespace Cslib.Complexity

open _root_.Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- Bounded termination reduces to HALT by a constant machine description and an unchanged input.
The machine semidecides bounded termination; its execution need not be polynomial-time. -/
theorem BoundedTermination.polyTimeReducible_haltingProblem :
    PolyTimeReducible encBits (encPair encBits encBits) BoundedTermination haltingProblem := by
  obtain ⟨f, hf, hmem⟩ := isDecidable_iff.mp BoundedTermination.isDecidable
  let r : Bool → Option (List Bool) := fun b => if b then some [] else none
  obtain ⟨k, State, _, tm, htm⟩ :=
    ((IsComputable.of_finite (encIn := encBool) (encMid := encPartial) r).comp hf).exists_partialize
  let eS := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  refine ⟨fun w => (eDesc (desc eS eBit tm), w), by fun_prop, fun w => ?_⟩
  rw [desc_mem_haltingProblem_iff, halts_iff_exists_computes]
  simp only [encBits_apply] at htm
  simp only [htm, Option.mem_def]
  cases h : f w <;> simp [r, hmem w, h]

/-- **Arora–Barak, Chapter 2, Exercise 3**: HALT is NP-hard under polynomial-time many-one
reductions, with machine descriptions and inputs encoded as a framed pair of bit strings. -/
theorem haltingProblem_npHard : NPHard (encPair encBits encBits) haltingProblem :=
  fun _ enc A hA => (BoundedTermination.polyTimeHard_EXP enc A (NP_subset_EXP hA)).trans
    BoundedTermination.polyTimeReducible_haltingProblem

/-- **Arora–Barak, Chapter 2, Exercise 3**: HALT is not in NP, hence is not NP-complete. -/
theorem haltingProblem_notMem_NP : haltingProblem ∉ NP (encPair encBits encBits) :=
  fun h => not_isDecidable_haltingProblem (isDecidable_of_mem_EXP (NP_subset_EXP h))

end Cslib.Complexity
