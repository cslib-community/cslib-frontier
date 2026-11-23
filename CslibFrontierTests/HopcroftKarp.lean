/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Lean.MaxFlow.HopcroftKarp
import CslibFrontier.Algorithms.WordRAM.HopcroftKarp
meta import CslibFrontier.Algorithms.WordRAM.HopcroftKarp
-- Fast compiled machine-data interpreter for concrete flat-program runs below.
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval
import Mathlib.Data.Nat.Sqrt

/-!
# Hopcroft–Karp Tests

Kernel-checked examples (without `native_decide`) and Word-RAM execution checks for
`CslibFrontier.Algorithms.Lean.MaxFlow.AugmentingPath`,
`CslibFrontier.Algorithms.Lean.MaxFlow.HopcroftKarp`, and
`CslibFrontier.Algorithms.WordRAM.HopcroftKarp`:

1. **Two-phase trap:** on the path `u₁ — v₀ — u₀ — v₁` the first phase greedily matches
   `(u₀, v₀)`, and the length-3 augmenting path `u₁ v₀ u₀ v₁` needs a second phase. Both the dense
   and the sparse solver return the perfect matching `{(0, 1), (1, 0)}` and a cover of size `2`
   after `2 = 2⌊√2⌋` phases, so the phase bound `IsPhaseRun.le_two_mul_sqrt` is attained.
2. **Non-vacuity of the phase structures:** an explicit two-phase `IsPhaseRun` for the trap
   graph, with positive and negative `IsMaximalLayeredAugmentation` instances.
3. **Further pure instances:** a `4 × 4` upper-triangular graph (one phase, perfect matching), an
   unbalanced `5 × 3` graph (matching and cover of size `2`, plus `card_hopcroftKarp_matching_eq`),
   and positive and negative `decidePerfectMatchingHK` instances.
4. **Word-RAM `O((m + r + |E|) √ν)` sparse and `O((m + r)² √ν)` dense execution:** ordinary
   `module` client instantiations of `executesList_sparseMatching`,
   `executesList_sparseMatching_sqrt_min`, `executes_sparseCard`, `executes_sparsePerfect`,
   `decidesInTime_sparsePerfect`, `executesList_denseMatching`, and `executes_denseCard`, plus
   compiled runs of the flat `Program`s across empty, unbalanced, non-involution 3-cycle,
   duplicate-edge CSR, width-invariance, and narrow-width fault cases.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.HopcroftKarp

open Cslib.Algorithms.Lean.MaxFlow
open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.HopcroftKarp

/-! ### 1. Two-phase trap -/

theorem sqrt_two : 1 = Nat.sqrt 2 := Nat.eq_sqrt.mpr ⟨by decide, by decide⟩

/-- The path `u₁ — v₀ — u₀ — v₁` on `Fin 2 × Fin 2`. -/
def trapGraph : Fin 2 × Fin 2 → Bool
  | (⟨0, _⟩, ⟨0, _⟩) => true
  | (⟨0, _⟩, ⟨1, _⟩) => true
  | (⟨1, _⟩, ⟨0, _⟩) => true
  | _ => false

/-- Exact adjacency lists of `trapGraph`. -/
def trapAdj : Fin 2 → List (Fin 2)
  | ⟨0, _⟩ => [0, 1]
  | ⟨1, _⟩ => [0]

theorem trapAdj_valid : BipAdjValid trapGraph trapAdj := by
  unfold BipAdjValid
  decide

example : ¬ BipAdjValid trapGraph (fun _ => []) := by
  unfold BipAdjValid
  decide

example : bipAdjSteps trapAdj = 3 := by decide

example : (hopcroftKarpDense trapGraph).matching = {(0, 1), (1, 0)} := by decide

example : (hopcroftKarpDense trapGraph).cover.size = 2 := by decide

example : (hopcroftKarpDense trapGraph).phases = 2 := by decide

example : (hopcroftKarp trapGraph trapAdj).matching = {(0, 1), (1, 0)} := by decide

example : (hopcroftKarp trapGraph trapAdj).phases = 2 := by decide

/-- The phase bound `2⌊√ν⌋` is attained by the trap graph. -/
example : (hopcroftKarpDense trapGraph).phases =
    2 * Nat.sqrt (hopcroftKarpDense trapGraph).matching.card := by
  rw [show (hopcroftKarpDense trapGraph).matching.card = 2 by decide, ← sqrt_two]
  decide

example :
    IsMaxMatching trapGraph (hopcroftKarp trapGraph trapAdj).matching ∧
      IsMinVertexCover trapGraph (hopcroftKarp trapGraph trapAdj).cover := by
  obtain ⟨hmax, hmin, _⟩ := hopcroftKarp_correct trapAdj_valid
  exact ⟨hmax, hmin⟩

/-! ### 2. Non-vacuity of the phase structures -/

/-- First phase: `{(0, 0)}` is a maximal layered augmentation of the empty matching. -/
theorem trap_phase₁ : IsMaximalLayeredAugmentation trapGraph ∅ {(0, 0)} 0 := by
  refine ⟨by decide, fun u v h => absurd h (Finset.notMem_empty _), fun u v h => ?_,
    fun r hr p hp => ?_⟩
  · rw [Finset.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, isLayer_zero.mpr (by decide), .inl ⟨by decide, rfl⟩⟩
  · have hr1 : r = 1 := by
      clear hp
      revert hr
      revert r
      decide
    subst hr1
    cases hp with
    | @last _ v _ hG _ hU =>
      revert hG hU
      revert v
      decide
    | cons _ _ hM _ _ => exact absurd hM (Finset.notMem_empty _)

/-- The empty edge set is not a maximal layered augmentation: `[(0, 0)]` is still available. -/
example : ¬ IsMaximalLayeredAugmentation trapGraph ∅ ∅ 0 := fun h =>
  h.maximal 0 (by decide) [(0, 0)]
    (.last (isLayer_zero.mpr (by decide)) rfl (by decide) (by decide))

/-- Second phase: after `{(0, 0)}`, the path `u₁ v₀ u₀ v₁` is a maximal layered augmentation with
`k = 1`. -/
theorem trap_phase₂ : IsMaximalLayeredAugmentation trapGraph {(0, 0)} {(1, 0), (0, 1)} 1 := by
  refine ⟨by decide, by decide, fun u v h => ?_, fun r hr => ?_⟩
  · have hl0 : IsLayer trapGraph {(0, 0)} 0 1 := by
      unfold IsLayer
      decide
    have hl1 : IsLayer trapGraph {(0, 0)} 1 0 := isLayer_zero.mpr (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, hl1, .inr ⟨0, by decide, hl0⟩⟩
    · exact ⟨1, hl0, .inl ⟨by decide, rfl⟩⟩
  · exfalso
    revert hr
    revert r
    decide

/-- The two phases form an `IsPhaseRun` of length `2` from the empty matching. -/
theorem trap_phaseRun : IsPhaseRun trapGraph ∅ 2 := by
  refine .step (k := 0) (t := 0) (fun j hj => absurd hj (Nat.not_lt_zero j)) (by decide)
    (by decide) trap_phase₁ ?_
  have h₁ : augment ∅ ({(0, 0)} : Finset (Fin 2 × Fin 2)) = {(0, 0)} := by decide
  rw [h₁]
  refine .step (k := 1) (t := 1) (fun j hj => ?_) (by decide) (by decide) trap_phase₂ .done
  obtain rfl : j = 0 := by omega
  decide

/-! ### 3. Further pure instances -/

/-- Upper-triangular `4 × 4` graph: `(u, v)` is an edge iff `u ≤ v`. -/
def triGraph : Fin 4 × Fin 4 → Bool := fun e => decide (e.1.val ≤ e.2.val)

example : (hopcroftKarpDense triGraph).matching.card = 4 := by decide

example : (hopcroftKarpDense triGraph).phases = 1 := by decide

/-- Unbalanced `5 × 3` graph: every left vertex sees `v₀`, and `u₄` sees every right vertex. -/
def starGraph : Fin 5 × Fin 3 → Bool := fun e => decide (e.2.val = 0 ∨ e.1.val = 4)

example : (hopcroftKarpDense starGraph).matching.card = 2 := by decide

example : (hopcroftKarpDense starGraph).cover.size = 2 := by decide

theorem starGraph_maxMatching :
    IsMaxMatching starGraph ({(0, 0), (4, 1)} : Finset (Fin 5 × Fin 3)) := by
  refine ⟨by unfold IsMatching; decide, fun M' hM' => ?_⟩
  have hcov : IsVertexCover starGraph ⟨{4}, {0}⟩ := by unfold IsVertexCover; decide
  calc M'.card ≤ (⟨{4}, {0}⟩ : VertexCover (Fin 5) (Fin 3)).size :=
        card_le_size_of_matching_vertexCover hM' hcov
    _ = ({(0, 0), (4, 1)} : Finset (Fin 5 × Fin 3)).card := by decide

example : (hopcroftKarpDense starGraph).matching.card =
    ({(0, 0), (4, 1)} : Finset (Fin 5 × Fin 3)).card :=
  card_hopcroftKarp_matching_eq (bipAdjValid_denseBipAdj starGraph) starGraph_maxMatching

/-- `3 × 3` bipartite graph with a unique perfect matching `(0, 1), (1, 2), (2, 0)`. -/
def perfGraph : Fin 3 × Fin 3 → Bool
  | (⟨0, _⟩, ⟨0, _⟩) => true
  | (⟨0, _⟩, ⟨1, _⟩) => true
  | (⟨1, _⟩, ⟨2, _⟩) => true
  | (⟨2, _⟩, ⟨0, _⟩) => true
  | _ => false

/-- `3 × 3` bipartite graph violating Hall's condition (`{1, 2}` only neighbors `{0}`). -/
def noPerfGraph : Fin 3 × Fin 3 → Bool
  | (⟨0, _⟩, ⟨0, _⟩) => true
  | (⟨0, _⟩, ⟨1, _⟩) => true
  | (⟨1, _⟩, ⟨0, _⟩) => true
  | (⟨2, _⟩, ⟨0, _⟩) => true
  | _ => false

theorem perfGraph_hasPerfectMatching :
    Cslib.Circuits.BipartiteMatching.HasPerfectMatching perfGraph :=
  (decidePerfectMatchingHK_eq_true_iff (bipAdjValid_denseBipAdj perfGraph)).mp (by decide)

theorem noPerfGraph_not_hasPerfectMatching :
    ¬ Cslib.Circuits.BipartiteMatching.HasPerfectMatching noPerfGraph := by
  rw [← decidePerfectMatchingHK_eq_true_iff (bipAdjValid_denseBipAdj noPerfGraph)]
  decide

/-! ### 4. Word-RAM `O((m + r + |E|) √ν)` sparse and `O((m + r)² √ν)` dense checks -/

private def emptySparse : SparseInstance := ⟨0, 0, Fin.elim0⟩
private def leftEmptySparse : SparseInstance := ⟨0, 2, Fin.elim0⟩
private def rightEmptySparse : SparseInstance := ⟨2, 0, fun _ => []⟩
private def trapSparse : SparseInstance := ⟨2, 2, trapAdj⟩
private def perfSparse : SparseInstance := ⟨3, 3, exactBipAdj perfGraph⟩
private def noPerfSparse : SparseInstance := ⟨3, 3, exactBipAdj noPerfGraph⟩
private def starSparse : SparseInstance := ⟨5, 3, exactBipAdj starGraph⟩

/-- CSR instance with duplicate candidate edges `adj 0 = [0, 0, 1]` on `trapGraph`. -/
private def dupSparse : SparseInstance where
  m := 2
  r := 2
  adj
    | ⟨0, _⟩ => [0, 0, 1]
    | ⟨1, _⟩ => [0]

private def emptyDense : DenseInstance := ⟨0, 0, fun _ => false⟩
private def trapDense : DenseInstance := ⟨2, 2, trapGraph⟩
private def triDense : DenseInstance := ⟨4, 4, triGraph⟩
private def starDense : DenseInstance := ⟨5, 3, starGraph⟩

example : trapSparse.matchingWords = [1, 0, 0, 1] ∧ trapSparse.maxMatchingCard = 2 := by decide

example : perfSparse.matchingWords = [2, 0, 0, 1, 1, 2] ∧ perfSparse.maxMatchingCard = 3 := by
  decide

/-- Ordinary `module` client instantiation of `executesList_sparseMatching` on `trapSparse` at
`w = 16`. -/
example : ∃ steps,
    ExecutesList 16 sparseMatchingProgram (.init trapSparse.encode) [1, 0, 0, 1] steps ∧
      steps ≤ sparseTime 2 2 3 2 := by
  have hw : trapSparse.matchingWords = [1, 0, 0, 1] := by decide
  have hc : trapSparse.maxMatchingCard = 2 := by decide
  have he : trapSparse.numEdges = 3 := by decide
  rw [← hw, ← hc, ← he]
  exact executesList_sparseMatching trapSparse (by decide)

/-- Ordinary `module` client instantiation of `executesList_sparseMatching_sqrt_min` on unbalanced
`starSparse` (`5 × 3`, `7` edges) at `w = 16`. -/
example : ∃ steps,
    ExecutesList 16 sparseMatchingProgram (.init starSparse.encode)
      starSparse.matchingWords steps ∧
      steps ≤ sparseTimeSqrtMin 5 3 7 := by
  have he : starSparse.numEdges = 7 := by decide
  rw [← he]
  exact executesList_sparseMatching_sqrt_min starSparse (by decide)

/-- Ordinary `module` client instantiation of `executes_sparseCard` on `perfSparse` at `w = 16`. -/
example : ∃ steps,
    Executes 16 sparseCardProgram (.init perfSparse.encode) 3 steps ∧
      steps ≤ sparseTime 3 3 4 3 := by
  have hc : perfSparse.maxMatchingCard = 3 := by decide
  have he : perfSparse.numEdges = 4 := by decide
  rw [← hc, ← he]
  exact executes_sparseCard perfSparse (by decide)

/-- Ordinary `module` client instantiations of `executes_sparsePerfect` (positive and negative)
and `decidesInTime_sparsePerfect`. -/
example :
    (∃ steps, Executes 16 sparsePerfectProgram (.init perfSparse.encode) 1 steps ∧
      steps ≤ sparseTime 3 3 4 3) ∧
    (∃ steps, Executes 16 sparsePerfectProgram (.init noPerfSparse.encode) 0 steps ∧
      steps ≤ sparseTime 3 3 4 2) := by
  have h1 := executes_sparsePerfect perfSparse (w := 16) (by decide)
  have h2 := executes_sparsePerfect noPerfSparse (w := 16) (by decide)
  have hc1 : perfSparse.maxMatchingCard = 3 := by decide
  have he1 : perfSparse.numEdges = 4 := by decide
  have hc2 : noPerfSparse.maxMatchingCard = 2 := by decide
  have he2 : noPerfSparse.numEdges = 4 := by decide
  rw [hc1, he1] at h1
  rw [hc2, he2] at h2
  exact ⟨h1, h2⟩

example : ∃ b n,
    Executes 16 sparsePerfectProgram (.init perfSparse.encode) b n ∧
      n ≤ sparseTime perfSparse.m perfSparse.r perfSparse.numEdges perfSparse.maxMatchingCard ∧
      b ≤ 1 ∧ (b = 1 ↔ perfSparse.HasPerfectMatching) :=
  decidesInTime_sparsePerfect perfSparse 16 (by decide) (by decide)

/-- Minimal-width boundary (`emptySparse.wordBound = 14 < 2 ^ 4`). -/
example : ∃ steps,
    ExecutesList 4 sparseMatchingProgram (.init emptySparse.encode) [] steps ∧
      steps ≤ sparseTime 0 0 0 0 :=
  executesList_sparseMatching emptySparse (w := 4) (by decide)

/-- Ordinary `module` client instantiations of `executesList_denseMatching`, `executes_denseCard`,
and the direct dense optimality and flat-word indexing bridge. -/
example :
    (∃ steps, ExecutesList 16 denseMatchingProgram (.init trapDense.encode) [1, 0, 0, 1] steps ∧
      steps ≤ denseTime 2 2 2) ∧
    (∃ steps, Executes 16 denseCardProgram (.init starDense.encode) 2 steps ∧
      steps ≤ denseTime 5 3 2) := by
  have h1 := executesList_denseMatching trapDense (w := 16) (by decide)
  have h2 := executes_denseCard starDense (w := 16) (by decide)
  have hw1 : trapDense.matchingWords = [1, 0, 0, 1] := by decide
  have hc1 : trapDense.maxMatchingCard = 2 := by decide
  have hc2 : starDense.maxMatchingCard = 2 := by decide
  rw [hw1, hc1] at h1
  rw [hc2] at h2
  exact ⟨h1, h2⟩

/-- End-to-end semantic bridge: a caller runs `denseMatchingProgram` via
`executesList_denseMatching`, extracts `inst.matchingPairs`, gets `IsMaxMatching inst.graph`
directly, and reads each `(u_i, v_i)` at `matchingWords[2 * i]` / `matchingWords[2 * i + 1]`. -/
example (inst : DenseInstance) (hw : Fits 16 inst.wordBound) :
    IsMaxMatching inst.graph inst.matchingPairs.toFinset ∧
      inst.matchingWords.length = 2 * inst.maxMatchingCard ∧
      (∀ (i : ℕ) (hi : i < inst.matchingPairs.length),
        inst.matchingWords[2 * i]'(by
          rw [inst.length_matchingWords, ← inst.length_matchingPairs]; omega) =
          (inst.matchingPairs[i]'hi).1.val ∧
        inst.matchingWords[2 * i + 1]'(by
          rw [inst.length_matchingWords, ← inst.length_matchingPairs]; omega) =
          (inst.matchingPairs[i]'hi).2.val) ∧
      ∃ steps, ExecutesList 16 denseMatchingProgram (.init inst.encode) inst.matchingWords steps ∧
        steps ≤ denseTime inst.m inst.r inst.maxMatchingCard :=
  ⟨inst.isMaxMatching_matchingPairs, inst.length_matchingWords,
    fun _ hi => ⟨inst.getElem_matchingWords_even hi, inst.getElem_matchingWords_odd hi⟩,
    executesList_denseMatching inst hw⟩

/-- Concrete sparse flat-word pair indexing via `SparseInstance.getElem_matchingWords_even` and
`SparseInstance.getElem_matchingWords_odd`. -/
example :
    (∀ (i : ℕ) (hi : i < perfSparse.matchingPairs.length),
      perfSparse.matchingWords[2 * i]'(by
        rw [perfSparse.length_matchingWords, ← perfSparse.length_matchingPairs]; omega) =
        (perfSparse.matchingPairs[i]'hi).1.val ∧
      perfSparse.matchingWords[2 * i + 1]'(by
        rw [perfSparse.length_matchingWords, ← perfSparse.length_matchingPairs]; omega) =
        (perfSparse.matchingPairs[i]'hi).2.val) ∧
    IsMaxMatching perfSparse.graph perfSparse.matchingPairs.toFinset ∧
    IsMaxMatching starDense.graph starDense.matchingPairs.toFinset :=
  ⟨fun _ hi => ⟨perfSparse.getElem_matchingWords_even hi, perfSparse.getElem_matchingWords_odd hi⟩,
    perfSparse.isMaxMatching_matchingPairs, starDense.isMaxMatching_matchingPairs⟩

private meta def checkSparse (w : ℕ) (inst : SparseInstance)
    (expectedWords : List ℕ) (expectedCard expectedPerf : ℕ) : Bool :=
  let budget := sparseTime inst.m inst.r inst.numEdges inst.maxMatchingCard
  match Program.runFastList w budget sparseMatchingProgram inst.encode,
      Program.runFast w budget sparseCardProgram inst.encode,
      Program.runFast w budget sparsePerfectProgram inst.encode with
  | some (words, s₁), some (card, s₂), some (perf, s₃) =>
    words == expectedWords && card == expectedCard && perf == expectedPerf &&
      s₁ ≤ budget && s₂ ≤ budget && s₃ ≤ budget
  | _, _, _ => false

private meta def checkDense (w : ℕ) (inst : DenseInstance)
    (expectedWords : List ℕ) (expectedCard : ℕ) : Bool :=
  let budget := denseTime inst.m inst.r inst.maxMatchingCard
  match Program.runFastList w budget denseMatchingProgram inst.encode,
      Program.runFast w budget denseCardProgram inst.encode with
  | some (words, s₁), some (card, s₂) =>
    words == expectedWords && card == expectedCard && s₁ ≤ budget && s₂ ≤ budget
  | _, _ => false

/-- info: true -/
#guard_msgs in
#eval checkSparse 16 emptySparse [] 0 1

/-- info: true -/
#guard_msgs in
#eval checkSparse 16 leftEmptySparse [] 0 0

/-- info: true -/
#guard_msgs in
#eval checkSparse 16 rightEmptySparse [] 0 0

/-- info: true -/
#guard_msgs in
#eval checkSparse 16 trapSparse [1, 0, 0, 1] 2 1

/-- info: true -/
#guard_msgs in
#eval checkSparse 16 perfSparse [2, 0, 0, 1, 1, 2] 3 1

/-- info: true -/
#guard_msgs in
#eval checkSparse 16 noPerfSparse [1, 0, 0, 1] 2 0

/-- info: true -/
#guard_msgs in
#eval checkSparse 16 starSparse [0, 0, 4, 1] 2 0

/-- info: true -/
#guard_msgs in
#eval checkSparse 16 dupSparse [1, 0, 0, 1] 2 1

/-- info: true -/
#guard_msgs in
#eval checkDense 16 emptyDense [] 0

/-- info: true -/
#guard_msgs in
#eval checkDense 16 trapDense [1, 0, 0, 1] 2

/-- info: true -/
#guard_msgs in
#eval checkDense 16 triDense [0, 0, 1, 1, 2, 2, 3, 3] 4

/-- info: true -/
#guard_msgs in
#eval checkDense 16 starDense [0, 0, 4, 1] 2

-- Width invariance (`w = 16` vs `w = 64`).
/-- info: true -/
#guard_msgs in
#eval decide (Program.runFastList 16 10000 sparseMatchingProgram perfSparse.encode =
    Program.runFastList 64 10000 sparseMatchingProgram perfSparse.encode ∧
  Program.runFastList 16 20000 denseMatchingProgram starDense.encode =
    Program.runFastList 64 20000 denseMatchingProgram starDense.encode)

-- Narrow word width (`w = 2`) faults cleanly.
/-- info: true -/
#guard_msgs in
#eval decide (Program.runFastList 2 5000 sparseMatchingProgram trapSparse.encode = none ∧
  Program.runFastList 2 5000 denseMatchingProgram trapDense.encode = none)

end CslibFrontierTests.HopcroftKarp
