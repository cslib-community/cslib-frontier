/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.BipartiteMatching
public import CslibFrontier.Algorithms.WordRAM.EdmondsKarp

/-!
# Network Flow, Edmonds–Karp, and Bipartite Matching Tests

Kernel-checked examples and non-vacuity witnesses (without `native_decide`) exercising:

1. **CLRS 6-vertex network (CLRS 2nd ed., Figure 26.1(a), with antiparallel arcs `(1, 2)` and
   `(2, 1)`; compare [CLRS2009], Figures 26.1–26.2, pp. 710–711):** both `edmondsKarpDense` and
   sparse `edmondsKarp` find a maximum flow of value `23` and minimum `s`-`t` cut `{0, 1, 2, 4}`
   of capacity `23`.
2. **Large-capacity diamond (`M = 10^9`), backward-arc cancellation, and simultaneous antiparallel
   flow:** `edmondsKarpDense` terminates in `2` shortest-path augmentations (`2 * 10^9` flow)
   independent of capacity magnitude; augmenting along `[0, 1, 2, 3]` followed by `bfs` exercises
   residual backward-arc cancellation along `[0, 2, 1, 3]`; and `bothWaysFlow` exercises
   simultaneous forward push and reverse cancellation across an antiparallel pair carrying positive
   flow in both directions.
3. **Bipartite matching, König's Theorem, and `HasPerfectMatching`:** asymmetric `Fin 3 × Fin 4`
   matching/cover duality (`card = size = 2`), positive and negative `decidePerfectMatching`
   instances on `Fin 3 × Fin 3`, and universe-polymorphic `Type 1` instantiations.
4. **Positive and negative witnesses** for `Network.IsCut`, `Network.Flow`, `Flow.IsAugmentingPath`,
   `AdjValid`, `IsMatching`, `IsVertexCover`, and `bfs` on edgeless graphs.
5. **Word-RAM runtime and output certificates:** `exists_edmondsKarp_program`,
   `exists_bipartiteMatching_program`, `exists_perfectMatching_program`, and
   `exists_minSeparator_program` instantiated at explicit word widths on non-trivial and boundary
   inputs.
-/

public section

namespace CslibFrontierTests.MaxFlow

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.MaxFlow

/-! ### 1. CLRS 6-vertex network (max flow = min cut = 23) -/

/-- Six-vertex shipping network (`s = 0`, `t = 5`) retaining both antiparallel arcs `(1, 2) ↦ 10`
and `(2, 1) ↦ 4` from CLRS 2nd ed., Figure 26.1(a) (compare [CLRS2009], Figures 26.1–26.2,
pp. 710–711, which split the antiparallel pair while keeping maximum flow and minimum cut `23`). -/
def clrsNet : Network (Fin 6) where
  cap u v :=
    match u.1, v.1 with
    | 0, 1 => 16
    | 0, 2 => 13
    | 1, 2 => 10
    | 2, 1 => 4
    | 1, 3 => 12
    | 3, 2 => 9
    | 2, 4 => 14
    | 4, 3 => 7
    | 3, 5 => 20
    | 4, 5 => 4
    | _, _ => 0
  s := 0
  t := 5

/-- Sparse symmetric adjacency lists for `clrsNet`. -/
def clrsAdj : Fin 6 → List (Fin 6)
  | ⟨0, _⟩ => [1, 2]
  | ⟨1, _⟩ => [0, 2, 3]
  | ⟨2, _⟩ => [0, 1, 3, 4]
  | ⟨3, _⟩ => [1, 2, 4, 5]
  | ⟨4, _⟩ => [2, 3, 5]
  | ⟨5, _⟩ => [3, 4]

theorem clrsAdj_valid : AdjValid clrsNet clrsAdj := by decide

example : ¬ AdjValid clrsNet (fun _ => []) := by decide

example : (edmondsKarpDense clrsNet).flow.value = 23 := by decide

example : (edmondsKarpDense clrsNet).cut = ({0, 1, 2, 4} : Finset (Fin 6)) := by decide

example : clrsNet.cutCapacity ({0, 1, 2, 4} : Finset (Fin 6)) = 23 := by decide

example : (edmondsKarp clrsNet clrsAdj).flow.value = 23 := by decide

example : (edmondsKarp clrsNet clrsAdj).cut = ({0, 1, 2, 4} : Finset (Fin 6)) := by decide

example :
    (edmondsKarp clrsNet clrsAdj).flow.IsMaxFlow ∧
      clrsNet.IsMinCut (edmondsKarp clrsNet clrsAdj).cut := by
  obtain ⟨hmax, hmin, _⟩ := edmondsKarp_correct clrsAdj_valid (by decide)
  exact ⟨hmax, hmin⟩

/-! ### 2. Capacity-independent `2`-augmentation diamond and backward-arc cancellation -/

/-- Ford–Fulkerson diamond network with `M = 10^9` outer capacities and unit cross arc `1 → 2`
([CLRS2009], Figure 26.6, p. 727). -/
def largeDiamondNet : Network (Fin 4) where
  cap u v :=
    match u.1, v.1 with
    | 0, 1 => 1000000000
    | 0, 2 => 1000000000
    | 1, 2 => 1
    | 1, 3 => 1000000000
    | 2, 3 => 1000000000
    | _, _ => 0
  s := 0
  t := 3

example : (edmondsKarpDense largeDiamondNet).augmentations = 2 := rfl

example : (edmondsKarpDense largeDiamondNet).flow.value = 2000000000 := by decide

example : (edmondsKarpDense largeDiamondNet).cut = ({0} : Finset (Fin 4)) := by decide

example : largeDiamondNet.cutCapacity ({0} : Finset (Fin 4)) = 2000000000 := by decide

/-- Unit diamond network exercising residual backward-arc cancellation after a zig-zag path. -/
def unitDiamondNet : Network (Fin 4) where
  cap u v :=
    match u.1, v.1 with
    | 0, 1 => 1
    | 0, 2 => 1
    | 1, 2 => 1
    | 1, 3 => 1
    | 2, 3 => 1
    | _, _ => 0
  s := 0
  t := 3

theorem zigZag_augPath :
    (Network.Flow.zero unitDiamondNet).IsAugmentingPath [0, 1, 2, 3] := by
  decide

/-- After pushing `1` unit along `[0, 1, 2, 3]`, BFS discovers `[0, 2, 1, 3]` via backward residual
arc `2 → 1`. -/
def afterZigZag : unitDiamondNet.Flow :=
  (Network.Flow.zero unitDiamondNet).augmentByBottleneck [0, 1, 2, 3] zigZag_augPath

example : afterZigZag.value = 1 := by decide

example : afterZigZag.resCap 2 1 = 1 ∧ afterZigZag.resCap 1 2 = 0 := by decide

example :
    (bfs unitDiamondNet (defaultAdj 4) afterZigZag).augPath = some [0, 2, 1, 3] := rfl

/-- Four-vertex antiparallel network (`cap 1 2 = 3`, `cap 2 1 = 2`) testing simultaneous positive
flow in both directions (`f 1 2 = 2` and `f 2 1 = 1`). -/
def antiparallelNet : Network (Fin 4) where
  cap u v :=
    match u.1, v.1 with
    | 0, 1 => 5
    | 0, 2 => 5
    | 1, 2 => 3
    | 2, 1 => 2
    | 1, 3 => 5
    | 2, 3 => 5
    | _, _ => 0
  s := 0
  t := 3

/-- Feasible flow on `antiparallelNet` carrying positive flow on both `(1, 2)` and `(2, 1)`. -/
def bothWaysFlow : antiparallelNet.Flow where
  toFun u v :=
    match u.1, v.1 with
    | 0, 1 => 2
    | 1, 2 => 2
    | 2, 1 => 1
    | 1, 3 => 1
    | 2, 3 => 1
    | _, _ => 0
  le_cap := by decide
  conserve := by decide

theorem bothWays_augPath : bothWaysFlow.IsAugmentingPath [0, 1, 2, 3] := by decide

def afterBothWays : antiparallelNet.Flow :=
  bothWaysFlow.augmentByBottleneck [0, 1, 2, 3] bothWays_augPath

example : bothWaysFlow 1 2 = 2 ∧ bothWaysFlow 2 1 = 1 ∧ bothWaysFlow.resCap 1 2 = 2 := by decide

example :
    afterBothWays 1 2 = 3 ∧ afterBothWays 2 1 = 0 ∧ afterBothWays.value = 4 := by decide

/-- Edgeless 4-vertex network verifying `bfs` returns `augPath = none` and `cut = {0}`. -/
def edgelessNet : Network (Fin 4) where
  cap _ _ := 0
  s := 0
  t := 3

example : (bfs edgelessNet (fun _ => []) (Network.Flow.zero edgelessNet)).augPath = none ∧
    (bfs edgelessNet (fun _ => []) (Network.Flow.zero edgelessNet)).cut = {0} := by decide

/-! ### 3. Bipartite matching, König's Theorem, and `HasPerfectMatching` -/

/-- Asymmetric `3 × 4` bipartite graph where left vertices `{0, 1, 2}` have neighborhood `{0, 1}`
on the right (`0` connects to `{0, 1}`; `1` and `2` connect only to `0`), so the maximum matching
and minimum vertex cover both have cardinality `2`. -/
def asymGraph : Fin 3 × Fin 4 → Bool
  | (⟨0, _⟩, ⟨0, _⟩) => true
  | (⟨0, _⟩, ⟨1, _⟩) => true
  | (⟨1, _⟩, ⟨0, _⟩) => true
  | (⟨2, _⟩, ⟨0, _⟩) => true
  | _ => false

example : (bipartiteMatching asymGraph).matching.card = 2 := by decide

example : (bipartiteMatching asymGraph).cover.size = 2 := by decide

example :
    IsMaxMatching asymGraph (bipartiteMatching asymGraph).matching ∧
      IsMinVertexCover asymGraph (bipartiteMatching asymGraph).cover := by
  obtain ⟨hmax, hmin, _⟩ := bipartiteMatching_correct asymGraph
  exact ⟨hmax, hmin⟩

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
  (decidePerfectMatching_eq_true_iff perfGraph).mp rfl

theorem noPerfGraph_not_hasPerfectMatching :
    ¬ Cslib.Circuits.BipartiteMatching.HasPerfectMatching noPerfGraph := by
  rw [← decidePerfectMatching_eq_true_iff noPerfGraph]
  decide

/-! ### 4. Positive/negative predicate witnesses and `Type 1` polymorphism -/

-- Positive and negative `IsCut` witnesses
example : unitDiamondNet.IsCut ({0, 1} : Finset (Fin 4)) := by decide
example : ¬ unitDiamondNet.IsCut ({1, 2} : Finset (Fin 4)) := by decide
example : ¬ unitDiamondNet.IsCut ({0, 3} : Finset (Fin 4)) := by decide

-- Non-zero `Network.Flow` witness (`afterZigZag`) and negative `IsAugmentingPath` witness
example : afterZigZag ≠ Network.Flow.zero unitDiamondNet := by
  intro h
  have hval : afterZigZag.value = (Network.Flow.zero unitDiamondNet).value :=
    congrArg Network.Flow.value h
  revert hval
  decide

example : ¬ afterZigZag.IsAugmentingPath [0, 1, 2, 3] := by decide

-- Degenerate `s = t` network exercising `Flow.value_le_source_outCap` without `N.s ≠ N.t`
example (f : ({ clrsNet with t := clrsNet.s }).Flow) :
    f.value ≤ (({ clrsNet with t := clrsNet.s }).cutCapacity {clrsNet.s} : ℤ) :=
  f.value_le_source_outCap

-- Positive and negative `IsMatching` witnesses
example : IsMatching asymGraph ({(0, 1), (1, 0)} : Finset (Fin 3 × Fin 4)) := by decide
example : ¬ IsMatching asymGraph ({(0, 0), (1, 0)} : Finset (Fin 3 × Fin 4)) := by decide
example : ¬ IsMatching asymGraph ({(2, 3)} : Finset (Fin 3 × Fin 4)) := by decide

-- Positive and negative `IsVertexCover` witnesses
example : IsVertexCover asymGraph ⟨{0}, {0}⟩ := by decide
example : ¬ IsVertexCover asymGraph ⟨{1, 2}, ∅⟩ := by decide

-- Universe-polymorphic `Type 1` check for Ford–Fulkerson and König's Theorem
theorem ulift_maxFlow_minCut :
    let N : Network (ULift.{1} (Fin 4)) :=
      unitDiamondNet.reindex Equiv.ulift.symm
    ∃ (f : N.Flow) (S : Finset (ULift.{1} (Fin 4))),
      f.IsMaxFlow ∧ N.IsMinCut S ∧ f.value = (N.cutCapacity S : ℤ) :=
  Network.exists_maxFlow_eq_minCut _ (by simp [Network.reindex, unitDiamondNet])

theorem ulift_koenig :
    let G : ULift.{1} (Fin 3) × ULift.{1} (Fin 4) → Bool := fun p => asymGraph (p.1.down, p.2.down)
    ∃ (M : Finset (ULift.{1} (Fin 3) × ULift.{1} (Fin 4)))
      (C : VertexCover (ULift.{1} (Fin 3)) (ULift.{1} (Fin 4))),
      IsMaxMatching G M ∧ IsMinVertexCover G C ∧ M.card = C.size :=
  exists_maxMatching_eq_minVertexCover _

/-! ### 5. Word-RAM Edmonds–Karp, bipartite matching, and vertex separator -/

section WordRAMTests

open Cslib.Algorithms.WordRAM.EdmondsKarp Cslib.WordRAM

example : ekWorkspace 4 = 44 := rfl
example : ekBound 4 1 = 84 := rfl
example : ekBound 9 1 = 814 := rfl
example : ekBound 12 6 = 2611 := rfl

/-- Dense Word-RAM Edmonds–Karp on `unitDiamondNet` (`B = 1`, width `7`): returns max flow `2`. -/
example : ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
    ∃ (y : Data R) (steps : ℕ) (f : unitDiamondNet.Flow),
      let C_cut : Finset (Fin 4) := Finset.univ.filter fun x => y.mem (ekCutAddr 4 x.1) < 4
      Runs 7 prog (State.init (encodeFlowInput unitDiamondNet)) ⟨pc, y⟩ steps ∧
      step 7 prog ⟨pc, y⟩ = .halt 2 ∧
      steps + 1 ≤ C * 5 ^ 5 ∧
      f.IsMaxFlow ∧ unitDiamondNet.IsMinCut C_cut ∧ f.value = 2 := by
  obtain ⟨R, C, pc, hC, prog, hprog⟩ := exists_edmondsKarp_program
  obtain ⟨y, steps, res, f, hruns, hhalt, htime, _, hmax, hmin, _, hval, hres⟩ :=
    hprog unitDiamondNet 1 7 (by decide) (by decide) (by decide) (by decide)
  have hval2 : f.value = 2 := by
    have hle : f.value ≤ (unitDiamondNet.cutCapacity ({0} : Finset (Fin 4)) : ℤ) :=
      f.value_le_cutCapacity (by decide)
    have hge : (edmondsKarpDense unitDiamondNet).flow.value ≤ f.value := hmax _
    have hed : (edmondsKarpDense unitDiamondNet).flow.value = 2 := by decide
    have hcut : unitDiamondNet.cutCapacity ({0} : Finset (Fin 4)) = 2 := by decide
    omega
  have hres2 : res = 2 := by omega
  subst hres2
  exact ⟨R, C, pc, hC, prog, y, steps, f, hruns, hhalt, htime, hmax, hmin, hval2⟩

/-- Dense Word-RAM Edmonds–Karp on `edgelessNet` (`B = 0`, width `7`): returns `0`. -/
example : ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
    ∃ (y : Data R) (steps : ℕ),
      Runs 7 prog (State.init (encodeFlowInput edgelessNet)) ⟨pc, y⟩ steps ∧
      step 7 prog ⟨pc, y⟩ = .halt 0 ∧ steps + 1 ≤ C * 5 ^ 5 := by
  obtain ⟨R, C, pc, hC, prog, hprog⟩ := exists_edmondsKarp_program
  obtain ⟨y, steps, res, f, hruns, hhalt, htime, _, _, hmin, _, _, hres⟩ :=
    hprog edgelessNet 0 7 (by decide) (by decide) (by decide) (by decide)
  have hzero : edgelessNet.cutCapacity (Finset.univ.filter fun x => y.mem (ekCutAddr 4 x.1) < 4) =
      0 := by
    have hle := hmin.2 ({0} : Finset (Fin 4)) (by decide)
    have hc0 : edgelessNet.cutCapacity ({0} : Finset (Fin 4)) = 0 := by decide
    omega
  rw [hres, hzero] at hhalt
  exact ⟨R, C, pc, hC, prog, y, steps, hruns, hhalt, htime⟩

/-- Word-RAM bipartite matching and König cover on asymmetric `asymGraph` (`3 × 4`, width `10`). -/
example : ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
    ∃ (y : Data R) (steps : ℕ) (M : Finset (Fin 3 × Fin 4))
      (cov : VertexCover (Fin 3) (Fin 4)),
      Runs 10 prog (State.init (encodeBipartiteInput asymGraph)) ⟨pc, y⟩ steps ∧
      step 10 prog ⟨pc, y⟩ = .halt 2 ∧
      steps + 1 ≤ C * 8 ^ 5 ∧
      IsMaxMatching asymGraph M ∧ IsMinVertexCover asymGraph cov ∧
      M.card = 2 ∧ cov.size = 2 := by
  obtain ⟨R, C, pc, hC, prog, hprog⟩ := exists_bipartiteMatching_program
  obtain ⟨y, steps, res, M, cov, hruns, hhalt, htime, hM, hCmin, hMC, hres, _, _, _⟩ :=
    hprog (w := 10) asymGraph (by decide)
  have hcard : M.card = 2 := by
    have hge : ({(0, 1), (1, 0)} : Finset (Fin 3 × Fin 4)).card ≤ M.card := hM.2 _ (by decide)
    have hle : M.card ≤ (⟨{0}, {0}⟩ : VertexCover (Fin 3) (Fin 4)).size :=
      card_le_size_of_matching_vertexCover hM.1 (by decide)
    have hc1 : ({(0, 1), (1, 0)} : Finset (Fin 3 × Fin 4)).card = 2 := by decide
    have hc2 : (⟨{0}, {0}⟩ : VertexCover (Fin 3) (Fin 4)).size = 2 := by decide
    omega
  rw [hres, hcard] at hhalt
  exact ⟨R, C, pc, hC, prog, y, steps, M, cov, hruns, hhalt, htime, hM, hCmin, hcard, by omega⟩

/-- Empty bipartite boundary `Fin 0 × Fin 0` at width `5`. -/
example : ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
    ∃ (y : Data R) (steps : ℕ),
      Runs 5 prog (State.init (encodeBipartiteInput (fun p : Fin 0 × Fin 0 => Fin.elim0 p.1)))
        ⟨pc, y⟩ steps ∧
      step 5 prog ⟨pc, y⟩ = .halt 0 ∧ steps + 1 ≤ C := by
  obtain ⟨R, C, pc, hC, prog, hprog⟩ := exists_bipartiteMatching_program
  obtain ⟨y, steps, res, M, _, hruns, hhalt, htime, _, _, _, hres, _, _, _⟩ :=
    hprog (w := 5) (fun p : Fin 0 × Fin 0 => Fin.elim0 p.1) (by decide)
  have hM0 : M.card = 0 := by
    rw [Finset.eq_empty_of_isEmpty M]; rfl
  rw [hres, hM0] at hhalt
  exact ⟨R, C, pc, hC, prog, y, steps, hruns, hhalt, by simpa using htime⟩

/-- Word-RAM perfect matching decision: positive (`perfGraph`) and negative (`noPerfGraph`) at
width `10`. -/
example : ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
    (∃ (y : Data R) (steps : ℕ),
      Runs 10 prog (State.init (encodeBipartiteInput perfGraph)) ⟨pc, y⟩ steps ∧
      step 10 prog ⟨pc, y⟩ = .halt 1 ∧ steps + 1 ≤ C * 4 ^ 5) ∧
    (∃ (y : Data R) (steps : ℕ),
      Runs 10 prog (State.init (encodeBipartiteInput noPerfGraph)) ⟨pc, y⟩ steps ∧
      step 10 prog ⟨pc, y⟩ = .halt 0 ∧ steps + 1 ≤ C * 4 ^ 5) := by
  obtain ⟨R, C, pc, hC, prog, hprog⟩ := exists_perfectMatching_program
  obtain ⟨y1, s1, r1, hr1, hh1, ht1, hiff1, _⟩ := hprog (w := 10) perfGraph (by decide)
  obtain ⟨y0, s0, r0, hr0, hh0, ht0, hiff0, hle0⟩ :=
    hprog (w := 10) noPerfGraph (by decide)
  have hr1_eq : r1 = 1 := hiff1.mpr perfGraph_hasPerfectMatching
  have hr0_eq : r0 = 0 := by
    have hne : r0 ≠ 1 := fun h => noPerfGraph_not_hasPerfectMatching (hiff0.mp h)
    omega
  rw [hr1_eq] at hh1
  rw [hr0_eq] at hh0
  exact ⟨R, C, pc, hC, prog, ⟨y1, s1, hr1, hh1, ht1⟩, ⟨y0, s0, hr0, hh0, ht0⟩⟩

/-- Five-vertex hourglass graph (`0, 1` adjacent to `2`; `2` adjacent to `3, 4`): vertex `2` is the
unique minimum separator between `{0, 1}` and `{3, 4}`. -/
def hourglassGraph : SimpleGraph (Fin 5) where
  Adj u v :=
    (u.1 = 2 ∧ v.1 ≠ 2) ∨ (v.1 = 2 ∧ u.1 ≠ 2)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

instance : DecidableRel hourglassGraph.Adj := fun u v =>
  inferInstanceAs (Decidable ((u.1 = 2 ∧ v.1 ≠ 2) ∨ (v.1 = 2 ∧ u.1 ≠ 2)))

/-- Word-RAM minimum vertex separator on `hourglassGraph` at width `12`: returns `1`, records
`{2}` at `sepOutAddr`, and labels `{0, 1}` as `1` and `{3, 4}` as `0` at `sepSideAddr`. -/
example : ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
    ∃ (y : Data R) (steps : ℕ),
      let Z : Vector Bool 5 := Vector.ofFn fun _ => false
      let A : Vector Bool 5 := Vector.ofFn fun v => decide (v.1 < 2)
      let B : Vector Bool 5 := Vector.ofFn fun v => decide (3 ≤ v.1)
      Runs 12 prog (State.init (encodeSepInput hourglassGraph Z A B)) ⟨pc, y⟩ steps ∧
      step 12 prog ⟨pc, y⟩ = .halt 1 ∧
      steps + 1 ≤ C * 6 ^ 5 ∧
      y.mem (sepOutAddr 5 2) = 1 ∧ y.mem (sepOutAddr 5 0) = 0 ∧
      y.mem (sepSideAddr 5 0) = 1 ∧ y.mem (sepSideAddr 5 3) = 0 := by
  let Z : Vector Bool 5 := Vector.ofFn fun _ => false
  let A : Vector Bool 5 := Vector.ofFn fun v => decide (v.1 < 2)
  let B : Vector Bool 5 := Vector.ofFn fun v => decide (3 ≤ v.1)
  obtain ⟨R, C, pc, hC, prog, hprog⟩ := exists_minSeparator_program
  obtain ⟨y, steps, res, out, hruns, hhalt, htime, _, _, hsep, hmin, _, hsideA, hsideB,
    hres, hout_mem, hside_mem⟩ := hprog (w := 12) hourglassGraph Z A B (by decide)
  have hY2 : hourglassGraph.IsSeparator {v | vget A v = true} {v | vget B v = true}
      ({v | vget Z v = true} ∪ ↑({(2 : Fin 5)} : Finset (Fin 5))) := by
    refine SimpleGraph.isSeparator_of_forall_adj (fun v : Fin 5 => decide (v.1 < 2)) ?_ ?_ ?_
    · intro u v huv hu hv
      have hu2 : u ≠ 2 := fun h => hu (Or.inr (by simp [h]))
      have hv2 : v ≠ 2 := fun h => hv (Or.inr (by simp [h]))
      rcases huv with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd (Fin.ext h) hu2
      · exact absurd (Fin.ext h) hv2
    · intro a ha _; simpa [A, vget] using ha
    · intro b hb _; have : 3 ≤ b.1 := by simpa [B, vget] using hb
      simp [show ¬(b.1 < 2) by omega]
  have hle1 : out.sep.length ≤ 1 := hmin {(2 : Fin 5)} hY2
  have h2mem : (2 : Fin 5) ∈ out.sep := by
    by_contra h2not
    have hnot : ∀ a : Fin 5, a.1 < 2 → ∀ b : Fin 5, 3 ≤ b.1 →
        a ∈ out.sep ∨ b ∈ out.sep := by
      intro a ha b hb
      have hpa : hourglassGraph.Adj a (2 : Fin 5) := Or.inr ⟨rfl, by omega⟩
      have hpb : hourglassGraph.Adj (2 : Fin 5) b := Or.inl ⟨rfl, by omega⟩
      let w : hourglassGraph.Walk a b := .cons hpa (.cons hpb .nil)
      obtain ⟨v, hv_supp, hv_mem⟩ := hsep.exists_mem_support (by simpa [A, vget] using ha)
        (by simpa [B, vget] using hb) w
      rcases hv_mem with hvZ | hvS
      · simp [Z, vget] at hvZ
      · simp only [w, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hv_supp
        rcases hv_supp with rfl | rfl | rfl
        · exact Or.inl hvS
        · exact absurd hvS h2not
        · exact Or.inr hvS
    have h2le : ∀ {a b : Fin 5}, a ≠ b → a ∈ out.sep → b ∈ out.sep → 2 ≤ out.sep.length := by
      intro a b hab ha hb
      rcases h : out.sep with _ | ⟨x, _ | ⟨z, _⟩⟩
      · rw [h] at ha; exact (List.not_mem_nil ha).elim
      · rw [h, List.mem_singleton] at ha hb
        exact absurd (ha.trans hb.symm) hab
      · simp
    have h03 := hnot 0 (by omega) 3 (by omega)
    have h14 := hnot 1 (by omega) 4 (by omega)
    rcases h03 with h0 | h3 <;> rcases h14 with h1 | h4
    · exact absurd (h2le (by decide) h0 h1) (by omega)
    · exact absurd (h2le (by decide) h0 h4) (by omega)
    · exact absurd (h2le (by decide) h3 h1) (by omega)
    · exact absurd (h2le (by decide) h3 h4) (by omega)
  have hlen1 : out.sep.length = 1 := by
    have hpos : 0 < out.sep.length := List.length_pos_of_mem h2mem
    omega
  have hsep_eq : out.sep = [(2 : Fin 5)] := by
    rcases heq : out.sep with _ | ⟨x, _ | ⟨z, zs⟩⟩
    · simp [heq] at hlen1
    · rw [heq, List.mem_singleton] at h2mem; rw [h2mem]
    · simp [heq] at hlen1
  have h0not : (0 : Fin 5) ∉ out.sep := by rw [hsep_eq]; decide
  rw [hres, hlen1] at hhalt
  refine ⟨R, C, pc, hC, prog, y, steps, hruns, hhalt, htime, ?_, ?_, ?_, ?_⟩
  · have := hout_mem 2; simpa [h2mem] using this
  · have := hout_mem 0; simpa [h0not] using this
  · have hs0 : vget out.side 0 = true :=
      hsideA (by simp [A, vget]) (by simp [Z, vget]) h0not
    have := hside_mem 0; simpa [hs0] using this
  · have hs3 : vget out.side 3 = false := hsideB (by simp [B, vget])
    have := hside_mem 3; simpa [hs3] using this

/-- Empty graph boundary (`n = 0`) for Word-RAM minimum vertex separator at width `5`. -/
example : ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
    ∃ (y : Data R) (steps : ℕ),
      let empty : Vector Bool 0 := Vector.ofFn Fin.elim0
      Runs 5 prog (State.init (encodeSepInput (⊥ : SimpleGraph (Fin 0)) empty empty empty))
        ⟨pc, y⟩ steps ∧
      step 5 prog ⟨pc, y⟩ = .halt 0 ∧ steps + 1 ≤ C := by
  let empty : Vector Bool 0 := Vector.ofFn Fin.elim0
  obtain ⟨R, C, pc, hC, prog, hprog⟩ := exists_minSeparator_program
  obtain ⟨y, steps, res, out, hruns, hhalt, htime, _, _, _, _, _, _, _, hres, _, _⟩ :=
    hprog (w := 5) (⊥ : SimpleGraph (Fin 0)) empty empty empty (by decide)
  have hlen0 : out.sep.length = 0 := by
    cases h : out.sep with
    | nil => rfl
    | cons x _ => exact Fin.elim0 x
  rw [hres, hlen0] at hhalt
  exact ⟨R, C, pc, hC, prog, y, steps, hruns, hhalt, by simpa using htime⟩

end WordRAMTests

end CslibFrontierTests.MaxFlow
