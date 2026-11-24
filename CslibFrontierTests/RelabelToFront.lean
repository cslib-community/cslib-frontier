/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.RelabelToFront

/-!
# Relabel-to-Front Max-Flow Tests

Kernel-checked examples (without `native_decide`) for `RelabelToFront`:

1. **CLRS 6-vertex network (`clrsNet`, compare [CLRS2009], Figure 26.1):**
   `relabelToFrontExact`, `relabelToFrontDense`, and a sparse `relabelToFront` instance all compute
   a maximum flow of value `23` and minimum cut `{0, 1, 2, 4}`, instantiating
   `relabelToFrontExact_correct`, `relabelToFrontDense_correct`, `relabelToFront_correct`, and
   `relabelToFrontWith_totalSteps_le`.
2. **Move-to-front back-push (`mtfNet`):**
   discharging vertex `2` relabels `2` above previously scanned vertex `1` and pushes flow back into
   `1`, triggering move-to-front so `discharges > |V| - 2 = 3`.
3. **Subtle model boundaries and negative witnesses:**
   self-loops (`selfLoopNet`), incoming arcs at `s` and outgoing arcs at `t` (`backArcNet`),
   antiparallel arcs (`antiNet`), unreachable sink (`cutOffNet`), direct `s → t` arc (`directNet`),
   `N.s = N.t` (`loopNet`, where no `RTFInv` holds), negative `IsAdjacency`, holding vs failing
   `TopoOrder` instances, and a concrete `discharge_spec` witness.
-/

public section

namespace CslibFrontierTests.RelabelToFront

open Cslib.Algorithms.Lean.MaxFlow Network Network.Preflow Network.PushRelabel
open Network.RelabelToFront

/-! ### CLRS 6-vertex network -/

/-- The CLRS 6-vertex network with antiparallel arcs `(1, 2)` and `(2, 1)`. -/
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

theorem clrsNet_st : clrsNet.s ≠ clrsNet.t := by decide

/-- Sparse duplicate-free adjacency lists for `clrsNet`. -/
def clrsAdj (u : Fin 6) : List (Fin 6) :=
  match u.1 with
  | 0 => [1, 2]
  | 1 => [0, 2, 3]
  | 2 => [0, 1, 3, 4]
  | 3 => [1, 2, 4, 5]
  | 4 => [2, 3, 5]
  | 5 => [3, 4]
  | _ => []

theorem clrsAdj_valid : AdjValid clrsNet clrsAdj := by decide

example : (relabelToFrontExact clrsNet).flow.value = 23 := by decide +kernel

example : (relabelToFrontExact clrsNet).cut = ({0, 1, 2, 4} : Finset (Fin 6)) := by decide +kernel

example : (relabelToFrontDense clrsNet).flow.value = 23 := by decide +kernel

example : (relabelToFrontDense clrsNet).cut = ({0, 1, 2, 4} : Finset (Fin 6)) := by decide +kernel

example : (relabelToFront clrsNet clrsAdj).flow.value = 23 := by decide +kernel

example : (relabelToFront clrsNet clrsAdj).cut = ({0, 1, 2, 4} : Finset (Fin 6)) := by
  decide +kernel

example : 0 < (relabelToFrontExact clrsNet).discharges ∧
    0 < (relabelToFrontExact clrsNet).advances ∧
    0 < (PushRelabel.init clrsNet).numNonsatPushes (relabelToFrontExact clrsNet).ops := by
  decide +kernel

example :
    let out := relabelToFrontExact clrsNet
    out.flow.IsMaxFlow ∧ clrsNet.IsMinCut out.cut ∧
      (PushRelabel.init clrsNet).IsRun out.ops ∧
      out.discharges ≤ 2 * 6 ^ 3 ∧
      out.advances ≤ 4 * 6 * clrsNet.posArcs.card ∧
      out.discharges + out.ops.length + out.advances ≤ 8 * 6 ^ 3 := by
  obtain ⟨hmax, hmin, _, hrun, _, _, hdis, _, _, hadv, htot⟩ :=
    relabelToFrontExact_correct clrsNet_st
  exact ⟨hmax, hmin, hrun, hdis, hadv, htot⟩

example :
    let out := relabelToFrontDense clrsNet
    out.flow.IsMaxFlow ∧ clrsNet.IsMinCut out.cut ∧
      out.discharges + out.ops.length + out.advances ≤ 8 * 6 ^ 3 := by
  obtain ⟨hmax, hmin, _, _, _, _, _, _, _, htot⟩ := relabelToFrontDense_correct clrsNet_st
  exact ⟨hmax, hmin, htot⟩

example :
    let out := relabelToFront clrsNet clrsAdj
    out.flow.IsMaxFlow ∧ out.advances ≤ 2 * 6 * adjSteps clrsAdj ∧
      out.discharges + out.ops.length + out.advances ≤ 8 * 6 ^ 3 := by
  obtain ⟨hmax, _, _, _, _, _, _, _, _, hadv, htot⟩ :=
    relabelToFront_correct clrsAdj_valid clrsNet_st
  exact ⟨hmax, hadv, htot (by decide)⟩

/-- Generic (non-`Fin`) type instance on `Bool` exercising `relabelToFrontWith_bounds` and
`relabelToFrontWith_totalSteps_le`. -/
def boolNet : Network Bool where
  cap u v := if u = false ∧ v = true then 3 else 0
  s := false
  t := true

example :
    let out := relabelToFrontWith boolNet [] (fun b => [!b]) id id
    out.flow.IsMaxFlow ∧ out.discharges + out.ops.length + out.advances ≤ 8 * 2 ^ 3 := by
  have hadj : IsAdjacency boolNet (fun b => [!b]) := by
    intro u v huv _
    revert u v huv
    decide
  have hmem : ∀ v : Bool, v ∈ ([] : List Bool) ↔ v ≠ false ∧ v ≠ true := by
    intro v
    cases v <;> simp
  have hb := (relabelToFrontWith_totalSteps_le (V := Bool) (N := boolNet) List.nodup_nil
    hmem hadj (fun _ => rfl) (fun _ => rfl) (by decide)).2 (by intro b; simp)
  have hc := (relabelToFrontWith_correct (V := Bool) (N := boolNet) List.nodup_nil
    hmem hadj (fun _ => rfl) (fun _ => rfl) (by decide)).1
  simp only [Fintype.card_bool] at hb
  exact ⟨hc, hb⟩

/-! ### Move-to-front back-push witness -/

/-- Network `0 → 2 → 1 → 3 → 4` where vertex `2` relabels past scanned vertex `1` and pushes flow
back into `1`, forcing `discharges > |V| - 2 = 3`. -/
def mtfNet : Network (Fin 5) where
  cap u v :=
    match u.1, v.1 with
    | 0, 2 => 5
    | 2, 1 => 5
    | 1, 3 => 5
    | 3, 4 => 5
    | _, _ => 0
  s := 0
  t := 4

theorem mtfNet_st : mtfNet.s ≠ mtfNet.t := by decide

example : (relabelToFrontExact mtfNet).flow.value = 5 := by decide +kernel

example : 3 < (relabelToFrontExact mtfNet).discharges ∧
    0 < (PushRelabel.init mtfNet).numRelabels (relabelToFrontExact mtfNet).ops := by
  decide +kernel

example :
    let out := relabelToFrontExact mtfNet
    out.flow.IsMaxFlow ∧ mtfNet.IsMinCut out.cut ∧
      out.discharges + out.ops.length + out.advances ≤ 8 * 5 ^ 3 := by
  obtain ⟨hmax, hmin, _, _, _, _, _, _, _, _, htot⟩ := relabelToFrontExact_correct mtfNet_st
  exact ⟨hmax, hmin, htot⟩

/-! ### Model boundaries and edge cases -/

/-- Network with a high-capacity self-loop `(1, 1)` of capacity `9`. -/
def selfLoopNet : Network (Fin 3) where
  cap u v :=
    match u.1, v.1 with
    | 0, 1 => 4
    | 1, 1 => 9
    | 1, 2 => 4
    | _, _ => 0
  s := 0
  t := 2

theorem selfLoopNet_st : selfLoopNet.s ≠ selfLoopNet.t := by decide

example : (1 : Fin 3) ∉ exactAdj selfLoopNet 1 := by decide

example : (relabelToFrontExact selfLoopNet).flow.value = 4 ∧
    (relabelToFrontDense selfLoopNet).flow.value = 4 := by decide +kernel

example : (relabelToFrontExact selfLoopNet).flow.IsMaxFlow ∧
    (relabelToFrontDense selfLoopNet).flow.IsMaxFlow :=
  ⟨(relabelToFrontExact_correct selfLoopNet_st).1,
    (relabelToFrontDense_correct selfLoopNet_st).1⟩

/-- Network with arcs entering `s = 0` and leaving `t = 2`. -/
def backArcNet : Network (Fin 3) where
  cap u v :=
    match u.1, v.1 with
    | 0, 1 => 5
    | 1, 2 => 4
    | 1, 0 => 3
    | 2, 1 => 2
    | _, _ => 0
  s := 0
  t := 2

theorem backArcNet_st : backArcNet.s ≠ backArcNet.t := by decide

example : (relabelToFrontExact backArcNet).flow.value = 4 ∧
    backArcNet.cutCapacity (relabelToFrontExact backArcNet).cut = 4 := by decide +kernel

example : (relabelToFrontExact backArcNet).flow.IsMaxFlow :=
  (relabelToFrontExact_correct backArcNet_st).1

/-- 4-vertex network with antiparallel arcs `1 → 2` and `2 → 1`. -/
def antiNet : Network (Fin 4) where
  cap u v :=
    match u.1, v.1 with
    | 0, 1 => 2
    | 0, 2 => 2
    | 1, 2 => 1
    | 2, 1 => 1
    | 1, 3 => 1
    | 2, 3 => 3
    | _, _ => 0
  s := 0
  t := 3

example : (relabelToFrontExact antiNet).flow.value = 4 := by decide +kernel

example : (relabelToFrontExact antiNet).flow.IsMaxFlow :=
  (relabelToFrontExact_correct (by decide : antiNet.s ≠ antiNet.t)).1

/-- Network where sink `2` is unreachable from source `0`. -/
def cutOffNet : Network (Fin 3) where
  cap u v :=
    match u.1, v.1 with
    | 0, 1 => 5
    | 2, 1 => 5
    | _, _ => 0
  s := 0
  t := 2

example : (relabelToFrontExact cutOffNet).flow.value = 0 ∧
    cutOffNet.cutCapacity (relabelToFrontExact cutOffNet).cut = 0 := by decide +kernel

/-- Single arc `s → t`: all non-terminal excesses vanish initially. -/
def directNet : Network (Fin 2) where
  cap u v := if u.1 = 0 ∧ v.1 = 1 then 7 else 0
  s := 0
  t := 1

example : (relabelToFrontExact directNet).flow.value = 7 ∧
    (relabelToFrontExact directNet).ops = [] ∧
    (relabelToFrontExact directNet).discharges = 0 ∧
    (relabelToFrontExact directNet).advances = 0 := by decide +kernel

/-- Degenerate `N.s = N.t`: the solver terminates immediately with no operations and no `RTFInv`. -/
def loopNet : Network (Fin 2) where
  cap _ _ := 1
  s := 0
  t := 0

example : (relabelToFrontExact loopNet).ops = [] ∧
    (relabelToFrontExact loopNet).flow.value = 0 ∧
    (relabelToFrontExact loopNet).discharges = 0 ∧
    (relabelToFrontExact loopNet).advances = 0 := by decide

example (st : RTFState loopNet) : ¬ RTFInv (defaultAdj 2) st :=
  fun h => h.caInv.prInv.valid.source_ne_sink rfl

/-! ### Negative witnesses and `discharge_spec` -/

/-- Incomplete neighbor lists omitting `(1, 3)` fail `IsAdjacency`. -/
def badAdj (u : Fin 6) : List (Fin 6) :=
  if u = 1 then [0, 2] else clrsAdj u

example : IsAdjacency clrsNet clrsAdj := (isAdjacency_iff_adjValid).mpr clrsAdj_valid

example : ¬ IsAdjacency clrsNet badAdj :=
  fun h => absurd (h 1 3 (by decide) (by decide)) (by decide)

/-- After relabeling vertex `2` in `mtfNet`, `(2, 1)` is admissible: `[2, 1, 3]` satisfies
`TopoOrder`, while `[1, 2, 3]` violates it. -/
example : TopoOrder ((PushRelabel.init mtfNet).apply (.relabel 2)) [2, 1, 3] := by
  intro u hu v hv hpos heq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first
    | exact .head (by decide)
    | exact absurd (And.intro hpos heq) (by decide)

example : ¬ TopoOrder ((PushRelabel.init mtfNet).apply (.relabel 2)) [1, 2, 3] := by
  intro h
  have hb := h 2 (by decide) 1 (by decide) (by decide) (by decide)
  cases hb with
  | tail hb' =>
    cases hb' with
    | head hm => simp at hm
    | tail hb'' =>
      cases hb'' with
      | tail hb''' => cases hb'''

example :
    let s0 := CAState.init clrsNet (exactAdj clrsNet)
    let r := discharge (exactAdj clrsNet) tabulateCA 1 s0
    ¬ r.ca.pr.flow.IsActive 1 ∧ r.relabeled = true ∧ 0 < r.advances := by
  decide +kernel

example :
    let s0 := CAState.init clrsNet (exactAdj clrsNet)
    let r := discharge (exactAdj clrsNet) tabulateCA 1 s0
    CAInv (exactAdj clrsNet) r.ca ∧ s0.pr.IsRun r.ops ∧ ¬ r.ca.pr.flow.IsActive 1 := by
  have hspec := discharge_spec (isAdjacency_exactAdj clrsNet) tabulateCA_eq 1
    (caInv_init clrsNet_st)
  exact ⟨hspec.1, hspec.2.1, hspec.2.2.2.1⟩

end CslibFrontierTests.RelabelToFront
