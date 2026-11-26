/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxCut.Derandomized
public import CslibFrontier.Computability.WordRAM.Compile
public import CslibFrontier.Computability.WordRAM.Function
public import CslibFrontier.Computability.WordRAM.ListArray
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.ListOutput
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.StructFrame
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Deterministic `1/2`-approximation for weighted `MaxCut` on the word RAM

Implements the method of conditional expectations for weighted multigraph `MaxCut` on a
deterministic `Basis.standard` word RAM (`Cslib.WordRAM.Code .standard 18`).

## Memory layout and algorithm

On an `n`-vertex weighted multigraph `edges : List WeightedEdge` (`m = edges.length`) whose
endpoints satisfy `e.u < n` and `e.v < n`, `Data.init (encode n edges)` stores:

* cell `0`: total input word length `2 + 3 * m`;
* cell `1`: vertex count `n`;
* cell `2`: edge count `m`;
* `[3, 3 + 3 * m)`: flat triples `[u₀, v₀, w₀, u₁, v₁, w₁, ...]`.

The scratch array `[3 + 3 * m, 3 + 3 * m + n)` stores the chosen vertex sides `0` (`false`) or `1`
(`true`). For each vertex `z = 0, …, n - 1` in order, the inner scan walks the `m` edges and
accumulates:

* `w0`: total weight of edges between `z` and an earlier vertex `u < z` currently on side `1`
  (edges cut if `z` is placed on side `0`), and
* `w1`: total weight of edges between `z` and an earlier vertex `u < z` currently on side `0`
  (edges cut if `z` is placed on side `1`).

Self-loops (`u = v = z`) are ignored, and edges with an endpoint `> z` remain balanced between both
sides under conditional expectations. Placing `z` on the larger-gain side (`1` when `w0 ≤ w1`, `0`
when `w1 < w0`) adds `max w0 w1 ≥ (w0 + w1) / 2` to `Reg.cutWt`, maintaining that twice the cut
weight on edges inside `{0, …, z - 1}` is at least the total non-loop weight inside
`{0, …, z - 1}`.

At `z = n`, all endpoints lie below `n`, so `maxCutCode` halts within
`maxCutTime n m = n * (20 * m + 15) + 12` (`O(|V| |E| + |V|)`) instructions with `Reg.cutWt`
holding `cutWeight edges side` and `nonLoopWeight edges ≤ 2 * cutWeight edges side`, giving a
certified deterministic `1 / 2`-approximation against every cut `τ : ℕ → Bool`.

## Main definitions

* `Cslib.Algorithms.WordRAM.MaxCut.encodeEdges`, `encode`: flat word-list encoding of `(n, edges)`.
* `Cslib.Algorithms.WordRAM.MaxCut.wordBound`: sufficient word-size bound
  `3 + 3 * edges.length + n + totalWeight edges`.
* `Cslib.Algorithms.WordRAM.MaxCut.sideAt`: cut indicator `ℕ → Bool` read from memory.
* `Cslib.Algorithms.WordRAM.MaxCut.Reg.cutWt`: output register holding the achieved cut weight.
* `Cslib.Algorithms.WordRAM.MaxCut.maxCutCode`, `maxCutProgram`: structured and compiled word-RAM
  `1 / 2`-approximation algorithm for weighted `MaxCut`.
* `Cslib.Algorithms.WordRAM.MaxCut.maxCutTime`: explicit `O(n * m + n)` instruction bound.

## Main results

* `Cslib.Algorithms.WordRAM.MaxCut.inputFits_encode`: `InputFits` certificate for `encode n edges`
  whenever all endpoints lie below `n` and `Fits w (wordBound n edges)`.
* `Cslib.Algorithms.WordRAM.MaxCut.maxCutCode_spec`: structured execution within
  `maxCutTime n edges.length` instructions computing `side` and `cutWeight edges side` with
  `nonLoopWeight edges ≤ 2 * cutWeight edges side` and
  `∀ τ, cutWeight edges τ ≤ 2 * cutWeight edges side`.
* `Cslib.Algorithms.WordRAM.MaxCut.maxCutProgram_spec`: compiled `Program .standard 18` halting
  certificate (`Executes`) within `maxCutTime n edges.length + 1` instructions returning a cut
  weight at least half of `nonLoopWeight edges` (and at least half of every cut `τ`).

## References

* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
* [D. P. Williamson and D. B. Shmoys, *The Design of Approximation Algorithms*,
  Sections 5.1–5.2][WilliamsonShmoys2011]
-/

public section

namespace Cslib.Algorithms.WordRAM.MaxCut

open Cslib.Complexity.MaxCut
open Cslib.Algorithms.Lean.MaxCut (totalWeight nonLoopWeight cutWeight_le_nonLoopWeight)
open Cslib.WordRAM Cslib.WordRAM.Block

/-! ### Input encoding and memory views -/

/-- Flat `[u, v, weight]` word list for a list of weighted edges. -/
@[expose] def encodeEdges (edges : List WeightedEdge) : List ℕ :=
  edges.flatMap fun e => [e.u, e.v, e.weight]

@[simp] theorem length_encodeEdges (edges : List WeightedEdge) :
    (encodeEdges edges).length = 3 * edges.length := by
  simp [encodeEdges, List.length_flatMap, Nat.mul_comm]

theorem getElem_encodeEdges (edges : List WeightedEdge) (i : ℕ) (hi : i < edges.length) :
    have _ : 3 * i < (encodeEdges edges).length := by rw [length_encodeEdges]; omega
    have _ : 3 * i + 1 < (encodeEdges edges).length := by rw [length_encodeEdges]; omega
    have _ : 3 * i + 2 < (encodeEdges edges).length := by rw [length_encodeEdges]; omega
    (encodeEdges edges)[3 * i] = edges[i].u ∧
      (encodeEdges edges)[3 * i + 1] = edges[i].v ∧
      (encodeEdges edges)[3 * i + 2] = edges[i].weight := by
  have hget : ∀ (j : ℕ) (hj : j < 3),
      (encodeEdges edges)[i * 3 + j]? = ([edges[i].u, edges[i].v, edges[i].weight])[j]? :=
    fun j hj => List.getElem?_flatMap_mul_add edges (fun e => [e.u, e.v, e.weight]) 3
      (fun _ _ => rfl) hi hj
  have h0 := hget 0 (by decide)
  have h1 := hget 1 (by decide)
  have h2 := hget 2 (by decide)
  simp only [Nat.mul_comm i 3, Nat.add_zero,
    List.getElem?_eq_getElem (show 3 * i < (encodeEdges edges).length by
      rw [length_encodeEdges]; omega),
    List.getElem?_eq_getElem (show 3 * i + 1 < (encodeEdges edges).length by
      rw [length_encodeEdges]; omega),
    List.getElem?_eq_getElem (show 3 * i + 2 < (encodeEdges edges).length by
      rw [length_encodeEdges]; omega)] at h0 h1 h2
  exact ⟨Option.some.inj h0, Option.some.inj h1, Option.some.inj h2⟩

/-- Full input word list `[n, edges.length, u₀, v₀, w₀, ...]` for `maxCutProgram`. -/
@[expose] def encode (n : ℕ) (edges : List WeightedEdge) : List ℕ :=
  n :: edges.length :: encodeEdges edges

@[simp] theorem length_encode (n : ℕ) (edges : List WeightedEdge) :
    (encode n edges).length = 2 + 3 * edges.length := by
  simp [encode]
  omega

/-- Sufficient upper bound on every constant, vertex/edge counter, memory address and accumulated
cut weight computed during `maxCutProgram`. -/
@[expose, wram_arith] def wordBound (n : ℕ) (edges : List WeightedEdge) : ℕ :=
  3 + 3 * edges.length + n + totalWeight edges

private theorem weight_le_totalWeight {edges : List WeightedEdge} {e : WeightedEdge}
    (he : e ∈ edges) : e.weight ≤ totalWeight edges :=
  List.le_sum_of_mem (List.mem_map_of_mem he)

/-- Every word of `encode n edges` and `(encode n edges).length` fit in width `w` whenever all
endpoints lie below `n` and `Fits w (wordBound n edges)`. -/
theorem inputFits_encode {w n : ℕ} {edges : List WeightedEdge}
    (hends : ∀ e ∈ edges, e.u < n ∧ e.v < n)
    (hw : Fits w (wordBound n edges)) :
    InputFits w (encode n edges) := by
  refine ⟨hw.of_le (by rw [length_encode]; unfold wordBound; omega), fun v hv => ?_⟩
  rcases List.mem_cons.mp hv with rfl | hv1
  · exact hw.of_le (by unfold wordBound; omega)
  · rcases List.mem_cons.mp hv1 with rfl | hmem
    · exact hw.of_le (by unfold wordBound; omega)
    · obtain ⟨e, he, hve⟩ := List.mem_flatMap.mp hmem
      have ⟨hu, hv_lt⟩ := hends e he
      have hwt := weight_le_totalWeight he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hve
      rcases hve with rfl | rfl | rfl <;> exact hw.of_le (by unfold wordBound; omega)

private def EdgesAt (mem : ℕ → ℕ) (base : ℕ) (edges : List WeightedEdge) : Prop :=
  ∀ (i : ℕ) (hi : i < edges.length),
    mem (base + 3 * i) = edges[i].u ∧
      mem (base + 3 * i + 1) = edges[i].v ∧
      mem (base + 3 * i + 2) = edges[i].weight

private theorem edgesAt_of_holdsList {mem : ℕ → ℕ} {base : ℕ} {edges : List WeightedEdge}
    (h : HoldsList base (encodeEdges edges) mem) : EdgesAt mem base edges := fun i hi => by
  obtain ⟨hu, hv, hw⟩ := getElem_encodeEdges edges i hi
  have h0 := h.get (3 * i) (by rw [length_encodeEdges]; omega)
  have h1 := h.get (3 * i + 1) (by rw [length_encodeEdges]; omega)
  have h2 := h.get (3 * i + 2) (by rw [length_encodeEdges]; omega)
  refine ⟨h0.trans hu, ?_, ?_⟩
  · rw [show base + 3 * i + 1 = base + (3 * i + 1) by omega]; exact h1.trans hv
  · rw [show base + 3 * i + 2 = base + (3 * i + 2) by omega]; exact h2.trans hw

/-- Cut indicator read from `n` cells starting at `base` (`true` iff `u < n` and cell `base + u`
contains `1`). -/
@[expose] def sideAt (mem : ℕ → ℕ) (base n : ℕ) (u : ℕ) : Bool :=
  decide (u < n ∧ mem (base + u) = 1)

/-! ### Prefix conditional-expectation invariants -/

private def belowVertex (z : ℕ) (e : WeightedEdge) : Bool :=
  decide (e.u < z ∧ e.v < z)

/-- Partner endpoint of `z` in `e`, defaulting to `z` when `e` is not incident to `z` (so the `< z`
guard evaluates to `false`). -/
private def otherEndpoint (z : ℕ) (e : WeightedEdge) : ℕ :=
  if e.u = z then e.v else if e.v = z then e.u else z

private def edgeGain (side : ℕ → Bool) (z : ℕ) (b : Bool) (e : WeightedEdge) : ℕ :=
  if otherEndpoint z e < z then (if side (otherEndpoint z e) != b then e.weight else 0) else 0

private def listGain (side : ℕ → Bool) (z : ℕ) (b : Bool) (edges : List WeightedEdge) : ℕ :=
  (edges.map (edgeGain side z b)).sum

private theorem listGain_take_succ (side : ℕ → Bool) (z : ℕ) (b : Bool)
    {edges : List WeightedEdge} {i : ℕ} (hi : i < edges.length) :
    listGain side z b (edges.take (i + 1)) =
      listGain side z b (edges.take i) + edgeGain side z b edges[i] := by
  rw [listGain, listGain, List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton]

private theorem edgeGain_le_weight (side : ℕ → Bool) (z : ℕ) (b : Bool) (e : WeightedEdge) :
    edgeGain side z b e ≤ e.weight := by
  dsimp only [edgeGain]
  split_ifs <;> omega

private theorem listGain_take_le_totalWeight (side : ℕ → Bool) (z : ℕ) (b : Bool)
    (edges : List WeightedEdge) (i : ℕ) :
    listGain side z b (edges.take i) ≤ totalWeight edges :=
  (List.sum_le_sum fun e _ => edgeGain_le_weight side z b e).trans
    (((List.take_sublist i edges).map WeightedEdge.weight).sum_le_sum fun _ _ => Nat.zero_le _)

private theorem nonLoopWeight_cons (e : WeightedEdge) (es : List WeightedEdge) :
    nonLoopWeight (e :: es) = (if e.u = e.v then 0 else e.weight) + nonLoopWeight es := by
  by_cases huv : e.u = e.v <;> simp [nonLoopWeight, huv]

private theorem cutWeight_cons (e : WeightedEdge) (es : List WeightedEdge) (side : ℕ → Bool) :
    cutWeight (e :: es) side = (if crosses side e then e.weight else 0) + cutWeight es side := by
  cases hcr : crosses side e <;> simp [cutWeight, hcr]

private theorem sum_belowVertex_succ {F₀ F₁ : List WeightedEdge → ℕ}
    {f₀ f₁ g : WeightedEdge → ℕ} (z : ℕ)
    (hnil₀ : F₀ [] = 0) (hnil₁ : F₁ [] = 0)
    (hcons₀ : ∀ e es, F₀ (e :: es) = f₀ e + F₀ es)
    (hcons₁ : ∀ e es, F₁ (e :: es) = f₁ e + F₁ es)
    (hbelow : ∀ e, e.u < z ∧ e.v < z → f₁ e = f₀ e ∧ g e = 0)
    (hnew : ∀ e, ¬(e.u < z ∧ e.v < z) → e.u < z + 1 ∧ e.v < z + 1 → f₁ e = g e)
    (habove : ∀ e, ¬(e.u < z + 1 ∧ e.v < z + 1) → g e = 0) :
    ∀ edges : List WeightedEdge,
      F₁ (edges.filter (belowVertex (z + 1))) =
        F₀ (edges.filter (belowVertex z)) + (edges.map g).sum
  | [] => by simp [hnil₀, hnil₁]
  | e :: es => by
    have ih := sum_belowVertex_succ z hnil₀ hnil₁ hcons₀ hcons₁ hbelow hnew habove es
    simp only [List.filter_cons, List.map_cons, List.sum_cons, belowVertex, decide_eq_true_eq]
    split_ifs with hlt1 hlt
    · obtain ⟨hf, hg⟩ := hbelow e hlt
      rw [hcons₁, hcons₀, ih, hf, hg]; omega
    · rw [hcons₁, ih, hnew e hlt hlt1]; omega
    · omega
    · rw [ih, habove e hlt1]; omega

private theorem nonLoop_belowVertex_succ (side : ℕ → Bool) (z : ℕ) (edges : List WeightedEdge) :
    nonLoopWeight (edges.filter (belowVertex (z + 1))) =
      nonLoopWeight (edges.filter (belowVertex z)) +
        listGain side z false edges + listGain side z true edges := by
  have h := sum_belowVertex_succ (F₀ := nonLoopWeight) (F₁ := nonLoopWeight)
    (f₀ := fun e => if e.u = e.v then 0 else e.weight)
    (f₁ := fun e => if e.u = e.v then 0 else e.weight)
    (g := fun e => edgeGain side z false e + edgeGain side z true e) z
    rfl rfl nonLoopWeight_cons nonLoopWeight_cons
    (fun e hlt => ⟨rfl, by unfold edgeGain otherEndpoint; split_ifs <;> omega⟩)
    (fun e hlt hlt1 => by
      by_cases huv : e.u = e.v
      · have hno : ¬otherEndpoint z e < z := by unfold otherEndpoint; split_ifs <;> omega
        simp [edgeGain, huv, hno]
      · have hyes : otherEndpoint z e < z := by unfold otherEndpoint; split_ifs <;> omega
        cases hs : side (otherEndpoint z e) <;> simp [edgeGain, huv, hyes, hs])
    (fun e hlt1 => by unfold edgeGain otherEndpoint; split_ifs <;> omega) edges
  rw [List.sum_map_add] at h
  dsimp only [listGain]
  omega

private theorem cutWeight_belowVertex_succ {side side' : ℕ → Bool} {z : ℕ} {b : Bool}
    (hprev : ∀ u < z, side' u = side u) (hz : side' z = b) (edges : List WeightedEdge) :
    cutWeight (edges.filter (belowVertex (z + 1))) side' =
      cutWeight (edges.filter (belowVertex z)) side + listGain side z b edges :=
  sum_belowVertex_succ (F₀ := fun es => cutWeight es side) (F₁ := fun es => cutWeight es side')
    (f₀ := fun e => if crosses side e then e.weight else 0)
    (f₁ := fun e => if crosses side' e then e.weight else 0)
    (g := edgeGain side z b) z
    rfl rfl (fun e es => cutWeight_cons e es side) (fun e es => cutWeight_cons e es side')
    (fun e hlt => ⟨by simp [crosses, hprev e.u hlt.1, hprev e.v hlt.2],
      by unfold edgeGain otherEndpoint; split_ifs <;> omega⟩)
    (fun e hlt hlt1 => by
      by_cases huv : e.u = e.v
      · have hno : ¬otherEndpoint z e < z := by unfold otherEndpoint; split_ifs <;> omega
        simp [crosses, edgeGain, huv, hno]
      · have hoth_lt : otherEndpoint z e < z := by unfold otherEndpoint; split_ifs <;> omega
        have hcr : crosses side' e = (side (otherEndpoint z e) != b) := by
          by_cases huz : e.u = z
          · rw [crosses, huz, hz, hprev e.v (by omega)]
            simp only [otherEndpoint, huz, ↓reduceIte]
            cases side e.v <;> cases b <;> rfl
          · have hvz : e.v = z := by omega
            rw [crosses, hvz, hz, hprev e.u (by omega)]
            simp [otherEndpoint, huz, hvz]
        simp [edgeGain, hoth_lt, hcr])
    (fun e hlt1 => by unfold edgeGain otherEndpoint; split_ifs <;> omega) edges

private theorem cutWeight_belowVertex_le_totalWeight (z : ℕ) (side : ℕ → Bool)
    (edges : List WeightedEdge) :
    cutWeight (edges.filter (belowVertex z)) side ≤ totalWeight edges := by
  have hnl : nonLoopWeight (edges.filter (belowVertex z)) ≤ nonLoopWeight edges :=
    ((((edges.filter_sublist (p := belowVertex z)).filter _).map
      WeightedEdge.weight).sum_le_sum fun _ _ => Nat.zero_le _)
  have htot := Cslib.Algorithms.Lean.MaxCut.totalWeight_eq_loopWeight_add_nonLoopWeight edges
  exact (cutWeight_le_nonLoopWeight (edges.filter (belowVertex z)) side).trans (by omega)

/-! ### Registers and word-RAM program -/

namespace Reg

private abbrev zero : Fin 18 := 0
private abbrev one : Fin 18 := 1
private abbrev three : Fin 18 := 2
private abbrev nReg : Fin 18 := 3
private abbrev mReg : Fin 18 := 4
private abbrev sideBase : Fin 18 := 5
private abbrev vIdx : Fin 18 := 6
/-- Output register holding the accumulated cut weight. -/
abbrev cutWt : Fin 18 := 7
private abbrev w0 : Fin 18 := 8
private abbrev w1 : Fin 18 := 9
private abbrev eIdx : Fin 18 := 10
private abbrev ePtr : Fin 18 := 11
private abbrev uReg : Fin 18 := 12
private abbrev vReg : Fin 18 := 13
private abbrev wtReg : Fin 18 := 14
private abbrev addr : Fin 18 := 15
private abbrev sVal : Fin 18 := 16
private abbrev chosen : Fin 18 := 17

end Reg

open Reg

private def setupCode : Code .standard 18 := ram[
  zero ← #0;
  one ← #1;
  three ← #3;
  nReg ← *one;
  addr ← #2;
  mReg ← *addr;
  sVal ← three * mReg;
  sideBase ← three + sVal;
  vIdx ← zero;
  cutWt ← zero ]

private def selectOtherCode : Code .standard 18 := ram[
  if uReg = vIdx then [
    sVal ← vReg
  ] else [
    if vReg = vIdx then [
      sVal ← uReg
    ] else [
      sVal ← vIdx
    ]
  ] ]

private def accumOtherCode : Code .standard 18 := ram[
  if sVal < vIdx then [
    addr ← sideBase + sVal;
    sVal ← *addr;
    if sVal = one then [ w0 ← w0 + wtReg ] else [ w1 ← w1 + wtReg ]
  ] else [
    addr ← zero
  ] ]

private def edgeScanBody : Code .standard 18 := ram[
  uReg ← *ePtr;
  addr ← ePtr + one;
  vReg ← *addr;
  addr ← addr + one;
  wtReg ← *addr;
  ⟪selectOtherCode⟫;
  ⟪accumOtherCode⟫;
  ePtr ← ePtr + three;
  eIdx ← eIdx + one ]

private def edgeScanLoop : Code .standard 18 :=
  .loop (.lt eIdx mReg) edgeScanBody

private def chooseSideCode : Code .standard 18 := ram[
  if w1 < w0 then [
    chosen ← zero;
    cutWt ← cutWt + w0
  ] else [
    chosen ← one;
    cutWt ← cutWt + w1
  ] ]

private def vertexBody : Code .standard 18 := ram[
  w0 ← zero;
  w1 ← zero;
  eIdx ← zero;
  ePtr ← three;
  ⟪edgeScanLoop⟫;
  ⟪chooseSideCode⟫;
  addr ← sideBase + vIdx;
  *addr ← chosen;
  vIdx ← vIdx + one ]

private def vertexLoop : Code .standard 18 :=
  .loop (.lt vIdx nReg) vertexBody

/-- Complete structured conditional-expectations `MaxCut` program. -/
def maxCutCode : Code .standard 18 := ram[
  ⟪setupCode⟫;
  ⟪vertexLoop⟫ ]

/-- Compiled flat `Program .standard 18` halting with the achieved cut weight in `Reg.cutWt`. -/
def maxCutProgram : Program .standard 18 :=
  maxCutCode.program cutWt

/-- Instruction budget of `maxCutCode` on `n` vertices and `m` edges (`O(n * m + n)`). -/
@[expose] def maxCutTime (n m : ℕ) : ℕ :=
  n * (20 * m + 15) + 12

/-! ### Correctness and instruction-count proof -/

private structure Frame (n : ℕ) (edges : List WeightedEdge) (x : Data 18) : Prop where
  zero_eq : x.regs zero = 0
  one_eq : x.regs one = 1
  three_eq : x.regs three = 3
  nReg_eq : x.regs nReg = n
  mReg_eq : x.regs mReg = edges.length
  sideBase_eq : x.regs sideBase = 3 + 3 * edges.length
  hedges : HoldsList 3 (encodeEdges edges) x.mem

private theorem selectOtherCode_spec {w z : ℕ} (e : WeightedEdge) {y : Data 18}
    (hvIdx : y.regs vIdx = z) (hu : y.regs uReg = e.u) (hv : y.regs vReg = e.v) :
    ∃ y', ExecWithin w selectOtherCode y y' 5 ∧
      y'.mem = y.mem ∧
      y'.regs sVal = otherEndpoint z e := by
  refine WP.exists_execWithin (w := w) (c := selectOtherCode) ?_
  unfold selectOtherCode otherEndpoint
  by_cases huz : e.u = z
  · wram_exec [hvIdx, hu, hv, huz]
    exact ⟨rfl, by wram_simp; simp [huz]⟩
  · by_cases hvz : e.v = z
    · wram_exec [hvIdx, hu, hv, huz, hvz]
      exact ⟨rfl, by wram_simp; simp [huz, hvz]⟩
    · wram_exec [hvIdx, hu, hv, huz, hvz]
      exact ⟨rfl, by wram_simp; simp [huz, hvz]⟩

private theorem accumOtherCode_spec {w n z g0 g1 : ℕ} {edges : List WeightedEdge}
    (e : WeightedEdge) {y : Data 18}
    (hz : z < n)
    (hz0 : y.regs zero = 0) (ho1 : y.regs one = 1)
    (hsBase : y.regs sideBase = 3 + 3 * edges.length)
    (hvIdx : y.regs vIdx = z)
    (hwt : y.regs wtReg = e.weight)
    (hsVal : y.regs sVal = otherEndpoint z e)
    (hw0 : y.regs w0 = g0) (hw1 : y.regs w1 = g1)
    (hfit0 : Fits w (g0 + edgeGain (sideAt y.mem (3 + 3 * edges.length) n) z false e))
    (hfit1 : Fits w (g1 + edgeGain (sideAt y.mem (3 + 3 * edges.length) n) z true e))
    (hw : Fits w (wordBound n edges)) :
    ∃ y', ExecWithin w accumOtherCode y y' 6 ∧
      y'.mem = y.mem ∧
      y'.regs w0 = g0 + edgeGain (sideAt y.mem (3 + 3 * edges.length) n) z false e ∧
      y'.regs w1 = g1 + edgeGain (sideAt y.mem (3 + 3 * edges.length) n) z true e := by
  set side := sideAt y.mem (3 + 3 * edges.length) n
  set u := otherEndpoint z e with hu_def
  refine WP.exists_execWithin (w := w) (c := accumOtherCode) ?_
  unfold accumOtherCode
  by_cases huz : u < z
  · have hun : u < n := by omega
    have : Fits w (3 + 3 * edges.length + u) := hw.of_le (by unfold wordBound; omega)
    by_cases hmem1 : y.mem (3 + 3 * edges.length + u) = 1
    · have hside_u : side u = true := by simp [side, sideAt, hun, hmem1]
      have hg0 : edgeGain side z false e = e.weight := by simp [edgeGain, ← hu_def, huz, hside_u]
      have hg1 : edgeGain side z true e = 0 := by simp [edgeGain, ← hu_def, huz, hside_u]
      have : Fits w (g0 + e.weight) := by rwa [← hg0]
      wram_exec [hz0, ho1, hsBase, hvIdx, hwt, hsVal, hw0, hw1, huz, hmem1]
      exact ⟨rfl, by wram_simp; omega, by wram_simp; omega⟩
    · have hside_u : side u = false := by simp [side, sideAt, hun, hmem1]
      have hg0 : edgeGain side z false e = 0 := by simp [edgeGain, ← hu_def, huz, hside_u]
      have hg1 : edgeGain side z true e = e.weight := by simp [edgeGain, ← hu_def, huz, hside_u]
      have : Fits w (g1 + e.weight) := by rwa [← hg1]
      wram_exec [hz0, ho1, hsBase, hvIdx, hwt, hsVal, hw0, hw1, huz, hmem1]
      exact ⟨rfl, by wram_simp; omega, by wram_simp; omega⟩
  · have hg0 : edgeGain side z false e = 0 := by simp [edgeGain, ← hu_def, huz]
    have hg1 : edgeGain side z true e = 0 := by simp [edgeGain, ← hu_def, huz]
    wram_exec [hz0, ho1, hsBase, hvIdx, hwt, hsVal, hw0, hw1, huz]
    exact ⟨rfl, by wram_simp; omega, by wram_simp; omega⟩

private theorem edgeScanLoop_spec {w n z : ℕ} {edges : List WeightedEdge} {x : Data 18}
    (hx : Frame n edges x) (hz : z < n) (hvIdx : x.regs vIdx = z)
    (hw0 : x.regs w0 = 0) (hw1 : x.regs w1 = 0)
    (heIdx : x.regs eIdx = 0) (hePtr : x.regs ePtr = 3)
    (hw : Fits w (wordBound n edges)) :
    ∃ y, ExecWithin w edgeScanLoop x y (20 * edges.length + 2) ∧
      y.mem = x.mem ∧
      y.regs w0 = listGain (sideAt x.mem (3 + 3 * edges.length) n) z false edges ∧
      y.regs w1 = listGain (sideAt x.mem (3 + 3 * edges.length) n) z true edges := by
  let side := sideAt x.mem (3 + 3 * edges.length) n
  have hlenE := length_encodeEdges edges
  have hedges_at : EdgesAt x.mem 3 edges := edgesAt_of_holdsList hx.hedges
  let P (i : ℕ) (y : Data 18) : Prop :=
    Frame n edges y ∧
    y.mem = x.mem ∧
    y.regs vIdx = z ∧
    y.regs ePtr = 3 + 3 * i ∧
    y.regs w0 = listGain side z false (edges.take i) ∧
    y.regs w1 = listGain side z true (edges.take i)
  have hP0 : P (x.regs eIdx) x := by
    rw [heIdx]
    exact ⟨hx, rfl, hvIdx, by simp [hePtr], by simp [hw0, listGain], by simp [hw1, listGain]⟩
  obtain ⟨y, hy, ⟨-, hym, -, -, hyw0, hyw1⟩, _⟩ :=
    ExecWithin.loop_count (B := .standard) (w := w) (N := edges.length) (T := 18) P
      (fun _ hyP => hyP.1.mReg_eq)
      (fun y ⟨hyf_y, hym_y, hvIdx_y, hePtr_y, hyw0_y, hyw1_y⟩ hi => by
        set i := y.regs eIdx with hi_eq
        symm at hi_eq
        obtain ⟨hu_mem, hv_mem, hw_mem⟩ := hedges_at i hi
        have hu_y : y.mem (3 + 3 * i) = edges[i].u := by rw [hym_y]; exact hu_mem
        have hv_y : y.mem (3 + 3 * i + 1) = edges[i].v := by rw [hym_y]; exact hv_mem
        have hw_y : y.mem (3 + 3 * i + 2) = edges[i].weight := by rw [hym_y]; exact hw_mem
        have hw0_cur := listGain_take_succ side z false hi
        have hw1_cur := listGain_take_succ side z true hi
        have hw0_le := listGain_take_le_totalWeight side z false edges (i + 1)
        have hw1_le := listGain_take_le_totalWeight side z true edges (i + 1)
        have hfit0 : Fits w (listGain side z false (edges.take i) +
            edgeGain side z false edges[i]) := by
          rw [← hw0_cur]; exact hw.of_le (by unfold wordBound; omega)
        have hfit1 : Fits w (listGain side z true (edges.take i) +
            edgeGain side z true edges[i]) := by
          rw [← hw1_cur]; exact hw.of_le (by unfold wordBound; omega)
        have : Fits w (3 + 3 * i + 1) := hw.of_le (by unfold wordBound; omega)
        have : Fits w (3 + 3 * i + 2) := hw.of_le (by unfold wordBound; omega)
        have : Fits w (3 + 3 * i + 3) := hw.of_le (by unfold wordBound; omega)
        have : Fits w (i + 1) := hw.of_le (by unfold wordBound; omega)
        refine WP.exists_execWithin (w := w) (c := edgeScanBody) ?_
        unfold edgeScanBody
        wram_exec [hyf_y.one_eq, hePtr_y, hu_y, hv_y, hw_y]
        wram_call (selectOtherCode_spec (w := w) (z := z) edges[i]) [hvIdx_y] with
          y₁ ⟨hy₁_mem, hy₁_sVal⟩
        wram_simp at hy₁_mem
        have hy₁_x : y₁.mem = x.mem := hy₁_mem.trans hym_y
        have hfit0' : Fits w (listGain side z false (edges.take i) +
            edgeGain (sideAt y₁.mem (3 + 3 * edges.length) n) z false edges[i]) := by
          simpa only [hy₁_x] using hfit0
        have hfit1' : Fits w (listGain side z true (edges.take i) +
            edgeGain (sideAt y₁.mem (3 + 3 * edges.length) n) z true edges[i]) := by
          simpa only [hy₁_x] using hfit1
        have ⟨hy₁_z0, hy₁_o1, hy₁_sb, hy₁_vIdx, hy₁_wt, hy₁_w0, hy₁_w1⟩ :
            y₁.regs zero = 0 ∧ y₁.regs one = 1 ∧
            y₁.regs sideBase = 3 + 3 * edges.length ∧ y₁.regs vIdx = z ∧
            y₁.regs wtReg = edges[i].weight ∧
            y₁.regs w0 = listGain side z false (edges.take i) ∧
            y₁.regs w1 = listGain side z true (edges.take i) := by
          have := hyf_y.zero_eq; have := hyf_y.one_eq; have := hyf_y.sideBase_eq
          regs_frame
        wram_call (accumOtherCode_spec edges[i] hz hy₁_z0 hy₁_o1 hy₁_sb hy₁_vIdx hy₁_wt hy₁_sVal
          hy₁_w0 hy₁_w1 hfit0' hfit1' hw) with y₂ ⟨hy₂_mem, hy₂_w0, hy₂_w1⟩
        have hy₂_x : y₂.mem = x.mem := hy₂_mem.trans hy₁_x
        simp only [hy₁_x] at hy₂_w0 hy₂_w1
        change y₂.regs w0 = listGain side z false (edges.take i) +
          edgeGain side z false edges[i] at hy₂_w0
        change y₂.regs w1 = listGain side z true (edges.take i) +
          edgeGain side z true edges[i] at hy₂_w1
        have hy₂_frame : Frame n edges y₂ := by struct_frame hyf_y
        have ⟨hy₂_vIdx, hy₂_ePtr, hy₂_eIdx⟩ :
            y₂.regs vIdx = z ∧ y₂.regs ePtr = 3 + 3 * i ∧ y₂.regs eIdx = i := by
          regs_frame
        wram_exec [hy₂_ePtr, hy₂_frame.three_eq, hy₂_eIdx, hy₂_frame.one_eq]
        refine ⟨⟨by struct_frame hy₂_frame, hy₂_x, by regs_frame, by wram_simp; omega,
          by wram_simp [hy₂_w0, hw0_cur], by wram_simp [hy₂_w1, hw1_cur]⟩, by wram_simp⟩)
      (by rw [heIdx]; exact Nat.zero_le _) hP0
  refine ⟨y, hy.mono (by rw [heIdx]; omega), hym, ?_, ?_⟩
  · simpa [side] using hyw0
  · simpa [side] using hyw1

private theorem chooseSideCode_spec {w g0 g1 : ℕ} {y : Data 18}
    (hz0 : y.regs zero = 0) (ho1 : y.regs one = 1)
    (hw0 : y.regs w0 = g0) (hw1 : y.regs w1 = g1)
    (hfit : Fits w (y.regs cutWt + max g0 g1)) :
    ∃ y', ExecWithin w chooseSideCode y y' 4 ∧
      y'.mem = y.mem ∧
      y'.regs chosen = (decide (g0 ≤ g1)).toNat ∧
      y'.regs cutWt = y.regs cutWt + max g0 g1 := by
  refine WP.exists_execWithin (w := w) (c := chooseSideCode) ?_
  unfold chooseSideCode
  by_cases hlt : g1 < g0
  · have hmax : max g0 g1 = g0 := Nat.max_eq_left (Nat.le_of_lt hlt)
    have hdec : decide (g0 ≤ g1) = false := decide_eq_false (Nat.not_le.mpr hlt)
    have : Fits w (y.regs cutWt + g0) := by rwa [← hmax]
    wram_exec [hz0, ho1, hw0, hw1, hlt]
    exact ⟨rfl, by wram_simp; simp [hdec], by wram_simp; omega⟩
  · have hle : g0 ≤ g1 := Nat.not_lt.mp hlt
    have hmax : max g0 g1 = g1 := Nat.max_eq_right hle
    have hdec : decide (g0 ≤ g1) = true := decide_eq_true hle
    have : Fits w (y.regs cutWt + g1) := by rwa [← hmax]
    wram_exec [hz0, ho1, hw0, hw1, hlt]
    exact ⟨rfl, by wram_simp; simp [hdec], by wram_simp; omega⟩

private theorem vertexLoop_spec {w n : ℕ} (edges : List WeightedEdge) {x : Data 18}
    (hx : Frame n edges x) (hv0 : x.regs vIdx = 0) (hc0 : x.regs cutWt = 0)
    (hw : Fits w (wordBound n edges)) :
    ∃ y, ExecWithin w vertexLoop x y (n * (20 * edges.length + 15) + 2) ∧
      Frame n edges y ∧
      (∀ u < n, y.mem (3 + 3 * edges.length + u) ≤ 1) ∧
      y.regs cutWt =
        cutWeight (edges.filter (belowVertex n)) (sideAt y.mem (3 + 3 * edges.length) n) ∧
      nonLoopWeight (edges.filter (belowVertex n)) ≤ 2 * y.regs cutWt := by
  have hlenE := length_encodeEdges edges
  let sBase := 3 + 3 * edges.length
  let P (z : ℕ) (y : Data 18) : Prop :=
    Frame n edges y ∧
    (∀ u < z, y.mem (sBase + u) ≤ 1) ∧
    y.regs cutWt = cutWeight (edges.filter (belowVertex z)) (sideAt y.mem sBase n) ∧
    nonLoopWeight (edges.filter (belowVertex z)) ≤ 2 * y.regs cutWt
  have hP0 : P (x.regs vIdx) x := by
    rw [hv0]
    have hemp : edges.filter (belowVertex 0) = [] :=
      List.filter_eq_nil_iff.mpr fun e _ => by simp [belowVertex]
    exact ⟨hx, fun _ hu => absurd hu (Nat.not_lt_zero _),
      by simp [hc0, hemp, cutWeight], by simp [hc0, hemp, nonLoopWeight]⟩
  obtain ⟨y, hy, ⟨hyf, hyside, hycut, hynl⟩, _⟩ :=
    ExecWithin.loop_count (B := .standard) (w := w) (N := n) (T := 20 * edges.length + 13) P
      (fun _ hyP => hyP.1.nReg_eq)
      (fun y ⟨hyf_y, hyside_y, hycut_y, hynl_y⟩ hz => by
        set z := y.regs vIdx with hz_eq
        symm at hz_eq
        let side := sideAt y.mem sBase n
        let g0 := listGain side z false edges
        let g1 := listGain side z true edges
        let bChoice : Bool := decide (g0 ≤ g1)
        let gainBest : ℕ := max g0 g1
        have hgainBest_eq : gainBest = listGain side z bChoice edges := by
          dsimp only [gainBest, bChoice, g0, g1]
          by_cases hle : listGain side z false edges ≤ listGain side z true edges
          · simp [hle]
          · simp [hle, Nat.max_eq_left (Nat.le_of_not_le hle)]
        have hside'_prev : ∀ u < z,
            sideAt (Function.update y.mem (sBase + z) bChoice.toNat) sBase n u = side u := by
          intro u hu
          have hne : sBase + u ≠ sBase + z := by omega
          simp [side, sideAt, Function.update_of_ne hne]
        have hside'_z :
            sideAt (Function.update y.mem (sBase + z) bChoice.toNat) sBase n z = bChoice := by
          dsimp only [bChoice]
          cases (decide (g0 ≤ g1)) <;> simp [sideAt, hz]
        have hcut_next := cutWeight_belowVertex_succ hside'_prev hside'_z edges
        have hcut_next_le := cutWeight_belowVertex_le_totalWeight (z + 1)
          (sideAt (Function.update y.mem (sBase + z) bChoice.toNat) sBase n) edges
        have hnl_next := nonLoop_belowVertex_succ side z edges
        have h2max : g0 + g1 ≤ 2 * gainBest := by dsimp only [gainBest]; omega
        have : Fits w (sBase + z) := hw.of_le (by unfold wordBound; omega)
        have : Fits w (z + 1) := hw.of_le (by unfold wordBound; omega)
        refine WP.exists_execWithin (w := w) (c := vertexBody) ?_
        unfold vertexBody
        wram_exec [hyf_y.zero_eq, hyf_y.three_eq]
        have hy₁_frame : Frame n edges ((((y.set w0 0).set w1 0).set eIdx 0).set ePtr 3) := by
          struct_frame hyf_y
        wram_call (edgeScanLoop_spec (w := w) (n := n) (z := z) (edges := edges) hy₁_frame hz)
          [hw] with y₂ ⟨hy₂_mem, hy₂_w0, hy₂_w1⟩
        wram_simp at hy₂_mem hy₂_w0 hy₂_w1
        change y₂.regs w0 = g0 at hy₂_w0
        change y₂.regs w1 = g1 at hy₂_w1
        have hy₂_frame : Frame n edges y₂ := by struct_frame hy₁_frame
        have ⟨hy₂_vIdx, hy₂_cut⟩ :
            y₂.regs vIdx = z ∧
            y₂.regs cutWt = cutWeight (edges.filter (belowVertex z)) side := by regs_frame
        have hfit_best : Fits w (y₂.regs cutWt + gainBest) := by
          rw [hy₂_cut, hgainBest_eq, ← hcut_next]
          exact hw.of_le (by unfold wordBound; omega)
        wram_call (chooseSideCode_spec hy₂_frame.zero_eq hy₂_frame.one_eq hy₂_w0 hy₂_w1 hfit_best)
          with y₃ ⟨hy₃_mem, hy₃_chosen, hy₃_cut⟩
        have hy₃_y : y₃.mem = y.mem := hy₃_mem.trans hy₂_mem
        change y₃.regs chosen = bChoice.toNat at hy₃_chosen
        change y₃.regs cutWt = y₂.regs cutWt + gainBest at hy₃_cut
        have hy₃_frame : Frame n edges y₃ := by struct_frame hy₂_frame
        have hy₃_vIdx : y₃.regs vIdx = z := by regs_frame
        wram_exec [hy₃_frame.sideBase_eq, hy₃_vIdx, hy₃_chosen, hy₃_frame.one_eq]
        refine ⟨⟨by struct_frame hy₃_frame, ?_, ?_, ?_⟩, by wram_simp⟩
        · intro u hu
          simp only [Data.set_mem, Data.write_mem, hy₃_y, Function.update_apply]
          split_ifs
          · exact Nat.lt_succ_iff.mp (Bool.toNat_lt _)
          · exact hyside_y u (by omega)
        · wram_simp [hy₃_cut, hy₂_cut, hgainBest_eq, ← hcut_next]
          simp only [hy₃_y]
          rfl
        · wram_simp [hy₃_cut]
          rw [hnl_next, hy₂_cut]
          dsimp only [side, g0, g1] at hnl_next h2max ⊢
          rw [hycut_y] at hynl_y
          omega)
      (by rw [hv0]; exact Nat.zero_le _) hP0
  exact ⟨y, hy.mono (by rw [hv0, Nat.sub_zero]), hyf, hyside, hycut, hynl⟩

private theorem setupCode_spec {w n : ℕ} (edges : List WeightedEdge)
    (hw : Fits w (wordBound n edges)) :
    ∃ y, ExecWithin w setupCode (Data.init (encode n edges)) y 10 ∧
      Frame n edges y ∧ y.regs vIdx = 0 ∧ y.regs cutWt = 0 := by
  let mem0 := (Data.init (encode n edges) : Data 18).mem
  have hm1 : (Data.init (encode n edges) : Data 18).mem 1 = n := rfl
  have hm2 : (Data.init (encode n edges) : Data 18).mem 2 = edges.length := rfl
  have hin : HoldsList 1 (n :: edges.length :: encodeEdges edges) mem0 :=
    (outputList_eq_iff.mp (outputList_init (encode n edges))).2
  simp only [holdsList_cons_iff] at hin
  obtain ⟨-, -, hedges⟩ := hin
  have : Fits w 0 := fits_zero w
  have : Fits w 1 := hw.of_le (by unfold wordBound; omega)
  have : Fits w 2 := hw.of_le (by unfold wordBound; omega)
  have : Fits w 3 := hw.of_le (by unfold wordBound; omega)
  have : Fits w (3 * edges.length) := hw.of_le (by unfold wordBound; omega)
  have : Fits w (3 + 3 * edges.length) := hw.of_le (by unfold wordBound; omega)
  refine WP.exists_execWithin (w := w) (c := setupCode) ?_
  unfold setupCode
  wram_exec [hm1, hm2]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩, rfl, rfl⟩
  simpa only [Data.set_mem] using hedges

/-- **Structured word-RAM specification of deterministic `1 / 2`-approximation `MaxCut`.**
When every endpoint in `edges` is below `n` and `Fits w (wordBound n edges)`, `maxCutCode` executes
within `maxCutTime n edges.length = n * (20 * edges.length + 15) + 12` instructions, writing a
boolean cut `side = sideAt y.mem (3 + 3 * edges.length) n` to `[3 + 3 * edges.length,
3 + 3 * edges.length + n)` and leaving `cutWeight edges side` in register `Reg.cutWt` with
`nonLoopWeight edges ≤ 2 * cutWeight edges side` and `cutWeight edges τ ≤ 2 * cutWeight edges side`
for every cut `τ : ℕ → Bool`. -/
theorem maxCutCode_spec {w n : ℕ} (edges : List WeightedEdge)
    (hends : ∀ e ∈ edges, e.u < n ∧ e.v < n)
    (hw : Fits w (wordBound n edges)) :
    ∃ y, ExecWithin w maxCutCode (Data.init (encode n edges)) y (maxCutTime n edges.length) ∧
      (∀ u < n, y.mem (3 + 3 * edges.length + u) ≤ 1) ∧
      y.regs cutWt = cutWeight edges (sideAt y.mem (3 + 3 * edges.length) n) ∧
      nonLoopWeight edges ≤ 2 * cutWeight edges (sideAt y.mem (3 + 3 * edges.length) n) ∧
      ∀ τ : ℕ → Bool,
        cutWeight edges τ ≤ 2 * cutWeight edges (sideAt y.mem (3 + 3 * edges.length) n) := by
  obtain ⟨y₀, hy₀, hf₀, hv₀, hc₀⟩ := setupCode_spec edges hw
  obtain ⟨y, hy, -, hyside, hycut, hynl⟩ := vertexLoop_spec edges hf₀ hv₀ hc₀ hw
  have hfilt : edges.filter (belowVertex n) = edges :=
    List.filter_eq_self.mpr fun e he => decide_eq_true (hends e he)
  rw [hfilt] at hycut hynl
  rw [hycut] at hynl
  refine ⟨y, (hy₀.seq hy).mono (by unfold maxCutTime; omega), hyside, hycut, hynl, fun τ => ?_⟩
  exact (cutWeight_le_nonLoopWeight edges τ).trans hynl

/-- **Compiled word-RAM specification of deterministic `1 / 2`-approximation `MaxCut`.**
At any word width `w` with `Fits w (wordBound n edges)`, `maxCutProgram` halts within
`maxCutTime n edges.length + 1` instructions from `State.init (encode n edges)` and outputs the
weight `cutWeight edges side` of an explicit cut `side : ℕ → Bool` achieving at least half of
`nonLoopWeight edges` and at least half of every cut `τ : ℕ → Bool`. -/
theorem maxCutProgram_spec {w n : ℕ} (edges : List WeightedEdge)
    (hends : ∀ e ∈ edges, e.u < n ∧ e.v < n)
    (hw : Fits w (wordBound n edges)) :
    ∃ (side : ℕ → Bool) (steps : ℕ),
      steps ≤ maxCutTime n edges.length + 1 ∧
      Executes w maxCutProgram (State.init (encode n edges)) (cutWeight edges side) steps ∧
      nonLoopWeight edges ≤ 2 * cutWeight edges side ∧
      ∀ τ : ℕ → Bool, cutWeight edges τ ≤ 2 * cutWeight edges side := by
  obtain ⟨y, ⟨steps, hsteps, hexec⟩, -, hycut, hynl, happrox⟩ := maxCutCode_spec edges hends hw
  refine ⟨sideAt y.mem (3 + 3 * edges.length) n, steps + 1, Nat.add_le_add_right hsteps 1, ?_,
    hynl, happrox⟩
  rw [← hycut]
  exact hexec.executes cutWt

end Cslib.Algorithms.WordRAM.MaxCut
