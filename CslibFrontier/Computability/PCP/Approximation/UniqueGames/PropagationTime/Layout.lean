/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.UniqueGames.PropagationTime.Model
public import CslibFrontier.Computability.WordRAM.SymbolicExec
import all CslibFrontier.Computability.PCP.Approximation.UniqueGames.Propagation
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Data.List.GetD

/-!
# Register map, memory layout, and search-state invariants for Word-RAM label propagation

This internal module defines the 34-register allocation, `@[wram_arith]` workspace base addresses,
memory invariants (`InputAt`, `ConstRegs`, `AdjChain`, `BucketsAt`, `TableStateAt`, `StateAt`),
frame/transition lemmas, and shared edge-header / row-pointer subroutines (`edgeVisLoad`,
`extendPrep`) used across the parallel symbolic-execution submodules of `PropagationTime`.

## Main definitions

* `Cslib.Complexity.UniqueGames.Propagation.headBase`,
  `Cslib.Complexity.UniqueGames.Propagation.nodeBase`,
  `Cslib.Complexity.UniqueGames.Propagation.visBase`,
  `Cslib.Complexity.UniqueGames.Propagation.tabBase`,
  `Cslib.Complexity.UniqueGames.Propagation.candBase`,
  `Cslib.Complexity.UniqueGames.Propagation.invBase`,
  `Cslib.Complexity.UniqueGames.Propagation.stackBase`,
  `Cslib.Complexity.UniqueGames.Propagation.compBase`,
  `Cslib.Complexity.UniqueGames.Propagation.outBaseAddr`: workspace region base addresses.
* `Cslib.Complexity.UniqueGames.Propagation.InputAt`,
  `Cslib.Complexity.UniqueGames.Propagation.ConstRegs`,
  `Cslib.Complexity.UniqueGames.Propagation.AdjChain`,
  `Cslib.Complexity.UniqueGames.Propagation.BucketsAt`: input, register, and incidence-list
  invariants.
* `Cslib.Complexity.UniqueGames.Propagation.statePotential`,
  `Cslib.Complexity.UniqueGames.Propagation.TableStateAt`,
  `Cslib.Complexity.UniqueGames.Propagation.StateAt`: inter-component and intra-component search
  state invariants.
* `Cslib.Complexity.UniqueGames.Propagation.edgeVisLoad`,
  `Cslib.Complexity.UniqueGames.Propagation.extendPrep`: shared Word-RAM blocks loading endpoint
  visit flags and row pointers.

## Main results

* `Cslib.Complexity.UniqueGames.Propagation.inputAt_init`: `Data.init (encode g)` satisfies
  `InputAt g` with zeroed cells from `headBase g` upward.
* `Cslib.Complexity.UniqueGames.Propagation.StateAt.push_slot`,
  `Cslib.Complexity.UniqueGames.Propagation.StateAt.frame_inv`: invariant preservation across slot
  pushes and scratch-inversion writes.
* `Cslib.Complexity.UniqueGames.Propagation.edgeVisLoad_spec`,
  `Cslib.Complexity.UniqueGames.Propagation.extendPrep_spec`: `ExecWithin` specifications for
  `edgeVisLoad` and `extendPrep`.
-/

public section

namespace Cslib.Complexity.UniqueGames.Propagation

open Cslib.PCP Cslib.PCP.Encoded Cslib.WordRAM Cslib.WordRAM.Block

/-! ## Internal registers -/

namespace Reg

/-- Constant `0` register. -/
abbrev rZero : Fin 34 := 0
/-- Constant `1` register. -/
abbrev rOne : Fin 34 := 1
/-- Constant `2` register. -/
abbrev rTwo : Fin 34 := 2
/-- Alphabet size `L`. -/
abbrev rL : Fin 34 := 3
/-- Edge record stride `L + 2`. -/
abbrev rStride : Fin 34 := 4
/-- Slot count `slots g`. -/
abbrev rN : Fin 34 := 5
/-- Edge count `g.edges.length`. -/
abbrev rE : Fin 34 := 6
/-- Base address `4` of encoded edge records. -/
abbrev rEdgeBase : Fin 34 := 7
/-- Base address of per-slot bucket head pointers. -/
abbrev rHeadBase : Fin 34 := 8
/-- Base address of linked incidence-list nodes. -/
abbrev rNodeBase : Fin 34 := 9
/-- Base address of per-slot visited flags. -/
abbrev rVisBase : Fin 34 := 10
/-- Base address of the `slots g × L` candidate-to-label table. -/
abbrev rTabBase : Fin 34 := 11
/-- Base address of the `L`-word surviving-candidate bitmask array. -/
abbrev rCandBase : Fin 34 := 12
/-- Base address of the `L`-word scratch preimage array. -/
abbrev rInvBase : Fin 34 := 13
/-- Base address of the DFS stack array. -/
abbrev rStackBase : Fin 34 := 14
/-- Base address of the current component's visited-slot array. -/
abbrev rCompBase : Fin 34 := 15
/-- Current DFS stack length. -/
abbrev rStackLen : Fin 34 := 17
/-- Current component slot list length. -/
abbrev rCompLen : Fin 34 := 18
/-- Outer loop index over edges or slots. -/
abbrev rOuterIdx : Fin 34 := 20
/-- Bump pointer into the incidence-list node pool. -/
abbrev rNodeFree : Fin 34 := 21
/-- Remaining fuel / component index counter. -/
abbrev rRem : Fin 34 := 22
/-- Chosen seed label or popped slot index. -/
abbrev rChosen : Fin 34 := 23
/-- Current linked-list node pointer during adjacency traversal. -/
abbrev rCurNode : Fin 34 := 24
/-- Current edge index or edge record address. -/
abbrev rEdgeIdx : Fin 34 := 25
/-- Source slot of the current edge. -/
abbrev rSrc : Fin 34 := 26
/-- Destination slot of the current edge. -/
abbrev rDst : Fin 34 := 27
/-- Inner loop index `0 .. L - 1` over labels. -/
abbrev rLabIdx : Fin 34 := 28
/-- Scratch register 1. -/
abbrev rTmp1 : Fin 34 := 29
/-- Scratch register 2. -/
abbrev rTmp2 : Fin 34 := 30
/-- Scratch register 3. -/
abbrev rTmp3 : Fin 34 := 31
/-- Scratch register 4. -/
abbrev rTmp4 : Fin 34 := 32
/-- Scratch register 5. -/
abbrev rTmp5 : Fin 34 := 33

end Reg

open Reg

/-! ## Memory layout addresses and bounds -/

/-- Base address of the `slots g` bucket-head pointers immediately above the input. -/
@[wram_arith] abbrev headBase {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  4 + g.edges.length * (L + 2)

/-- Base address of the `4 * |g.edges|`-word incidence-list node arena. -/
@[wram_arith] abbrev nodeBase {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  headBase g + slots g

/-- Base address of the `slots g` visited-flag cells. -/
@[wram_arith] abbrev visBase {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  nodeBase g + 4 * g.edges.length

/-- Base address of the `slots g × L` propagation tables. -/
@[wram_arith] abbrev tabBase {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  visBase g + slots g

/-- Base address of the `L` candidate indicator cells. -/
@[wram_arith] abbrev candBase {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  tabBase g + slots g * L

/-- Base address of the `L` preimage scratch cells. -/
@[wram_arith] abbrev invBase {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  candBase g + L

/-- Base address of the `slots g`-word traversal stack. -/
@[wram_arith] abbrev stackBase {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  invBase g + L

/-- Base address of the `slots g`-word settled-component buffer. -/
@[wram_arith] abbrev compBase {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  stackBase g + slots g

/-- Base address of the length-prefixed solution output buffer. -/
@[wram_arith] abbrev outBaseAddr {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  compBase g + slots g

/-- The entire workspace including the `(slots g + 2)`-word output buffer fits in `wordBound g`. -/
theorem outBaseAddr_lt_wordBound {L : ℕ} (g : Graph (Fin L → Fin L)) :
    outBaseAddr g + slots g + 2 ≤ wordBound g := by
  simp only [outBaseAddr, compBase, stackBase, invBase, candBase, tabBase, visBase, nodeBase,
    headBase, wordBound]
  nlinarith

/-- Any address up to `outBaseAddr g + slots g + 2` fits when `wordBound g` fits. -/
theorem fits_top {L w a : ℕ} {g : Graph (Fin L → Fin L)} (hw : Fits w (wordBound g))
    (ha : a ≤ outBaseAddr g + slots g + 2) : Fits w a :=
  hw.of_le (ha.trans (outBaseAddr_lt_wordBound g))

/-- Every encoded edge record lies below `headBase g`. -/
theorem edge_end_le_headBase {L j : ℕ} {g : Graph (Fin L → Fin L)}
    (hj : j < g.edges.length) : 4 + j * (L + 2) + (L + 2) ≤ headBase g := by
  have : j * (L + 2) + (L + 2) ≤ g.edges.length * (L + 2) := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right (L + 2) hj
  simp only [headBase]
  omega

/-- Every encoded edge record fits within `wordBound g`. -/
theorem edge_end_le_wordBound {L j : ℕ} {g : Graph (Fin L → Fin L)}
    (hj : j < g.edges.length) : 4 + j * (L + 2) + (L + 2) ≤ wordBound g :=
  (edge_end_le_headBase hj).trans (by wram_omega : headBase g ≤ outBaseAddr g + slots g + 2)
    |>.trans (outBaseAddr_lt_wordBound g)

/-- Basic linear bound relating `|g.edges|`, `slots g`, and `L` to `wordBound g`. -/
theorem edges_lt_wordBound {L : ℕ} (g : Graph (Fin L → Fin L)) :
    g.edges.length + slots g + L + 4 ≤ wordBound g := by
  simp only [wordBound]
  nlinarith

/-- Self-copy instruction `r ← r` executes in 1 step as a no-op. -/
theorem exec_nop {w : ℕ} (r : Fin 34) (x : Data 34) :
    Exec (B := .standard) w (.op (.copy r r)) x x 1 := by
  have h : x.set r (x.regs r) = x := by cases x; simp only [Data.set, Function.update_eq_self]
  simpa only [h] using
    (Exec.copy : Exec (B := .standard) w (.op (.copy r r)) x (x.regs r |> x.set r) 1)

/-- Distinct slots `u ≠ w` occupy disjoint `L`-word rows in `tabBase g`. -/
theorem not_in_tabRow {L u w a : ℕ} {g : Graph (Fin L → Fin L)}
    (huw : u ≠ w) (ha : a < L) :
    ¬ (tabBase g + w * L ≤ tabBase g + u * L + a ∧
        tabBase g + u * L + a < tabBase g + w * L + L) := by
  rcases Nat.lt_or_gt_of_ne huw with h | h
  all_goals
    have := Nat.mul_le_mul_right L h
    rw [Nat.succ_mul] at this
    omega

/-- Every valid slot row `w < slots g` ends at or below `candBase g`. -/
theorem tabRow_hi_le_candBase {L w : ℕ} {g : Graph (Fin L → Fin L)} (hw : w < slots g) :
    tabBase g + w * L + L ≤ candBase g := by
  have : w * L + L ≤ slots g * L := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right L hw
  simp only [candBase]
  omega

/-! ## Input, constant-register, and incidence-list invariants -/

/-- Input memory cells `0 .. 3 + E * (L + 2)` hold the header and edge records of `g`. -/
structure InputAt {L : ℕ} (g : Graph (Fin L → Fin L)) (mem : ℕ → ℕ) : Prop where
  /-- Length cell at address `0`. -/
  mem0 : mem 0 = 3 + g.edges.length * (L + 2)
  /-- Alphabet size `L` at address `1`. -/
  mem1 : mem 1 = L
  /-- Declared vertex count `g.vertices` at address `2`. -/
  mem2 : mem 2 = g.vertices
  /-- Edge count `g.edges.length` at address `3`. -/
  mem3 : mem 3 = g.edges.length
  /-- Source endpoint of edge `j`. -/
  edge_src : ∀ j (hj : j < g.edges.length), mem (4 + j * (L + 2)) = g.edges[j].src
  /-- Destination endpoint of edge `j`. -/
  edge_dst : ∀ j (hj : j < g.edges.length), mem (4 + j * (L + 2) + 1) = g.edges[j].dst
  /-- Constraint entry `a` of edge `j`. -/
  edge_val : ∀ j (hj : j < g.edges.length) a (ha : a < L),
    mem (4 + j * (L + 2) + 2 + a) = (g.edges[j].constraint ⟨a, ha⟩).val

/-- `InputAt g` depends only on addresses below `headBase g`. -/
theorem InputAt.frame {L : ℕ} {g : Graph (Fin L → Fin L)} {mem mem' : ℕ → ℕ}
    (h : InputAt g mem) (heq : ∀ a < headBase g, mem' a = mem a) : InputAt g mem' where
  mem0 := (heq 0 (by simp only [headBase]; omega)).trans h.mem0
  mem1 := (heq 1 (by simp only [headBase]; omega)).trans h.mem1
  mem2 := (heq 2 (by simp only [headBase]; omega)).trans h.mem2
  mem3 := (heq 3 (by simp only [headBase]; omega)).trans h.mem3
  edge_src j hj := (heq _ (by have := edge_end_le_headBase hj; omega)).trans (h.edge_src j hj)
  edge_dst j hj := (heq _ (by have := edge_end_le_headBase hj; omega)).trans (h.edge_dst j hj)
  edge_val j hj a ha :=
    (heq _ (by have := edge_end_le_headBase hj; omega)).trans (h.edge_val j hj a ha)

/-- Initial Word-RAM state `Data.init (encode g)` satisfies `InputAt g` and is `0` at
`≥ headBase g`. -/
theorem inputAt_init {L : ℕ} (g : Graph (Fin L → Fin L)) :
    InputAt g (Data.init (encode g) : Data 34).mem ∧
      ∀ a, headBase g ≤ a → (Data.init (encode g) : Data 34).mem a = 0 := by
  have hedge (j) (hj : j < g.edges.length) (r) (hr : r < L + 2) :
      (Data.init (encode g) : Data 34).mem (4 + j * (L + 2) + r) =
        (encodeEdge g.edges[j])[r]'(by simp only [length_encodeEdge]; exact hr) := by
    rw [show 4 + j * (L + 2) + r = (3 + (j * (L + 2) + r)) + 1 by omega, Data.init_mem_succ]
    simp only [encode, List.getD_eq_getElem?_getD]
    change ([L, g.vertices, g.edges.length] ++ g.edges.flatMap encodeEdge)[
      3 + (j * (L + 2) + r)]?.getD 0 = _
    rw [List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
    simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel_left]
    rw [List.getElem?_flatMap_mul_add g.edges encodeEdge (L + 2)
      (fun _ _ => length_encodeEdge _) hj hr,
      List.getElem?_eq_getElem (by simp only [length_encodeEdge]; exact hr)]
    rfl
  refine ⟨⟨by rw [Data.init_mem_zero, length_encode],
    by rw [Data.init_mem_succ]
       simp only [encode, List.getD_cons_zero],
    by rw [show (2 : ℕ) = 1 + 1 from rfl, Data.init_mem_succ]
       simp only [encode, List.getD_cons_succ, List.getD_cons_zero],
    by rw [show (3 : ℕ) = 2 + 1 from rfl, Data.init_mem_succ]
       simp only [encode, List.getD_cons_succ, List.getD_cons_zero],
    fun j hj => by
      simpa only [encodeEdge, List.getElem_cons_zero, Nat.add_zero] using hedge j hj 0 (by omega),
    fun j hj => by
      simpa only [encodeEdge, List.getElem_cons_succ, List.getElem_cons_zero] using
        hedge j hj 1 (by omega),
    fun j hj a ha => ?_⟩, fun a ha => ?_⟩
  · have h := hedge j hj (a + 2) (by omega)
    rw [show 4 + j * (L + 2) + (a + 2) = 4 + j * (L + 2) + 2 + a by omega] at h
    simpa only [encodeEdge, List.getElem_cons_succ, List.getElem_map, List.getElem_finRange,
      Fin.cast_mk] using h
  · rw [show a = (a - 1) + 1 by simp only [headBase] at ha; omega, Data.init_mem_succ]
    exact List.getD_eq_default _ _ (by rw [length_encode]; simp only [headBase] at ha; omega)

/-- Fixed layout registers `0 .. 16` established after `layoutSetupCode`. -/
structure ConstRegs {L : ℕ} (g : Graph (Fin L → Fin L)) (x : Data 34) : Prop where
  /-- `rZero = 0`. -/
  zero : x.regs rZero = 0
  /-- `rOne = 1`. -/
  one : x.regs rOne = 1
  /-- `rTwo = 2`. -/
  two : x.regs rTwo = 2
  /-- `rL = L`. -/
  regL : x.regs rL = L
  /-- `rStride = L + 2`. -/
  stride : x.regs rStride = L + 2
  /-- `rN = slots g`. -/
  regN : x.regs rN = slots g
  /-- `rE = g.edges.length`. -/
  regE : x.regs rE = g.edges.length
  /-- `rEdgeBase = 4`. -/
  edgeB : x.regs rEdgeBase = 4
  /-- `rHeadBase = headBase g`. -/
  headB : x.regs rHeadBase = headBase g
  /-- `rNodeBase = nodeBase g`. -/
  nodeB : x.regs rNodeBase = nodeBase g
  /-- `rVisBase = visBase g`. -/
  visB : x.regs rVisBase = visBase g
  /-- `rTabBase = tabBase g`. -/
  tabB : x.regs rTabBase = tabBase g
  /-- `rCandBase = candBase g`. -/
  candB : x.regs rCandBase = candBase g
  /-- `rInvBase = invBase g`. -/
  invB : x.regs rInvBase = invBase g
  /-- `rStackBase = stackBase g`. -/
  stackB : x.regs rStackBase = stackBase g
  /-- `rCompBase = compBase g`. -/
  compB : x.regs rCompBase = compBase g
  /-- `outBase = outBaseAddr g`. -/
  outB : x.regs outBase = outBaseAddr g

/-- Memory writes preserve `ConstRegs`. -/
@[wram_simps] theorem ConstRegs.write_iff {L : ℕ} {g : Graph (Fin L → Fin L)}
    (x : Data 34) (a v : ℕ) : ConstRegs g (x.write a v) ↔ ConstRegs g x := by
  simp only [Data.write]
  exact ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14,
      h.15, h.16, h.17⟩,
    fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14,
      h.15, h.16, h.17⟩⟩

/-- Updating any scratch/mutable register `17 ≤ r.val` preserves `ConstRegs`. -/
@[wram_simps] theorem ConstRegs.set_iff {L : ℕ} {g : Graph (Fin L → Fin L)}
    (x : Data 34) {r : Fin 34} (v : ℕ) (hr : 17 ≤ r.val) :
    ConstRegs g (x.set r v) ↔ ConstRegs g x := by
  have ne (i : Fin 34) (hi : i.val < 17) : i ≠ r := fun h => by rw [h] at hi; omega
  constructor <;> intro h <;> exact
    { zero := by simpa only [Data.set_regs_of_ne (ne rZero (by decide))] using h.zero
      one := by simpa only [Data.set_regs_of_ne (ne rOne (by decide))] using h.one
      two := by simpa only [Data.set_regs_of_ne (ne rTwo (by decide))] using h.two
      regL := by simpa only [Data.set_regs_of_ne (ne rL (by decide))] using h.regL
      stride := by simpa only [Data.set_regs_of_ne (ne rStride (by decide))] using h.stride
      regN := by simpa only [Data.set_regs_of_ne (ne rN (by decide))] using h.regN
      regE := by simpa only [Data.set_regs_of_ne (ne rE (by decide))] using h.regE
      edgeB := by simpa only [Data.set_regs_of_ne (ne rEdgeBase (by decide))] using h.edgeB
      headB := by simpa only [Data.set_regs_of_ne (ne rHeadBase (by decide))] using h.headB
      nodeB := by simpa only [Data.set_regs_of_ne (ne rNodeBase (by decide))] using h.nodeB
      visB := by simpa only [Data.set_regs_of_ne (ne rVisBase (by decide))] using h.visB
      tabB := by simpa only [Data.set_regs_of_ne (ne rTabBase (by decide))] using h.tabB
      candB := by simpa only [Data.set_regs_of_ne (ne rCandBase (by decide))] using h.candB
      invB := by simpa only [Data.set_regs_of_ne (ne rInvBase (by decide))] using h.invB
      stackB := by simpa only [Data.set_regs_of_ne (ne rStackBase (by decide))] using h.stackB
      compB := by simpa only [Data.set_regs_of_ne (ne rCompBase (by decide))] using h.compB
      outB := by simpa only [Data.set_regs_of_ne (ne outBase (by decide))] using h.outB }

/-- Preserved Phase 3 state registers `17 .. 27` (`rStackLen`, `rCompLen`, `rOuterIdx`,
`rCurNode`, `rRem`, `rEdgeIdx`, `rSrc`, `rDst`) across scratch operations. -/
structure Phase3Regs (x y : Data 34) : Prop where
  /-- `rEdgeIdx` is preserved. -/
  edgeIdx : y.regs rEdgeIdx = x.regs rEdgeIdx
  /-- `rSrc` is preserved. -/
  src : y.regs rSrc = x.regs rSrc
  /-- `rDst` is preserved. -/
  dst : y.regs rDst = x.regs rDst
  /-- `rStackLen` is preserved. -/
  stackLen : y.regs rStackLen = x.regs rStackLen
  /-- `rCompLen` is preserved. -/
  compLen : y.regs rCompLen = x.regs rCompLen
  /-- `rCurNode` is preserved. -/
  curNode : y.regs rCurNode = x.regs rCurNode
  /-- `rRem` is preserved. -/
  rem : y.regs rRem = x.regs rRem
  /-- `rOuterIdx` is preserved. -/
  outerIdx : y.regs rOuterIdx = x.regs rOuterIdx

/-- Reflexivity of `Phase3Regs`. -/
theorem Phase3Regs.refl (x : Data 34) : Phase3Regs x x :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Transitivity of `Phase3Regs`. -/
theorem Phase3Regs.trans {x y z : Data 34}
    (h2 : Phase3Regs y z) (h1 : Phase3Regs x y) : Phase3Regs x z :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2, h2.3.trans h1.3, h2.4.trans h1.4,
    h2.5.trans h1.5, h2.6.trans h1.6, h2.7.trans h1.7, h2.8.trans h1.8⟩

/-- Memory writes preserve `Phase3Regs`. -/
@[wram_simps] theorem Phase3Regs.write_iff (x y : Data 34) (a v : ℕ) :
    Phase3Regs x (y.write a v) ↔ Phase3Regs x y := by
  simp only [Data.write]
  exact ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8⟩,
    fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8⟩⟩

/-- Updating registers outside `17 .. 27` preserves `Phase3Regs`. -/
@[wram_simps] theorem Phase3Regs.set_iff (x y : Data 34) {r : Fin 34} (v : ℕ)
    (hr : r.val ≤ 16 ∨ 28 ≤ r.val) :
    Phase3Regs x (y.set r v) ↔ Phase3Regs x y := by
  have ne (i : Fin 34) (hi : 17 ≤ i.val ∧ i.val ≤ 27) : i ≠ r := fun h => by
    rw [h] at hi; omega
  constructor <;> intro h <;> exact
    { edgeIdx := by simpa only [Data.set_regs_of_ne (ne rEdgeIdx (by decide))] using h.edgeIdx
      src := by simpa only [Data.set_regs_of_ne (ne rSrc (by decide))] using h.src
      dst := by simpa only [Data.set_regs_of_ne (ne rDst (by decide))] using h.dst
      stackLen := by simpa only [Data.set_regs_of_ne (ne rStackLen (by decide))] using h.stackLen
      compLen := by simpa only [Data.set_regs_of_ne (ne rCompLen (by decide))] using h.compLen
      curNode := by simpa only [Data.set_regs_of_ne (ne rCurNode (by decide))] using h.curNode
      rem := by simpa only [Data.set_regs_of_ne (ne rRem (by decide))] using h.rem
      outerIdx := by simpa only [Data.set_regs_of_ne (ne rOuterIdx (by decide))] using h.outerIdx }

/-- Null-terminated linked list in `[nodeBase g, top)` representing a list of edges of `g`. -/
inductive AdjChain {L : ℕ} (g : Graph (Fin L → Fin L)) (mem : ℕ → ℕ) (top : ℕ) :
    ℕ → List (Edge (Fin L → Fin L)) → Prop where
  /-- Null pointer `0` represents the empty incidence list. -/
  | nil : AdjChain g mem top 0 []
  /-- Two-word cell `[j, next]` at `p ∈ [nodeBase g, top - 2]` prepends `g.edges[j]`. -/
  | cons {p j : ℕ} {es : List (Edge (Fin L → Fin L))} (hj : j < g.edges.length)
      (hp_lo : nodeBase g ≤ p) (hp_hi : p + 2 ≤ top) (hp0 : mem p = j)
      (htl : AdjChain g mem top (mem (p + 1)) es) :
      AdjChain g mem top p (g.edges[j] :: es)

/-- `AdjChain` is preserved under growing `top` and framing `[nodeBase g, top)`. -/
theorem AdjChain.frame {L : ℕ} {g : Graph (Fin L → Fin L)} {mem mem' : ℕ → ℕ}
    {top top' p : ℕ} {es : List (Edge (Fin L → Fin L))} (h : AdjChain g mem top p es)
    (htop : top ≤ top') (heq : ∀ a, nodeBase g ≤ a → a < top → mem' a = mem a) :
    AdjChain g mem' top' p es := by
  induction h with
  | nil => exact .nil
  | @cons p j es hj hlo hhi hp0 _ ih =>
    have hm0 : mem' p = j := by rw [heq p hlo (by omega)]; exact hp0
    have hm1 : mem' (p + 1) = mem (p + 1) := heq (p + 1) (by omega) (by omega)
    exact .cons hj hlo (by omega) hm0 (hm1 ▸ ih)

/-- Invariant that `[headBase g, visBase g)` realizes `adj g u` for every `u < slots g`. -/
@[expose] def BucketsAt {L : ℕ} (g : Graph (Fin L → Fin L)) (mem : ℕ → ℕ) : Prop :=
  ∀ u < slots g, AdjChain g mem (visBase g) (mem (headBase g + u)) (adj g u)

/-- `BucketsAt g` depends only on addresses below `visBase g`. -/
theorem BucketsAt.frame {L : ℕ} {g : Graph (Fin L → Fin L)} {mem mem' : ℕ → ℕ}
    (h : BucketsAt g mem) (heq : ∀ a < visBase g, mem' a = mem a) : BucketsAt g mem' := by
  intro u hu
  have hhd : mem' (headBase g + u) = mem (headBase g + u) :=
    heq _ (by simp only [visBase, nodeBase]; omega)
  rw [hhd]
  exact (h u hu).frame le_rfl fun a _ ha => heq a ha

/-! ## Component search-state invariants and shared subroutines -/

/-- Unvisited-plus-stack potential matching `State.potential` via public `State` projections. -/
@[expose] def statePotential {α : Type} (S : State α) : ℕ :=
  ((Finset.range S.table.length).filter fun v => (S.get v).isNone).card + S.stack.length

/-- Memory and constant-register invariant between connected components. -/
structure TableStateAt {L : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L))
    (x : Data 34) : Prop where
  /-- Layout registers `0 .. 16` hold their fixed values. -/
  consts : ConstRegs g x
  /-- Input encoding region `[0, headBase g)` holds `g`. -/
  inp : InputAt g x.mem
  /-- Bucket heads and node arena `[headBase g, visBase g)` realize `adj g`. -/
  bkt : BucketsAt g x.mem
  /-- `S.table` has length `slots g`. -/
  len_table : S.table.length = slots g
  /-- Unvisited slots have `vis = 0`. -/
  vis_none : ∀ v < slots g, S.get v = none → x.mem (visBase g + v) = 0
  /-- Visited slots have `vis = 1` and row `v` of `tabBase g` storing `f`. -/
  vis_some : ∀ v < slots g, ∀ f, S.get v = some f →
    x.mem (visBase g + v) = 1 ∧
      ∀ a (ha : a < L), x.mem (tabBase g + v * L + a) = (f ⟨a, ha⟩).val

/-- Full search-state invariant inside one connected component's exploration. -/
structure StateAt {L : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L))
    (x : Data 34) : Prop extends TableStateAt g S x where
  /-- Search potential never exceeds `slots g`. -/
  pot_le : statePotential S ≤ slots g
  /-- Candidate bitmask cells match `S.cand`. -/
  cand_mem : ∀ a (ha : a < L), x.mem (candBase g + a) = (S.cand ⟨a, ha⟩).toNat
  /-- `rStackLen` tracks `S.stack.length`. -/
  stack_len : x.regs rStackLen = S.stack.length
  /-- Every slot on `S.stack` is `< slots g`. -/
  stack_lt : ∀ u ∈ S.stack, u < slots g
  /-- `stackBase g` holds `S.stack.reverse`. -/
  stack_mem : HoldsList (stackBase g) S.stack.reverse x.mem
  /-- `rCompLen` tracks `S.comp.length`. -/
  comp_len : x.regs rCompLen = S.comp.length
  /-- `S.comp.length` never exceeds `slots g`. -/
  comp_le : S.comp.length ≤ slots g
  /-- Every slot in `S.comp` is `< slots g`. -/
  comp_lt : ∀ u ∈ S.comp, u < slots g
  /-- `compBase g` holds `S.comp.reverse`. -/
  comp_mem : HoldsList (compBase g) S.comp.reverse x.mem

/-- Transport `TableStateAt` across memory writes outside `[0, tabBase g + slots g * L)`. -/
theorem TableStateAt.frame {L : ℕ} {g : Graph (Fin L → Fin L)} {S S' : State (Fin L)}
    {x y : Data 34} (h : TableStateAt g S x) (hc : ConstRegs g y) (htab : S'.table = S.table)
    (bound : ℕ) (hb : tabBase g + slots g * L ≤ bound) (hfr : ∀ a < bound, y.mem a = x.mem a) :
    TableStateAt g S' y := by
  refine ⟨hc, h.inp.frame (fun a ha => hfr a (by wram_omega)),
    h.bkt.frame (fun a ha => hfr a (by wram_omega)), htab ▸ h.len_table,
    fun v hv hvn => by
      change S'.table.getD v none = none at hvn
      rw [htab] at hvn
      rw [hfr _ (by wram_omega)]; exact h.vis_none v hv hvn,
    fun v hv fn hvf => ?_⟩
  change S'.table.getD v none = some fn at hvf
  rw [htab] at hvf
  obtain ⟨hv1, hvtab⟩ := h.vis_some v hv fn hvf
  have hv_cb := tabRow_hi_le_candBase (g := g) hv
  exact ⟨by rw [hfr _ (by wram_omega)]; exact hv1,
    fun a ha => by rw [hfr _ (by wram_omega)]; exact hvtab a ha⟩

/-- Transport `TableStateAt` across register updates that leave memory unchanged. -/
theorem TableStateAt.of_eq {L : ℕ} {g : Graph (Fin L → Fin L)} {S : State (Fin L)}
    {x y : Data 34} (h : TableStateAt g S x) (hc : ConstRegs g y) (hm : y.mem = x.mem) :
    TableStateAt g S y :=
  h.frame hc rfl (tabBase g + slots g * L) le_rfl fun _ _ => congrFun hm _

/-- Transport `StateAt` across scratch-register updates that preserve `rStackLen`, `rCompLen`,
and memory. -/
theorem StateAt.of_eq {L : ℕ} {g : Graph (Fin L → Fin L)} {S : State (Fin L)}
    {x y : Data 34} (h : StateAt g S x) (hc : ConstRegs g y)
    (hsl : y.regs rStackLen = S.stack.length) (hcl : y.regs rCompLen = S.comp.length)
    (hm : y.mem = x.mem) : StateAt g S y :=
  ⟨h.toTableStateAt.of_eq hc hm, h.pot_le, fun a ha => hm ▸ h.cand_mem a ha,
    hsl, h.stack_lt, hm ▸ h.stack_mem, hcl, h.comp_le, h.comp_lt, hm ▸ h.comp_mem⟩

/-- Modifications confined to `[invBase g, invBase g + L)` preserve `StateAt`. -/
theorem StateAt.frame_inv {L : ℕ} {g : Graph (Fin L → Fin L)} {S : State (Fin L)}
    {x y : Data 34} (hS : StateAt g S x) (hc : ConstRegs g y)
    (hsl : y.regs rStackLen = S.stack.length) (hcl : y.regs rCompLen = S.comp.length)
    (hfr : ∀ a, ¬ (invBase g ≤ a ∧ a < invBase g + L) → y.mem a = x.mem a) :
    StateAt g S y :=
  ⟨hS.toTableStateAt.frame hc rfl (invBase g) (by wram_omega) (fun a ha => hfr a (by omega)),
    hS.pot_le,
    fun a ha => by rw [hfr _ (by wram_omega)]; exact hS.cand_mem a ha,
    hsl, hS.stack_lt,
    hS.stack_mem.frame (fun a _ _ => hfr _ (by wram_omega)),
    hcl, hS.comp_le, hS.comp_lt,
    hS.comp_mem.frame (fun a _ _ => hfr _ (by wram_omega))⟩

/-- Establish `StateAt g (push S u f) y` after writing row `u`, setting `vis[u] := 1`, and
pushing `u` onto the stack array. -/
theorem StateAt.push_slot {L : ℕ} {g : Graph (Fin L → Fin L)} {S : State (Fin L)}
    {x y : Data 34} {u : ℕ} {f : Fin L → Fin L}
    (hS : StateAt g S x) (hc : ConstRegs g y) (hu : u < slots g) (hnone : S.get u = none)
    (hrow : ∀ a (ha : a < L), y.mem (tabBase g + u * L + a) = (f ⟨a, ha⟩).val)
    (hvis : y.mem (visBase g + u) = 1)
    (hstk_mem : HoldsList (stackBase g) (S.stack.reverse ++ [u]) y.mem)
    (hstk_len : y.regs rStackLen = S.stack.length + 1)
    (hcmp_len : y.regs rCompLen = S.comp.length)
    (hframe : ∀ a,
      ¬ (tabBase g + u * L ≤ a ∧ a < tabBase g + u * L + L) →
      a ≠ visBase g + u → a ≠ stackBase g + S.stack.length → y.mem a = x.mem a) :
    StateAt g (push S u f) y := by
  have hcb := tabRow_hi_le_candBase (g := g) hu
  have hstk_le : S.stack.length < slots g := by
    have hpos : 0 < S.unvisited.card :=
      Finset.card_pos.mpr ⟨u, mem_unvisited (hS.len_table ▸ hu) hnone⟩
    have hpot : S.potential ≤ slots g := hS.pot_le
    unfold State.potential at hpot
    omega
  have hfr_low : ∀ a < visBase g, y.mem a = x.mem a := fun a ha =>
    hframe a (by wram_omega) (by omega) (by wram_omega)
  refine ⟨⟨hc, hS.inp.frame (fun a ha => hfr_low a (by wram_omega)),
      hS.bkt.frame hfr_low, length_push S u f ▸ hS.len_table, fun v hv hvn => ?_,
      fun v hv fn hvf => ?_⟩,
    (step_push (hS.len_table ▸ hu) hnone f).potential_le.trans hS.pot_le,
    fun a ha => ?_, by simpa only [push, List.length_cons] using hstk_len,
    fun v hv => (List.mem_cons.mp hv).elim (fun h => h ▸ hu) (hS.stack_lt v),
    by simpa only [push, List.reverse_cons] using hstk_mem, hcmp_len, hS.comp_le, hS.comp_lt,
    hS.comp_mem.frame fun a _ ha2 => by
      have hcl := hS.comp_le
      rw [List.length_reverse] at ha2
      exact hframe a
        (by wram_omega)
        (by wram_omega)
        (by wram_omega)⟩
  · have hne : u ≠ v := by
      rintro rfl
      rw [get_push_self (hS.len_table ▸ hu)] at hvn
      nomatch hvn
    rw [get_push_ne S hne] at hvn
    exact (hframe _
      (by wram_omega)
      (by omega)
      (by wram_omega)).trans (hS.vis_none v hv hvn)
  · by_cases huv : u = v
    · subst huv
      rw [get_push_self (hS.len_table ▸ hu)] at hvf
      cases hvf
      exact ⟨hvis, hrow⟩
    · rw [get_push_ne S huv] at hvf
      obtain ⟨hv1, hvtab⟩ := hS.vis_some v hv fn hvf
      refine ⟨(hframe _
          (by wram_omega)
          (by omega)
          (by wram_omega)).trans hv1, fun a ha => ?_⟩
      have := tabRow_hi_le_candBase (g := g) hv
      exact (hframe _ (not_in_tabRow (Ne.symm huv) ha)
        (by wram_omega)
        (by wram_omega)).trans (hvtab a ha)
  · exact (hframe _ (by omega)
      (by wram_omega)
      (by wram_omega)).trans (hS.cand_mem a ha)

/-- Load visited flags `vis[rSrc]` and `vis[rDst]` into `rTmp1` and `rTmp2`. -/
def edgeVisLoad : Code .standard 34 := ram[
  rTmp1 ← rVisBase + rSrc;
  rTmp1 ← *rTmp1;
  rTmp2 ← rVisBase + rDst;
  rTmp2 ← *rTmp2 ]

/-- Set `rTmp2 := tabBase + fromReg * L`, `rTmp3 := tabBase + toReg * L`, and `rLabIdx := 0`. -/
def extendPrep (fromReg toReg : Fin 34) : Code .standard 34 := ram[
  rTmp2 ← fromReg * rL;
  rTmp2 ← rTabBase + rTmp2;
  rTmp3 ← toReg * rL;
  rTmp3 ← rTabBase + rTmp3;
  rLabIdx ← rZero ]

/-- Specification for `edgeVisLoad`. -/
theorem edgeVisLoad_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L))
    (x : Data 34) (j : ℕ) (hj : j < g.edges.length)
    (hS : StateAt g S x)
    (hsrc_reg : x.regs rSrc = g.edges[j].src)
    (hdst_reg : x.regs rDst = g.edges[j].dst)
    (hw : Fits w (wordBound g)) :
    ∃ x1, ExecWithin w edgeVisLoad x x1 4 ∧ ConstRegs g x1 ∧
      x1.regs rTmp1 = x.mem (visBase g + g.edges[j].src) ∧
      x1.regs rTmp2 = x.mem (visBase g + g.edges[j].dst) ∧
      Phase3Regs x x1 ∧ x1.mem = x.mem := by
  have hs_lt : g.edges[j].src < slots g := src_lt_slots (List.getElem_mem hj)
  have hd_lt : g.edges[j].dst < slots g := dst_lt_slots (List.getElem_mem hj)
  have : Fits w (visBase g + g.edges[j].src) := fits_top hw (by wram_omega)
  have : Fits w (visBase g + g.edges[j].dst) := fits_top hw (by wram_omega)
  wram_exec [edgeVisLoad, hS.consts.visB, hsrc_reg, hdst_reg]
  exact ⟨by wram_simp [hS.consts], by wram_simp, by wram_simp,
    by wram_simp [Phase3Regs.refl], by wram_simp⟩

/-- Specification for `extendPrep`. -/
theorem extendPrep_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (fromReg toReg : Fin 34)
    (x1 : Data 34) (u v : ℕ)
    (hregs : (fromReg = rSrc ∧ toReg = rDst) ∨ (fromReg = rDst ∧ toReg = rSrc))
    (hc1 : ConstRegs g x1) (hu : u < slots g) (hv : v < slots g)
    (hfrom : x1.regs fromReg = u) (hto : x1.regs toReg = v)
    (hw : Fits w (wordBound g)) :
    ∃ x2, ExecWithin w (extendPrep fromReg toReg) x1 x2 5 ∧ ConstRegs g x2 ∧
      x2.regs rTmp2 = tabBase g + u * L ∧ x2.regs rTmp3 = tabBase g + v * L ∧
      x2.regs rLabIdx = 0 ∧ Phase3Regs x1 x2 ∧ x2.mem = x1.mem := by
  have hcb_u := tabRow_hi_le_candBase (g := g) hu
  have hcb_v := tabRow_hi_le_candBase (g := g) hv
  have : Fits w (u * L) := fits_top hw (by wram_omega)
  have : Fits w (v * L) := fits_top hw (by wram_omega)
  have : Fits w (tabBase g + u * L) := fits_top hw (by wram_omega)
  have : Fits w (tabBase g + v * L) := fits_top hw (by wram_omega)
  rcases hregs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · wram_exec [extendPrep, hc1.zero, hc1.regL, hc1.tabB, hfrom, hto]
    exact ⟨by wram_simp [hc1], by wram_simp, by wram_simp, by wram_simp,
      by wram_simp [Phase3Regs.refl], by wram_simp⟩

end Cslib.Complexity.UniqueGames.Propagation
