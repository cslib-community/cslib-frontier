/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.WordRAM.WordStack

/-!
# Flat memory records and register-top stacks

Checked instances and concrete symbolic-execution checks for `RecordSpec`, `storeRecord`,
`loadRecord`, `ram_keep` across `modifies_writeWords`, and `WordStack.push` / `WordStack.pop` on a
multi-field domain `structure` across the exported `module` boundary.
-/

public section

namespace CslibFrontierTests.WordRAMRecordStack

open Cslib.WordRAM

/-- Three-word traversal frame used across the record and stack checks. -/
structure NodeFrame where
  /-- Current vertex index. -/
  vertex : ℕ
  /-- Current recursion depth. -/
  depth : ℕ
  /-- Accumulated edge weight. -/
  weight : ℕ
  deriving DecidableEq

/-- Nonvacuous `RecordSpec` instance for `NodeFrame`. -/
def nodeFrameSpec : RecordSpec NodeFrame 3 where
  toWords f := ![f.vertex, f.depth, f.weight]

theorem nodeFrameSpec_injective : Function.Injective nodeFrameSpec.toWords := by
  intro a b h
  cases a; cases b
  simp only [NodeFrame.mk.injEq]
  exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩

example (mem : ℕ → ℕ) (u v : NodeFrame) :
    nodeFrameSpec.HoldsAt 40 u (nodeFrameSpec.write 40 v mem) ↔ u = v :=
  nodeFrameSpec.holdsAt_write_iff nodeFrameSpec_injective 40 u v mem

example (mem : ℕ → ℕ) (xs ys : List NodeFrame) (hlen : xs.length = ys.length)
    (hxs : WordStack.Holds nodeFrameSpec 100 xs mem)
    (hys : WordStack.Holds nodeFrameSpec 100 ys mem) : xs = ys :=
  hxs.unique nodeFrameSpec_injective hys hlen

example (mem : ℕ → ℕ) (f₀ f₁ : NodeFrame) :
    WordStack.Holds nodeFrameSpec 100 [f₁, f₀] mem ↔
      ∀ idx : Fin 2, nodeFrameSpec.HoldsAt (100 + idx.val * 3) ([f₁, f₀].reverse[idx.val]) mem :=
  WordStack.holds_iff_getElem_reverse nodeFrameSpec 100 [f₁, f₀] mem

example (mem mem' : ℕ → ℕ) (items : List NodeFrame)
    (h : WordStack.Holds nodeFrameSpec 100 items mem)
    (hmod : Modifies (Block.mk 0 50).footprint mem mem') :
    WordStack.Holds nodeFrameSpec 100 items mem' :=
  h.keep (Modifies.eqOn hmod (by
    rw [Set.disjoint_left]
    intro a ha hw
    rw [Finset.mem_coe, Block.mem_footprint] at hw
    simp only [Set.mem_Ico, Block.Owns] at ha hw
    omega)) Set.Subset.rfl

/-! ## `storeRecord`, `loadRecord`, and `ram_keep` -/

section RecordExec

private abbrev addrReg : Fin 8 := 0
private abbrev curReg : Fin 8 := 1
private abbrev oneReg : Fin 8 := 2
private abbrev vReg : Fin 8 := 3
private abbrev dReg : Fin 8 := 4
private abbrev wReg : Fin 8 := 5
private abbrev keepReg : Fin 8 := 6

private abbrev frameRegs : Fin 3 → Fin 8 := ![vReg, dReg, wReg]

/-- Store a `NodeFrame` at address `20` while keeping an earlier `NodeFrame` at address `10`
via `ram_keep`, then load the newly stored frame into registers in `6 + 6 = 12` exact steps. -/
example (x : Data 8) (haddr : x.regs addrReg = 20) (hone : x.regs oneReg = 1)
    (hv : x.regs vReg = 7) (hd : x.regs dReg = 2) (hw : x.regs wReg = 42)
    (hkeep : x.regs keepReg = 99)
    (hold : nodeFrameSpec.HoldsAt 10 ⟨3, 1, 15⟩ x.mem) :
    ∃ z, Exec 8
      (.seq (storeRecord addrReg curReg oneReg frameRegs)
            (loadRecord addrReg curReg oneReg frameRegs)) x z 12 ∧
      nodeFrameSpec.HoldsAt 10 ⟨3, 1, 15⟩ z.mem ∧
      nodeFrameSpec.HoldsAt 20 ⟨7, 2, 42⟩ z.mem ∧
      z.regs vReg = 7 ∧ z.regs dReg = 2 ∧ z.regs wReg = 42 ∧
      z.regs keepReg = 99 := by
  obtain ⟨y, hy, hynew, _, hymod, hyregs⟩ :=
    nodeFrameSpec.store_exec (w := 8) addrReg curReg oneReg frameRegs ⟨7, 2, 42⟩ x
      (by decide) (by decide) hone
      (fun i => by match i with | 0 => exact hv | 1 => exact hd | 2 => exact hw)
      (by rw [haddr]; decide)
  rw [haddr] at hynew hymod
  have hold_y : nodeFrameSpec.HoldsAt 10 ⟨3, 1, 15⟩ y.mem := by
    ram_keep hold using hymod
  have hy_addr : y.regs addrReg = 20 := (hyregs addrReg (by decide)).trans haddr
  have hy_one : y.regs oneReg = 1 := (hyregs oneReg (by decide)).trans hone
  obtain ⟨z, hz, hzmem, hzfields, hzregs⟩ :=
    nodeFrameSpec.load_exec (w := 8) addrReg curReg oneReg frameRegs ⟨7, 2, 42⟩ y
      (by decide) (by decide) (by decide) (by decide) hy_one
      (by rwa [hy_addr]) (by rw [hy_addr]; decide)
  refine ⟨z, hy.seq hz, hzmem ▸ hold_y, hzmem ▸ hynew,
    hzfields 0, hzfields 1, hzfields 2, ?_⟩
  exact (hzregs keepReg (by decide)).trans ((hyregs keepReg (by decide)).trans hkeep)

end RecordExec

/-! ## `WordStack.push` and `WordStack.pop` -/

section StackExec

private abbrev sBase : Fin 9 := 0
private abbrev sTop : Fin 9 := 1
private abbrev sCur : Fin 9 := 2
private abbrev sWidth : Fin 9 := 3
private abbrev sOne : Fin 9 := 4
private abbrev fV : Fin 9 := 5
private abbrev fD : Fin 9 := 6
private abbrev fW : Fin 9 := 7
private abbrev callerSaved : Fin 9 := 8

private abbrev sFields : Fin 3 → Fin 9 := ![fV, fD, fW]

/-- Push two `NodeFrame` records onto an initially empty dirty-memory `WordStack` of capacity `4`
at base `100`, then pop the top record back into `sFields` in `8 + 3 + 8 + 8 = 27` exact steps. -/
example (x : Data 9) (hb : x.regs sBase = 100) (ht : x.regs sTop = 0)
    (hw : x.regs sWidth = 3) (h1 : x.regs sOne = 1)
    (hv : x.regs fV = 11) (hd : x.regs fD = 4) (hwt : x.regs fW = 50)
    (hsaved : x.regs callerSaved = 77) :
    let pushProg := WordStack.push sBase sTop sCur sWidth sOne sFields
    let popProg := WordStack.pop sBase sTop sCur sWidth sOne sFields
    let setSecond : Code .standard 9 := ram[ fV ← #22; fD ← #5; fW ← #60 ]
    ∃ z, Exec 8 (.seq pushProg (.seq setSecond (.seq pushProg popProg))) x z 27 ∧
      z.regs sTop = 1 ∧
      WordStack.Holds nodeFrameSpec 100 [⟨11, 4, 50⟩] z.mem ∧
      z.regs fV = 22 ∧ z.regs fD = 5 ∧ z.regs fW = 60 ∧
      z.regs callerSaved = 77 ∧
      Modifies (Block.mk 100 12).footprint x.mem z.mem := by
  dsimp only
  obtain ⟨y₁, hy₁, hy₁_top, hy₁_stack, _, hy₁_mod, hy₁_regs⟩ :=
    WordStack.push_exec (w := 8) (cap := 4) nodeFrameSpec sBase sTop sCur sWidth sOne sFields
      [] ⟨11, 4, 50⟩ x
      (by decide) (by decide) (by decide) (by decide) hb ht hw h1
      (fun i => by match i with | 0 => exact hv | 1 => exact hd | 2 => exact hwt)
      trivial (by decide) (by decide)
  let y₂ := ((y₁.set fV 22).set fD 5).set fW 60
  have hset : Exec 8 (ram[ fV ← #22; fD ← #5; fW ← #60 ] : Code .standard 9) y₁ y₂ 3 := by
    ram_eval [y₂]
  obtain ⟨y₃, hy₃, hy₃_top, hy₃_stack, _, hy₃_mod, hy₃_regs⟩ :=
    WordStack.push_exec (w := 8) (cap := 4) nodeFrameSpec sBase sTop sCur sWidth sOne sFields
      [⟨11, 4, 50⟩] ⟨22, 5, 60⟩ y₂
      (by decide) (by decide) (by decide) (by decide)
      (by simp +decide [y₂, hy₁_regs sBase (by decide), hb])
      (by simp +decide [y₂, hy₁_top])
      (by simp +decide [y₂, hy₁_regs sWidth (by decide), hw])
      (by simp +decide [y₂, hy₁_regs sOne (by decide), h1])
      (fun i => by match i with | 0 => rfl | 1 => rfl | 2 => rfl)
      hy₁_stack (by decide) (by decide)
  obtain ⟨z, hz, hz_top, hz_stack, hz_fields, hz_mem, hz_regs⟩ :=
    WordStack.pop_exec (w := 8) nodeFrameSpec sBase sTop sCur sWidth sOne sFields
      [⟨11, 4, 50⟩] ⟨22, 5, 60⟩ y₃
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by simp +decide [y₂, hy₃_regs sBase (by decide), hy₁_regs sBase (by decide), hb])
      hy₃_top
      (by simp +decide [y₂, hy₃_regs sWidth (by decide), hy₁_regs sWidth (by decide), hw])
      (by simp +decide [y₂, hy₃_regs sOne (by decide), hy₁_regs sOne (by decide), h1])
      hy₃_stack (by decide)
  refine ⟨z, hy₁.seq (hset.seq (hy₃.seq hz)), hz_top, hz_stack,
    hz_fields 0, hz_fields 1, hz_fields 2, ?_, ?_⟩
  · have h3 := hz_regs callerSaved (by decide)
    have h2 := hy₃_regs callerSaved (by decide)
    have h1' := hy₁_regs callerSaved (by decide)
    simpa +decide [y₂, h3, h2, h1'] using hsaved
  · intro a ha
    rw [hz_mem]
    exact (hy₃_mod a ha).trans (hy₁_mod a ha)

end StackExec

end CslibFrontierTests.WordRAMRecordStack
