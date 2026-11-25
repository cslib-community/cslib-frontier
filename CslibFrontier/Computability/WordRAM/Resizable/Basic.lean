/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.BoundedExec
public import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import CslibFrontier.Tactic.WramOmega

/-!
# Resizable Word RAM machine model

This module formalizes the word-granular **Resizable Word RAM** machine model (`RData`, `RInstr`,
`RProgram`, `RCode`, and `RDemonicExec`), grounding the resizable word-prefix memory model of
[LiLiangYuZhou2023Succincter], [LiLiangYuZhou2024], and [KuszmaulLiangZhou2026] directly on
`Cslib.WordRAM` instructions.

A machine configuration `RData r` holds `r` registers (`regs : Fin r → ℕ`), word-addressed memory
(`mem : ℕ → ℕ`), and the `0`-indexed active word frontier (`frontier : ℕ`, `[0, frontier)`):

1. **Bounds-checked access (`evalResizable`)**: `Op.load d a` and `Op.store a s` require
   `x.regs a < x.frontier`, faulting (`none`) otherwise.
2. **Single-word resizing primitives (`RInstr.grow`, `RInstr.shrink`)**: `grow dst` extends
   `[0, frontier)` by `1` word to `[0, frontier + 1)` when `Fits w (frontier + 1)`, stores old
   `frontier` in `dst`, and initializes cell `frontier` demonically (`DemonicGrow w frontier 1`,
   matching [KuszmaulLiangZhou2026], Section 5.1, PDF pp. 16–17 / printed pp. 15–16 and
   Footnote 10, PDF p. 18 / printed p. 17); `shrink` contracts `[0, frontier)` by `1` word when
   `1 ≤ frontier` and zeroes cell `frontier - 1`. Multi-word resizing (`growDirtyCode`,
   `growZeroCode`, `shrinkCode`) is provided as derived `RCode` subroutines costing `Θ(k + 1)`
   instructions.
3. **Direct `realize` bridge (`RDemonicExec.of_execBounded`, `RDemonicExec.of_realizesBounded`)**:
   any `ExecBounded w L c x.toData y T` with `L ≤ x.frontier` lifts directly to `RDemonicExec`.

## Main definitions

* `Cslib.WordRAM.Resizable.RData`, `Cslib.WordRAM.Resizable.RData.Bounded`: resizable machine data
  and its word/frontier boundedness invariant.
* `Cslib.WordRAM.Resizable.DemonicGrow`, `Cslib.WordRAM.Resizable.evalResizable`: demonic growth
  relation and bounds-checked data instruction evaluation.
* `Cslib.WordRAM.Resizable.RInstr`, `Cslib.WordRAM.Resizable.RProgram`,
  `Cslib.WordRAM.Resizable.RState`, `Cslib.WordRAM.Resizable.RCfg`,
  `Cslib.WordRAM.Resizable.RCode`: flat and structured Resizable Word RAM programs and states.
* `Cslib.WordRAM.Resizable.RDemonicExec`: big-step demonic execution tracking steps `T` and peak
  hardware word frontier `L_peak`.
* `Cslib.WordRAM.Resizable.growDirtyCode`, `Cslib.WordRAM.Resizable.growZeroCode`,
  `Cslib.WordRAM.Resizable.shrinkCode`: derived exact-basis (`Basis.exact`) `RCode` subroutines for
  `Θ(k + 1)`-step demonic growth, zero-initialized growth, and multi-word shrinking.

## Main results

* `Cslib.WordRAM.Resizable.clear_demonicGrow_eq`: clearing `[frontier, frontier + k)` after
  `DemonicGrow` recovers canonical zero-extended memory.
* `Cslib.WordRAM.Resizable.RDemonicExec.of_execBounded`,
  `Cslib.WordRAM.Resizable.RDemonicExec.of_realizesBounded`,
  `Cslib.WordRAM.Resizable.RDemonicExec.mapSimulates`: lifting `ExecBounded`/`RealizesBounded`
  programs and transporting bases.
* `Cslib.WordRAM.Resizable.growDirtyCode_exec`, `Cslib.WordRAM.Resizable.growZeroCode_exec`,
  `Cslib.WordRAM.Resizable.shrinkCode_exec`: `Θ(k + 1)`-step execution certificates for the derived
  bulk resize subroutines.

## References

* [Hagerup1998] Torben Hagerup, *Sorting and Searching on the Word RAM*, STACS 1998.
* [RamanRao2003] Rajeev Raman and Satti Srinivasa Rao, *Succinct Dynamic Dictionaries and Trees*,
  ICALP 2003, LNCS 2719, pp. 357–368, Section 1.1.
* [LiLiangYuZhou2023Succincter] Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic
  "Succincter"*, FOCS 2023, pp. 1715–1733 (`arXiv:2309.12950v1`, Section 2.1, PDF pp. 6–7 /
  printed pp. 5–6).
* [LiLiangYuZhou2024] Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic
  Dictionary with Subconstant Wasted Bits per Key*, SODA 2024 (`arXiv:2310.20536v1`, Section 3.2,
  PDF pp. 9–10 / printed pp. 8–9).
* [KuszmaulLiangZhou2026] William Kuszmaul, Jingxun Liang, and Renfei Zhou, *Succinct Dynamic
  Rank/Select: Bypassing the Tree-Structure Bottleneck*, SODA 2026 (`arXiv:2510.19175v1`,
  Section 5.1, PDF pp. 16–20 / printed pp. 15–19; Theorem 5.2(6) and Footnote 10, PDF p. 18 /
  printed p. 17).
-/

@[expose] public section

namespace Cslib.WordRAM.Resizable

open Cslib.WordRAM Cslib.DataStructure

variable {B B' : Basis} {r : ℕ}

/-! ## Resizable machine data and demonic word growth -/

/-- Machine data of a word-granular Resizable Word RAM: `r` registers, word-addressed memory `mem`,
and the current number of allocated `w`-bit words `frontier` (the active prefix is
`[0, frontier)`). -/
@[ext]
structure RData (r : ℕ) where
  /-- Register file contents. -/
  regs : Fin r → ℕ
  /-- Word-addressed memory contents. -/
  mem : ℕ → ℕ
  /-- Number of currently allocated words `L`. -/
  frontier : ℕ

namespace RData

/-- Underlying fixed-memory `WordRAM.Data r` (registers and memory). -/
def toData (x : RData r) : Data r := ⟨x.regs, x.mem⟩
/-- Set register `i` to `v`. -/
def set (x : RData r) (i : Fin r) (v : ℕ) : RData r :=
  ⟨Function.update x.regs i v, x.mem, x.frontier⟩
/-- Write `v` to memory address `a`. -/
def write (x : RData r) (a v : ℕ) : RData r := ⟨x.regs, Function.update x.mem a v, x.frontier⟩
/-- Set register `i` to `v` if `Fits w v`, and fault (`none`) otherwise. -/
def put (w : ℕ) (x : RData r) (i : Fin r) (v : ℕ) : Option (RData r) :=
  if Fits w v then some (x.set i v) else none

@[simp] theorem toData_regs (x : RData r) : x.toData.regs = x.regs := rfl
@[simp] theorem toData_mem (x : RData r) : x.toData.mem = x.mem := rfl
@[simp] theorem set_regs (x : RData r) (i : Fin r) (v : ℕ) :
    (x.set i v).regs = Function.update x.regs i v := rfl
@[simp] theorem set_mem (x : RData r) (i : Fin r) (v : ℕ) : (x.set i v).mem = x.mem := rfl
@[simp] theorem set_frontier (x : RData r) (i : Fin r) (v : ℕ) :
    (x.set i v).frontier = x.frontier := rfl
@[simp] theorem set_toData (x : RData r) (i : Fin r) (v : ℕ) :
    (x.set i v).toData = x.toData.set i v := rfl
@[simp] theorem write_regs (x : RData r) (a v : ℕ) : (x.write a v).regs = x.regs := rfl
@[simp] theorem write_mem (x : RData r) (a v : ℕ) :
    (x.write a v).mem = Function.update x.mem a v := rfl
@[simp] theorem write_frontier (x : RData r) (a v : ℕ) : (x.write a v).frontier = x.frontier := rfl
@[simp] theorem write_toData (x : RData r) (a v : ℕ) :
    (x.write a v).toData = x.toData.write a v := rfl
theorem put_of_fits {w : ℕ} {x : RData r} {i : Fin r} {v : ℕ} (h : Fits w v) :
    x.put w i v = some (x.set i v) := by simp [put, h]

/-- Word-boundedness and canonical frontier invariant at word width `w`: every register, memory
cell, and `frontier` fits in `w` bits, and all unallocated cells `a ≥ frontier` hold `0`. -/
def Bounded (w : ℕ) (x : RData r) : Prop :=
  x.toData.Bounded w ∧ Fits w x.frontier ∧ (∀ a, x.frontier ≤ a → x.mem a = 0)

theorem Bounded.regs_fits {w : ℕ} {x : RData r} (hx : x.Bounded w) (i : Fin r) :
    Fits w (x.regs i) := hx.1.1 i
theorem Bounded.mem_fits {w : ℕ} {x : RData r} (hx : x.Bounded w) (a : ℕ) :
    Fits w (x.mem a) := hx.1.2 a
theorem Bounded.frontier_fits {w : ℕ} {x : RData r} (hx : x.Bounded w) : Fits w x.frontier := hx.2.1
theorem Bounded.zero_above {w : ℕ} {x : RData r} (hx : x.Bounded w) {a : ℕ} (ha : x.frontier ≤ a) :
    x.mem a = 0 := hx.2.2 a ha
theorem Bounded.set {w : ℕ} {x : RData r} (hx : x.Bounded w) {i : Fin r} {v : ℕ}
    (hv : Fits w v) : (x.set i v).Bounded w := ⟨hx.1.set hv, hx.2.1, hx.2.2⟩
theorem Bounded.write {w : ℕ} {x : RData r} (hx : x.Bounded w) {a v : ℕ}
    (ha : a < x.frontier) (hv : Fits w v) : (x.write a v).Bounded w :=
  ⟨hx.1.write hv, hx.2.1, fun b hb => by
    have hne : b ≠ a := by simp only [RData.write_frontier] at hb; omega
    simpa [Function.update_of_ne hne] using hx.2.2 b hb⟩

end RData

/-- Demonic word-granular growth of `[0, L)` by `k` words at word width `w`
([KuszmaulLiangZhou2026], Section 5.1): cells `a < L` retain their values, cells `a ∈ [L, L + k)`
receive arbitrary `w`-bit words (`Fits w (mem' a)`), and cells `a ≥ L + k` hold `0`. -/
def DemonicGrow (w L k : ℕ) (mem mem' : ℕ → ℕ) : Prop :=
  (∀ a < L, mem' a = mem a) ∧ (∀ a, L ≤ a → a < L + k → Fits w (mem' a)) ∧
    (∀ a, L + k ≤ a → mem' a = 0)

/-- Zero-word growth is the identity transition on any memory zeroed above `L`. -/
theorem DemonicGrow.zero (w L : ℕ) {mem : ℕ → ℕ} (hz : ∀ a, L ≤ a → mem a = 0) :
    DemonicGrow w L 0 mem mem := ⟨fun _ _ => rfl, fun _ hlo hhi => absurd hhi (by omega), hz⟩
/-- Composing a `k`-word demonic growth from `L` with a `1`-word demonic growth from `L + k`. -/
theorem DemonicGrow.trans_one {w L k : ℕ} {mem₀ mem₁ mem₂ : ℕ → ℕ}
    (h₁ : DemonicGrow w L k mem₀ mem₁) (h₂ : DemonicGrow w (L + k) 1 mem₁ mem₂) :
    DemonicGrow w L (k + 1) mem₀ mem₂ := by
  refine ⟨fun a ha => (h₂.1 a (by omega)).trans (h₁.1 a ha), fun a hlo hhi => ?_,
    fun a ha => h₂.2.2 a (by omega)⟩
  rcases lt_or_ge a (L + k) with hlt | hge
  · exact h₂.1 a hlt ▸ h₁.2.1 a hlo hlt
  · exact h₂.2.1 a hge (by omega)
/-- Zero-initializing `[L, L + k)` via `clear mem L k` satisfies `DemonicGrow` when zero above. -/
theorem demonicGrow_clear (w L k : ℕ) (mem : ℕ → ℕ) (hz : ∀ a, L ≤ a → mem a = 0) :
    DemonicGrow w L k mem (clear mem L k) :=
  ⟨fun _ _ => clear_of_not_owns (by wram_omega),
    fun _ hlo hhi => clear_of_owns ⟨hlo, hhi⟩ ▸ fits_zero w,
    fun a _ => (clear_of_not_owns (by wram_omega)).trans (hz a (by omega))⟩
/-- `DemonicGrow w x.frontier k` preserves `RData.Bounded w` when `Fits w (x.frontier + k)`. -/
theorem RData.Bounded.grow {w : ℕ} {x : RData r} (hx : x.Bounded w) {dst : Fin r} {k : ℕ}
    {mem' : ℕ → ℕ} (hfit : Fits w (x.frontier + k))
    (hgrow : DemonicGrow w x.frontier k x.mem mem') :
    (⟨Function.update x.regs dst x.frontier, mem', x.frontier + k⟩ : RData r).Bounded w := by
  refine ⟨⟨(hx.1.set hx.frontier_fits).1, fun a => ?_⟩, hfit, hgrow.2.2⟩
  rcases lt_or_ge a x.frontier with hlt | hge
  · simpa [hgrow.1 a hlt] using hx.mem_fits a
  · rcases lt_or_ge a (x.frontier + k) with hmid | hge'
    · exact hgrow.2.1 a hge hmid
    · simp [hgrow.2.2 a hge']

/-- Shrinking by `k ≤ x.frontier` words and clearing `[frontier - k, frontier)` keeps `Bounded`. -/
theorem RData.Bounded.shrink {w : ℕ} {x : RData r} (hx : x.Bounded w) {k : ℕ}
    (hk : k ≤ x.frontier) :
    (⟨x.regs, clear x.mem (x.frontier - k) k, x.frontier - k⟩ : RData r).Bounded w := by
  refine ⟨⟨hx.1.1, fun a => ?_⟩, hx.2.1.of_le (Nat.sub_le _ _), fun a ha => ?_⟩
  · dsimp only [RData.toData]; by_cases hown : (Block.mk (x.frontier - k) k).Owns a
    · exact clear_of_owns hown ▸ fits_zero w
    · exact clear_of_not_owns hown ▸ hx.mem_fits a
  · dsimp only at ha ⊢; by_cases hlt : a < x.frontier
    · exact clear_of_owns (by wram_omega)
    · exact (clear_of_not_owns (by wram_omega)).trans (hx.zero_above (by omega))

/-- Clearing `[frontier, frontier + k)` after `DemonicGrow` recovers `x.mem` when `x.Bounded w`. -/
theorem clear_demonicGrow_eq {w k : ℕ} {x : RData r} {mem' : ℕ → ℕ}
    (hx : x.Bounded w) (hdem : DemonicGrow w x.frontier k x.mem mem') :
    clear mem' x.frontier k = x.mem := by
  funext a
  by_cases ha_lt : a < x.frontier
  · exact (clear_of_not_owns (by wram_omega)).trans (hdem.1 a ha_lt)
  · by_cases ha_in : a < x.frontier + k
    · exact (clear_of_owns (by wram_omega)).trans (hx.zero_above (by omega)).symm
    · rw [clear_of_not_owns (by wram_omega), hdem.2.2 a (by omega), hx.zero_above (by omega)]

/-! ## Bounds-checked data instruction evaluation on `RData r` -/

/-- Evaluate a data instruction on `RData r` at word size `w`, faulting when `load`/`store` accesses
an address `x.regs a ≥ x.frontier`. -/
def evalResizable (w : ℕ) : Op B r → RData r → Option (RData r)
  | .const d v, x => x.put w d v
  | .copy d s, x => some (x.set d (x.regs s))
  | .alu f d args, x => do let value ← B.interp w f (x.regs ∘ args); x.put w d value
  | .load d a, x => if x.regs a < x.frontier then some (x.set d (x.mem (x.regs a))) else none
  | .store a s, x => if x.regs a < x.frontier then some (x.write (x.regs a) (x.regs s)) else none

private theorem put_eq_some_iff {w : ℕ} {x y : RData r} {i : Fin r} {v : ℕ} :
    x.put w i v = some y ↔ Fits w v ∧ y = x.set i v := by
  simp only [RData.put]; split_ifs with h <;> simp [h, eq_comm]

/-- Any data instruction whose fixed-memory `Op.eval` succeeds with `Op.BoundedAccess L x.toData`
for `L ≤ x.frontier` evaluates identically under `evalResizable` and preserves `x.frontier`. -/
theorem evalResizable_of_boundedAccess {w L : ℕ} {o : Op B r} {x : RData r} {y : Data r}
    (hb : o.BoundedAccess L x.toData) (hL : L ≤ x.frontier) (he : o.eval w x.toData = some y) :
    evalResizable w o x = some ⟨y.regs, y.mem, x.frontier⟩ := by
  cases o with
  | const d v =>
    obtain ⟨hf, rfl⟩ := Data.put_eq_some.mp he
    simp [evalResizable, RData.put_of_fits hf, RData.set, Data.set]
  | copy d s => cases he; rfl
  | alu f d args =>
    obtain ⟨v, hv, hf, rfl⟩ := Op.eval_alu_eq_some.mp he
    change B.interp w f (x.regs ∘ args) = some v at hv
    simp [evalResizable, bind, hv, RData.put_of_fits hf, RData.set, Data.set]
  | load d a | store a s =>
    cases he
    simp [evalResizable, show x.regs _ < x.frontier from lt_of_lt_of_le hb hL,
      RData.set, Data.set, RData.write, Data.write]

/-- `evalResizable` preserves `RData.Bounded w`. -/
theorem RData.Bounded.evalResizable {w : ℕ} {o : Op B r} {x y : RData r}
    (hx : x.Bounded w) (he : Resizable.evalResizable w o x = some y) : y.Bounded w := by
  cases o with
  | const d v =>
    obtain ⟨hf, rfl⟩ := put_eq_some_iff.mp he; exact hx.set hf
  | copy d s => cases he; exact hx.set (hx.regs_fits s)
  | alu f d args =>
    obtain ⟨_, _, hput⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨hf, rfl⟩ := put_eq_some_iff.mp hput; exact hx.set hf
  | load d a =>
    rw [Resizable.evalResizable] at he
    split_ifs at he with hlt
    exact Option.some.inj he ▸ hx.set (hx.mem_fits _)
  | store a s =>
    rw [Resizable.evalResizable] at he
    split_ifs at he with hlt
    exact Option.some.inj he ▸ hx.write hlt (hx.regs_fits s)

/-- Basis simulation transports `evalResizable`. -/
theorem evalResizable_mapSimulates (φ : B.Simulates B') {w : ℕ} {o : Op B r} {x y : RData r}
    (he : evalResizable w o x = some y) : evalResizable w (o.mapSimulates φ) x = some y := by
  cases o with
  | alu f d args =>
    obtain ⟨v, hv, hput⟩ := Option.bind_eq_some_iff.mp he
    exact Option.bind_eq_some_iff.mpr ⟨v, φ.eval_some w f (x.regs ∘ args) hv, hput⟩
  | _ => exact he

/-! ## Flat and structured Resizable Word RAM programs -/

/-- Flat instructions of a word-granular Resizable Word RAM over basis `B` and `r` registers. -/
inductive RInstr (B : Basis) (r : ℕ) where
  /-- Execute a bounds-checked data instruction (`load`/`store` require `regs a < frontier`). -/
  | op (o : Op B r)
  /-- Jump unconditionally to instruction `t`. -/
  | jump (t : ℕ)
  /-- Jump to `t` if `c` holds, otherwise advance `pc` by `1`. -/
  | branch (c : Cond r) (t : ℕ)
  /-- Halt with the contents of register `i` as output. -/
  | halt (i : Fin r)
  /-- Sample uniformly from `[0, regs src]` into `dst`. -/
  | rand (dst src : Fin r)
  /-- Grow `[0, frontier)` by `1` word to `[0, frontier + 1)`, storing old `frontier` in `dst`. -/
  | grow (dst : Fin r)
  /-- Shrink `[0, frontier)` by `1` word (`1 ≤ frontier`), zeroing cell `frontier - 1`. -/
  | shrink
  deriving DecidableEq

/-- A flat Resizable Word RAM program is a list of `RInstr B r` indexed by the program counter. -/
abbrev RProgram (B : Basis) (r : ℕ) := List (RInstr B r)

/-- Machine state of a flat Resizable Word RAM program: program counter and `RData r`. -/
@[ext]
structure RState (r : ℕ) where
  /-- Program counter. -/
  pc : ℕ
  /-- Registers, memory, and active word frontier. -/
  data : RData r

/-- Absorbing configuration for clocked execution of a flat Resizable Word RAM program. -/
inductive RCfg (r : ℕ) where
  /-- Active execution at state `s`. -/
  | running (s : RState r)
  /-- Halted with scalar output `v` and final resizable machine data `data`. -/
  | halted (v : ℕ) (data : RData r)
  /-- Faulted on an out-of-bounds memory access, overflow, invalid shrink, or invalid `pc`. -/
  | faulted

/-- `p` contains the subprogram `q` starting at instruction index `base`. -/
def RProgram.Contains (p : RProgram B r) (base : ℕ) (q : RProgram B r) : Prop :=
  ∃ pre post, p = pre ++ q ++ post ∧ pre.length = base

namespace RProgram.Contains

variable {p q q₁ q₂ : RProgram B r} {base : ℕ}

theorem self (p : RProgram B r) : p.Contains 0 p := ⟨[], [], by simp, rfl⟩
theorem append_left (h : p.Contains base (q₁ ++ q₂)) : p.Contains base q₁ :=
  let ⟨pre, post, hp, hl⟩ := h; ⟨pre, q₂ ++ post, by simp [hp], hl⟩
theorem append_right (h : p.Contains base (q₁ ++ q₂)) : p.Contains (base + q₁.length) q₂ :=
  let ⟨pre, post, hp, hl⟩ := h; ⟨pre ++ q₁, post, by simp [hp], by simp [hl]⟩
theorem cons_tail {i : RInstr B r} (h : p.Contains base (i :: q)) : p.Contains (base + 1) q :=
  append_right (q₁ := [i]) h
theorem getElem? (h : p.Contains base q) {k : ℕ} (hk : k < q.length) :
    p[base + k]? = q[k]? := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hk]
theorem head {i : RInstr B r} (h : p.Contains base (i :: q)) : p[base]? = some i := by
  simpa using h.getElem? (k := 0) (by simp)

end RProgram.Contains

/-- Whether a flat resizable instruction inspects the ambient word width `w`. -/
def RInstr.ReadsWidth : RInstr B r → Prop | .op o => o.ReadsWidth | _ => False
/-- Map a basis simulation across a flat resizable instruction. -/
def RInstr.mapSimulates (φ : B.Simulates B') : RInstr B r → RInstr B' r
  | .op o => .op (o.mapSimulates φ) | .jump t => .jump t | .branch c t => .branch c t
  | .halt i => .halt i | .rand dst src => .rand dst src
  | .grow dst => .grow dst | .shrink => .shrink

/-- Structured programs of a Resizable Word RAM: bounds-checked data instructions, sequencing,
conditionals, while loops, uniform random sampling (`rand`), single-word demonic `grow`, and
single-word `shrink`. -/
inductive RCode (B : Basis) (r : ℕ) where
  | op (o : Op B r)
  | seq (c₁ c₂ : RCode B r)
  | branch (c : Cond r) (pos neg : RCode B r)
  | loop (c : Cond r) (body : RCode B r)
  | rand (dst src : Fin r)
  | grow (dst : Fin r)
  | shrink
  deriving DecidableEq

namespace RCode

/-- Embed a standard structured `WordRAM.Code B r` into `RCode B r`. -/
def ofCode : Code B r → RCode B r
  | .op o => .op o | .seq c₁ c₂ => .seq (ofCode c₁) (ofCode c₂)
  | .branch c pos neg => .branch c (ofCode pos) (ofCode neg)
  | .loop c body => .loop c (ofCode body) | .rand dst src => .rand dst src

/-- Compiled flat instruction count of a structured `RCode B r`. -/
@[simp] def size : RCode B r → ℕ
  | .seq c₁ c₂ => c₁.size + c₂.size | .branch _ pos neg => neg.size + pos.size + 2
  | .loop _ body => body.size + 3 | .op _ | .rand _ _ | .grow _ | .shrink => 1

/-- Assemble a structured `RCode B r` at instruction index `pc`. -/
def assemble : RCode B r → ℕ → RProgram B r
  | .op o, _ => [.op o] | .rand dst src, _ => [.rand dst src]
  | .grow dst, _ => [.grow dst] | .shrink, _ => [.shrink]
  | .seq c₁ c₂, pc => c₁.assemble pc ++ c₂.assemble (pc + c₁.size)
  | .branch c pos neg, pc =>
    .branch c (pc + neg.size + 2) :: neg.assemble (pc + 1) ++
      .jump (pc + neg.size + pos.size + 2) :: pos.assemble (pc + neg.size + 2)
  | .loop c body, pc =>
    .branch c (pc + 2) :: .jump (pc + body.size + 3) :: body.assemble (pc + 2) ++ [.jump pc]

/-- Assembling `c : RCode B r` at any base index produces `c.size` flat instructions. -/
@[simp] theorem length_assemble (c : RCode B r) (pc : ℕ) : (c.assemble pc).length = c.size := by
  induction c generalizing pc with
  | branch _ _ _ ihp ihn =>
    simp only [assemble, List.length_append, List.length_cons, ihp, ihn, size]; omega
  | _ => simp_all [assemble]

/-- Complete flat Resizable Word RAM program: `c.assemble 0` followed by `halt out`. -/
def program (c : RCode B r) (out : Fin r) : RProgram B r := c.assemble 0 ++ [.halt out]

/-- Whether a structured `RCode B r` inspects the ambient word width `w`. -/
def ReadsWidth : RCode B r → Prop
  | .op o => o.ReadsWidth | .seq c₁ c₂ => c₁.ReadsWidth ∨ c₂.ReadsWidth
  | .branch _ pos neg => pos.ReadsWidth ∨ neg.ReadsWidth | .loop _ body => body.ReadsWidth
  | .rand _ _ | .grow _ | .shrink => False

@[simp] theorem readsWidth_ofCode (c : Code B r) : (ofCode c).ReadsWidth ↔ c.ReadsWidth := by
  induction c <;> simp_all [ofCode, ReadsWidth, Code.ReadsWidth]

/-- Map a basis simulation across `RCode B r`. -/
def mapSimulates (φ : B.Simulates B') : RCode B r → RCode B' r
  | .op o => .op (o.mapSimulates φ) | .seq c₁ c₂ => .seq (c₁.mapSimulates φ) (c₂.mapSimulates φ)
  | .branch c pos neg => .branch c (pos.mapSimulates φ) (neg.mapSimulates φ)
  | .loop c body => .loop c (body.mapSimulates φ) | .rand dst src => .rand dst src
  | .grow dst => .grow dst | .shrink => .shrink

@[simp] theorem size_mapSimulates (φ : B.Simulates B') (c : RCode B r) :
    (c.mapSimulates φ).size = c.size := by induction c <;> simp_all [mapSimulates, size]
theorem mapSimulates_ofCode (φ : B.Simulates B') (c : Code B r) :
    (ofCode c).mapSimulates φ = ofCode (c.mapSimulates φ) := by
  induction c <;> simp_all [ofCode, mapSimulates, Code.mapSimulates]
theorem readsWidth_of_mapSimulates (φ : B.Simulates B') {c : RCode B r}
    (h : (c.mapSimulates φ).ReadsWidth) : c.ReadsWidth := by
  induction c with
  | op o => exact Op.readsWidth_of_mapSimulates φ h
  | seq _ _ ih₁ ih₂ | branch _ _ _ ih₁ ih₂ => exact h.imp ih₁ ih₂
  | loop _ _ ih => exact ih h
  | rand _ _ | grow _ | shrink => exact h

end RCode

/-! ### Locating the parts of an assembled structured program -/

namespace RProgram.Contains

variable {p : RProgram B r} {pc : ℕ}

/-- The second part of an assembled sequence starts after the first. -/
theorem seq_right {c₁ c₂ : RCode B r} (hp : p.Contains pc ((RCode.seq c₁ c₂).assemble pc)) :
    p.Contains (pc + c₁.size) (c₂.assemble (pc + c₁.size)) := by
  simpa [RCode.length_assemble] using hp.append_right

/-- An assembled branch starts with its test, which jumps over the negative arm. -/
theorem branch_head {c : Cond r} {pos neg : RCode B r}
    (hp : p.Contains pc ((RCode.branch c pos neg).assemble pc)) :
    p[pc]? = some (.branch c (pc + neg.size + 2)) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head

/-- The negative arm of an assembled branch follows its test. -/
theorem branch_neg {c : Cond r} {pos neg : RCode B r}
    (hp : p.Contains pc ((RCode.branch c pos neg).assemble pc)) :
    p.Contains (pc + 1) (neg.assemble (pc + 1)) :=
  hp.cons_tail.append_left

/-- The negative arm of an assembled branch ends with a jump over the positive arm. -/
theorem branch_jump {c : Cond r} {pos neg : RCode B r}
    (hp : p.Contains pc ((RCode.branch c pos neg).assemble pc)) :
    p[pc + 1 + neg.size]? = some (.jump (pc + neg.size + pos.size + 2)) := by
  simpa using (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).head

/-- The positive arm of an assembled branch follows the jump that ends the negative arm. -/
theorem branch_pos {c : Cond r} {pos neg : RCode B r}
    (hp : p.Contains pc ((RCode.branch c pos neg).assemble pc)) :
    p.Contains (pc + neg.size + 2) (pos.assemble (pc + neg.size + 2)) := by
  have h := (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).cons_tail
  rwa [RCode.length_assemble, show pc + 1 + neg.size + 1 = pc + neg.size + 2 by omega] at h

/-- The test of an assembled loop is followed by its exit jump. -/
theorem loop_exit {c : Cond r} {body : RCode B r}
    (hp : p.Contains pc ((RCode.loop c body).assemble pc)) :
    p[pc + 1]? = some (.jump (pc + body.size + 3)) :=
  hp.cons_tail.head

/-- The body of an assembled loop follows its test and exit jump. -/
theorem loop_body {c : Cond r} {body : RCode B r}
    (hp : p.Contains pc ((RCode.loop c body).assemble pc)) :
    p.Contains (pc + 2) (body.assemble (pc + 2)) := by
  simpa [Nat.add_assoc] using hp.cons_tail.cons_tail.append_left

/-- The body of an assembled loop is followed by a jump back to the test. -/
theorem loop_back {c : Cond r} {body : RCode B r}
    (hp : p.Contains pc ((RCode.loop c body).assemble pc)) :
    p[pc + 2 + body.size]? = some (.jump pc) := by
  simpa using hp.cons_tail.cons_tail.append_right.head

end RProgram.Contains

/-! ## Big-step demonic execution (`RDemonicExec`) -/

/-- Big-step demonic execution judgment `RDemonicExec w L_peak c x T P`: at word width `w`,
starting from `x : RData r`, the structured program `c : RCode B r` executes without faulting in at
most `T` instructions, keeps the active hardware word frontier `≤ L_peak` at every step, and
establishes postcondition `P y` on the resulting state `y : RData r` for **every** demonic choice
of newly grown memory words (`DemonicGrow`) on `grow` instructions. -/
inductive RDemonicExec (w L_peak : ℕ) : RCode B r → RData r → ℕ → (RData r → Prop) → Prop where
  | op {o : Op B r} {x y : RData r} {P : RData r → Prop} :
      x.frontier ≤ L_peak → evalResizable w o x = some y → P y → RDemonicExec w L_peak (.op o) x 1 P
  | grow {dst : Fin r} {x : RData r} {P : RData r → Prop} :
      x.frontier + 1 ≤ L_peak → Fits w (x.frontier + 1) →
      (∀ mem', DemonicGrow w x.frontier 1 x.mem mem' →
        P ⟨Function.update x.regs dst x.frontier, mem', x.frontier + 1⟩) →
      RDemonicExec w L_peak (.grow dst) x 1 P
  | shrink {x : RData r} {P : RData r → Prop} :
      x.frontier ≤ L_peak → 1 ≤ x.frontier →
      P ⟨x.regs, clear x.mem (x.frontier - 1) 1, x.frontier - 1⟩ →
      RDemonicExec w L_peak .shrink x 1 P
  | rand {dst src : Fin r} {x : RData r} {P : RData r → Prop} :
      x.frontier ≤ L_peak → Fits w (x.regs src) → (∀ v ≤ x.regs src, P (x.set dst v)) →
      RDemonicExec w L_peak (.rand dst src) x 1 P
  | seq {c₁ c₂ : RCode B r} {x : RData r} {T₁ T₂ : ℕ} {Q P : RData r → Prop} :
      RDemonicExec w L_peak c₁ x T₁ Q → (∀ y, Q y → RDemonicExec w L_peak c₂ y T₂ P) →
      RDemonicExec w L_peak (.seq c₁ c₂) x (T₁ + T₂) P
  | branch_pos {c : Cond r} {pos neg : RCode B r} {x : RData r} {T : ℕ} {P : RData r → Prop} :
      c.Holds x.toData → RDemonicExec w L_peak pos x T P →
      RDemonicExec w L_peak (.branch c pos neg) x (T + 1) P
  | branch_neg {c : Cond r} {pos neg : RCode B r} {x : RData r} {T : ℕ} {P : RData r → Prop} :
      ¬c.Holds x.toData → RDemonicExec w L_peak neg x T P →
      RDemonicExec w L_peak (.branch c pos neg) x (T + 2) P
  | loop_exit {c : Cond r} {body : RCode B r} {x : RData r} {P : RData r → Prop} :
      x.frontier ≤ L_peak → ¬c.Holds x.toData → P x → RDemonicExec w L_peak (.loop c body) x 2 P
  | loop_iter {c : Cond r} {body : RCode B r} {x : RData r} {T₁ T₂ : ℕ} {Q P : RData r → Prop} :
      c.Holds x.toData → RDemonicExec w L_peak body x T₁ Q →
      (∀ y, Q y → RDemonicExec w L_peak (.loop c body) y T₂ P) →
      RDemonicExec w L_peak (.loop c body) x (T₁ + 2 + T₂) P
  | mono {c : RCode B r} {x : RData r} {T₁ T₂ : ℕ} {P Q : RData r → Prop} :
      RDemonicExec w L_peak c x T₁ P → T₁ ≤ T₂ → (∀ y, P y → Q y) → RDemonicExec w L_peak c x T₂ Q

namespace RDemonicExec

variable {w L_peak : ℕ} {x : RData r}

/-- Every `RDemonicExec` requires the entry hardware frontier to satisfy `x.frontier ≤ L_peak`. -/
theorem frontier_le {c : RCode B r} {T : ℕ} {P : RData r → Prop}
    (h : RDemonicExec w L_peak c x T P) : x.frontier ≤ L_peak := by
  induction h with
  | grow hL _ _ => omega
  | op hL | shrink hL | rand hL | loop_exit hL | seq _ _ hL | branch_pos _ _ hL
  | branch_neg _ _ hL | loop_iter _ _ _ hL | mono _ _ _ hL => exact hL

/-- Enlarge the peak hardware frontier bound `L₁ ≤ L₂`. -/
theorem mono_peak {L₁ L₂ : ℕ} {c : RCode B r} {T : ℕ} {P : RData r → Prop}
    (hL : L₁ ≤ L₂) (h : RDemonicExec w L₁ c x T P) : RDemonicExec w L₂ c x T P := by
  induction h with
  | op hf he hp => exact .op (hf.trans hL) he hp
  | grow hf hfit hp => exact .grow (hf.trans hL) hfit hp
  | shrink hf hk hp => exact .shrink (hf.trans hL) hk hp
  | rand hf hfit hp => exact .rand (hf.trans hL) hfit hp
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | branch_pos hc _ ih => exact .branch_pos hc ih
  | branch_neg hc _ ih => exact .branch_neg hc ih
  | loop_exit hf hc hp => exact .loop_exit (hf.trans hL) hc hp
  | loop_iter hc _ _ ihb ihl => exact .loop_iter hc ihb ihl
  | mono _ hT hPQ ih => exact .mono ih hT hPQ

/-- Deterministic sequential composition specialized to equality postcondition `· = y`. -/
theorem seq_eq {c₁ c₂ : RCode B r} {y : RData r} {T₁ T₂ : ℕ} {P : RData r → Prop}
    (h₁ : RDemonicExec w L_peak c₁ x T₁ (· = y))
    (h₂ : RDemonicExec w L_peak c₂ y T₂ P) :
    RDemonicExec w L_peak (.seq c₁ c₂) x (T₁ + T₂) P :=
  h₁.seq fun _ hy => hy ▸ h₂

theorem grow_seq {dst : Fin r} {c : RCode B r} {T : ℕ} {P : RData r → Prop}
    (hL : x.frontier + 1 ≤ L_peak) (hf : Fits w (x.frontier + 1))
    (hc : ∀ m, DemonicGrow w x.frontier 1 x.mem m →
      RDemonicExec w L_peak c ⟨Function.update x.regs dst x.frontier, m, x.frontier + 1⟩ T P) :
    RDemonicExec w L_peak (.seq (.grow dst) c) x (1 + T) P :=
  RDemonicExec.seq (Q := fun z => ∃ m, DemonicGrow w x.frontier 1 x.mem m ∧
      z = ⟨Function.update x.regs dst x.frontier, m, x.frontier + 1⟩)
    (RDemonicExec.grow hL hf fun m hm => ⟨m, hm, rfl⟩) fun _ ⟨m, hm, h⟩ => h ▸ hc m hm

theorem const {d : Fin r} {v : ℕ} (hL : x.frontier ≤ L_peak) (hv : Fits w v) :
    RDemonicExec (B := B) w L_peak (.op (.const d v)) x 1 (· = x.set d v) :=
  .op hL (RData.put_of_fits hv) rfl

theorem copy {d s : Fin r} (hL : x.frontier ≤ L_peak) :
    RDemonicExec (B := B) w L_peak (.op (.copy d s)) x 1 (· = x.set d (x.regs s)) := .op hL rfl rfl
theorem load {d a : Fin r} (hL : x.frontier ≤ L_peak) (ha : x.regs a < x.frontier) :
    RDemonicExec (B := B) w L_peak (.op (.load d a)) x 1 (· = x.set d (x.mem (x.regs a))) :=
  .op hL (by simp [evalResizable, ha]) rfl
theorem store {a s : Fin r} (hL : x.frontier ≤ L_peak) (ha : x.regs a < x.frontier) :
    RDemonicExec (B := B) w L_peak (.op (.store a s)) x 1 (· = x.write (x.regs a) (x.regs s)) :=
  .op hL (by simp [evalResizable, ha]) rfl
theorem exactBin {f : BinOp} {d i j : Fin r} (hL : x.frontier ≤ L_peak) {v : ℕ}
    (hev : f.evalExact (x.regs i) (x.regs j) = some v) (hfit : Fits w v) :
    RDemonicExec (B := .exact) w L_peak (.op (.exactBin f d i j)) x 1 (· = x.set d v) := by
  refine .op hL ?_ rfl
  change (do let val ← f.evalExact (x.regs i) (x.regs j); x.put w d val) = some (x.set d v)
  rw [hev]; exact RData.put_of_fits hfit

/-- Indexed relational loop rule for `RDemonicExec`. -/
theorem loop_rel {cond : Cond r} {body : RCode B r} (P : ℕ → RData r → Prop) (k T : ℕ)
    (hc : ∀ i < k, ∀ z, P i z → cond.Holds z.toData)
    (hk : ∀ z, P k z → z.frontier ≤ L_peak ∧ ¬cond.Holds z.toData)
    (hbody : ∀ i < k, ∀ z, P i z → RDemonicExec w L_peak body z T (P (i + 1)))
    {x₀ : RData r} (hx₀ : P 0 x₀) :
    RDemonicExec w L_peak (.loop cond body) x₀ (k * (T + 2) + 2) (P k) := by
  induction k generalizing P x₀ with
  | zero => obtain ⟨hL, hnc⟩ := hk x₀ hx₀; simpa using RDemonicExec.loop_exit hL hnc hx₀
  | succ k ih =>
    refine (RDemonicExec.loop_iter (hc 0 (by omega) x₀ hx₀) (hbody 0 (by omega) x₀ hx₀)
      fun y hy => ih (fun i => P (i + 1)) (fun i hi => hc (i + 1) (by omega)) hk
        (fun i hi => hbody (i + 1) (by omega)) hy).mono (by rw [Nat.succ_mul]; omega) fun _ h => h

/-- Indexed deterministic loop rule for `RDemonicExec`. -/
theorem loop {cond : Cond r} {body : RCode B r} (xs : ℕ → RData r) (k T : ℕ)
    (hL_end : (xs k).frontier ≤ L_peak)
    (hc : ∀ i < k, cond.Holds (xs i).toData) (hk : ¬cond.Holds (xs k).toData)
    (hbody : ∀ i < k, RDemonicExec w L_peak body (xs i) T (· = xs (i + 1))) :
    RDemonicExec w L_peak (.loop cond body) (xs 0) (k * (T + 2) + 2) (· = xs k) :=
  loop_rel (fun i z => z = xs i) k T (fun i hi _ hz => hz ▸ hc i hi)
    (fun _ hz => ⟨hz ▸ hL_end, hz ▸ hk⟩) (fun i hi _ hz => hz ▸ hbody i hi) rfl

/-- Transport `RDemonicExec` along any defined-evaluation basis simulation `φ : B.Simulates B'`. -/
theorem mapSimulates (φ : B.Simulates B') {c : RCode B r} {T : ℕ} {P : RData r → Prop}
    (h : RDemonicExec w L_peak c x T P) : RDemonicExec w L_peak (c.mapSimulates φ) x T P := by
  induction h with
  | op hL he hp => exact .op hL (evalResizable_mapSimulates φ he) hp
  | grow hL hfit hp => exact .grow hL hfit hp
  | shrink hL hk hp => exact .shrink hL hk hp
  | rand hL hfit hp => exact .rand hL hfit hp
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | branch_pos hc _ ih => exact .branch_pos hc ih
  | branch_neg hc _ ih => exact .branch_neg hc ih
  | loop_exit hL hc hp => exact .loop_exit hL hc hp
  | loop_iter hc _ _ ihb ihl => exact .loop_iter hc ihb ihl
  | mono _ hT hPQ ih => exact .mono ih hT hPQ

/-- Lift any frontier-bounded structured execution `ExecBoundedExact w L c x.toData y n` with
`L ≤ x.frontier ≤ L_peak` directly to `RDemonicExec` on `RCode.ofCode c`. -/
theorem of_execBoundedExact {L n : ℕ} {c : Code B r} {y : Data r}
    (hL_peak : x.frontier ≤ L_peak) (hL : L ≤ x.frontier)
    (h : ExecBoundedExact w L c x.toData y n) :
    RDemonicExec w L_peak (RCode.ofCode c) x n (· = ⟨y.regs, y.mem, x.frontier⟩) := by
  generalize hx0 : x.toData = x₀ at h
  induction h generalizing x with
  | op hb he => subst hx0; exact .op hL_peak (evalResizable_of_boundedAccess hb hL he) rfl
  | seq _ _ ih₁ ih₂ => subst hx0; exact (ih₁ hL_peak hL rfl).seq_eq (ih₂ hL_peak hL rfl)
  | branch_pos hc _ ih => subst hx0; exact .branch_pos hc (ih hL_peak hL rfl)
  | branch_neg hc _ ih => subst hx0; exact .branch_neg hc (ih hL_peak hL rfl)
  | loop_exit hc => subst hx0; exact .loop_exit hL_peak hc (by cases x; rfl)
  | @loop_iter _ _ _ y _ m n hc _ _ ihb ihl =>
    subst hx0
    exact (RDemonicExec.loop_iter (T₂ := n) hc (ihb hL_peak hL rfl) fun _ hy =>
      hy ▸ ihl (x := ⟨y.regs, y.mem, x.frontier⟩) hL_peak hL rfl).mono (by omega) fun _ h => h

/-- **Main `ExecBounded` → `RDemonicExec` bridge (`RDemonicExec.of_execBounded`).**
Every `ExecBounded w L c x.toData y T` whose address bound `L` lies at or below `x.frontier` lifts
directly to `RDemonicExec w L_peak (RCode.ofCode c) x T` with unchanged hardware `frontier`. -/
theorem of_execBounded {L T : ℕ} {c : Code B r} {y : Data r}
    (hL_peak : x.frontier ≤ L_peak) (hL : L ≤ x.frontier)
    (h : ExecBounded w L c x.toData y T) :
    RDemonicExec w L_peak (RCode.ofCode c) x T (· = ⟨y.regs, y.mem, x.frontier⟩) := by
  obtain ⟨n, hn, hex⟩ := h
  exact (of_execBoundedExact hL_peak hL hex).mono hn fun _ hy => hy

/-- Lift any register-only `ExecWithin` execution directly to `RDemonicExec`. -/
theorem of_execWithin_regOnly {T : ℕ} {c : Code B r} {y : Data r}
    (hL_peak : x.frontier ≤ L_peak) (hc : IsRegOnlyCode c)
    (h : ExecWithin w c x.toData y T) :
    RDemonicExec w L_peak (RCode.ofCode c) x T (· = ⟨y.regs, y.mem, x.frontier⟩) :=
  of_execBounded hL_peak (Nat.zero_le _) (ExecBounded.of_execWithin_regOnly hc h)

/-- **Direct `RealizesBounded` → `RDemonicExec` bridge (`RDemonicExec.of_realizesBounded`).**
Any `Memory.Prog` client certified by `RealizesBounded` whose post-state frontier stays
`≤ x.frontier` (for example, any non-allocating segment using only `Memory.read`, `Memory.write`,
arithmetic glue, conditionals, `iterate`, and `boundedWhile` when `x.regs frontier ≤ x.frontier`)
executes directly on the Resizable Word RAM via `RCode.ofCode`. -/
theorem of_realizesBounded {k l n C : ℕ} {δ α : Type}
    {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}
    {emit : ∀ {r : ℕ}, Fin r → (Fin k → Fin r) → (Fin (l + n + 1) → Fin r) → Code B r}
    (hspec : Realization.Realizes.SpecBounded B p input output safe work n C emit)
    (frontier : Fin r) (src : Fin k → Fin r) (tmp : Fin (l + n + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier)
    (d : δ) (hx : x.Bounded w) (hL_peak : x.frontier ≤ L_peak)
    (hin : x.regs ∘ src = input d)
    (hsafe : safe w d (Realization.memoryState frontier x.toData))
    (hv : (Memory.spec w).ValidHistory (Realization.memoryState frontier x.toData)
      ((Memory.spec w).clientHistory (Realization.memoryState frontier x.toData) (p d)))
    (hnoalloc : ((Memory.spec w).clientState
      (Realization.memoryState frontier x.toData) (p d)).frontier ≤ x.frontier) :
    ∃ y : Data r,
      RDemonicExec w L_peak (RCode.ofCode (emit frontier src tmp)) x
        (C * (Realization.memoryCost (p d) (Realization.memoryState frontier x.toData) +
          work d (Realization.memoryState frontier x.toData) + 1))
        (· = ⟨y.regs, y.mem, x.frontier⟩) ∧
      Realization.memoryState frontier y =
        (Memory.spec w).clientState (Realization.memoryState frontier x.toData) (p d) ∧
      (∀ i : Fin l, y.regs (tmp (Fin.castAdd (n + 1) i)) =
        output ((Memory.spec w).clientResult (Realization.memoryState frontier x.toData) (p d)) i) ∧
      ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i := by
  obtain ⟨_, hrun⟩ := hspec frontier src tmp hi hd hf hs
  obtain ⟨y, hy, hm, hout, hframe⟩ := hrun w d x.toData hx.1 hin hsafe hv
  exact ⟨y, of_execBounded hL_peak
    (hm ▸ hnoalloc : (Realization.memoryState frontier y).frontier ≤ x.frontier) hy, hm, hout,
    hframe⟩

end RDemonicExec

/-! ## Derived `Θ(k + 1)` bulk resize subroutines (`growDirtyCode`, `growZeroCode`, `shrinkCode`) -/

private theorem write_zero_demonicGrow_one {w L : ℕ} {mem mem' : ℕ → ℕ}
    (hz : ∀ a, L ≤ a → mem a = 0) (hg : DemonicGrow w L 1 mem mem') :
    Function.update mem' L 0 = mem := by
  funext a
  rcases lt_trichotomy a L with hlt | rfl | hgt
  · rw [Function.update_of_ne hlt.ne, hg.1 a hlt]
  · exact (Function.update_self ..).trans (hz a le_rfl).symm
  · rw [Function.update_of_ne hgt.ne', hg.2.2 a (by omega), hz a (by omega)]

private theorem clear_shrink_step {m : ℕ → ℕ} {f i : ℕ} (hi : i < f) :
    clear (clear m (f - i) i) (f - i - 1) 1 = clear m (f - (i + 1)) (i + 1) := by
  funext a; by_cases h1 : (Block.mk (f - i - 1) 1).Owns a
  · rw [clear_of_owns h1, clear_of_owns (by wram_omega [h1])]
  · rw [clear_of_not_owns h1]; by_cases h2 : (Block.mk (f - i) i).Owns a
    · rw [clear_of_owns h2, clear_of_owns (by wram_omega [h2])]
    · rw [clear_of_not_owns h2, clear_of_not_owns (by wram_omega [h1, h2])]

section GrowLoop

variable {count result cur idx zero one : Fin r}

private theorem seq_const {w L_peak T : ℕ} {d : Fin r} {v : ℕ} {c : RCode B r} {x : RData r}
    {P : RData r → Prop} (hL : x.frontier ≤ L_peak) (hv : Fits w v)
    (hc : RDemonicExec w L_peak c (x.set d v) T P) :
    RDemonicExec w L_peak (.seq (.op (.const d v)) c) x (1 + T) P :=
  RDemonicExec.seq_eq (RDemonicExec.const hL hv) hc

private theorem seq_grow_store_zero {w L_peak T : ℕ} {dst : Fin r} {tail : RCode .exact r}
    {x : RData r} {P : RData r → Prop} (hz : ∀ a, x.frontier ≤ a → x.mem a = 0)
    (hne : zero ≠ dst) (hzero : x.regs zero = 0) (hL : x.frontier + 1 ≤ L_peak)
    (hfit : Fits w (x.frontier + 1)) (htail : RDemonicExec (B := .exact) w L_peak tail
      ⟨Function.update x.regs dst x.frontier, x.mem, x.frontier + 1⟩ T P) :
    RDemonicExec (B := .exact) w L_peak
      (.seq (.grow dst) (.seq (.op (.store dst zero)) tail)) x (1 + (1 + T)) P := by
  refine RDemonicExec.grow_seq hL hfit fun m hm =>
    RDemonicExec.seq_eq (RDemonicExec.store hL (by simp)) ?_
  have hw : (⟨Function.update x.regs dst x.frontier, m, x.frontier + 1⟩ : RData r).write
      (Function.update x.regs dst x.frontier dst) (Function.update x.regs dst x.frontier zero) =
      ⟨Function.update x.regs dst x.frontier, x.mem, x.frontier + 1⟩ :=
    RData.ext rfl (by
      simp only [RData.write_mem, Function.update_self, Function.update_of_ne hne, hzero]
      exact write_zero_demonicGrow_one hz hm) rfl
  exact hw ▸ htail

/-- Shared loop-invariant register file after `i` iterations of `growDirtyCode` / `growZeroCode`. -/
private def growLoopRegs (regs : Fin r → ℕ) (result cur idx zero one : Fin r) (f i : ℕ) :
    Fin r → ℕ :=
  let base := Function.update (Function.update (Function.update regs zero 0) one 1) result f
  Function.update (if i = 0 then base else Function.update base cur (f + i)) idx (i + 1)

private theorem growLoopRegs_ne {regs : Fin r → ℕ} {j : Fin r} {f i : ℕ}
    (hi : j ≠ idx) (hc : j ≠ cur) :
    growLoopRegs regs result cur idx zero one f i j =
      Function.update (Function.update (Function.update regs zero 0) one 1) result f j := by
  dsimp only [growLoopRegs]; rw [Function.update_of_ne hi]
  split_ifs <;> simp [Function.update_of_ne hc]

private theorem growLoop_exec {w L_peak T : ℕ} {body : RCode .exact r} {regs : Fin r → ℕ} {f : ℕ}
    (Q : ℕ → (ℕ → ℕ) → Prop) (hpos : 0 < regs count) (hL : f + regs count ≤ L_peak)
    (hcd : count ≠ result ∧ count ≠ cur ∧ count ≠ idx ∧ count ≠ zero ∧ count ≠ one) {m₀ : ℕ → ℕ}
    (hm₀ : Q 0 m₀) (hstep : ∀ i < regs count - 1, ∀ m, Q i m → RDemonicExec w L_peak body
      ⟨growLoopRegs regs result cur idx zero one f i, m, f + (i + 1)⟩ T fun z =>
        z.regs = growLoopRegs regs result cur idx zero one f (i + 1) ∧
          z.frontier = f + (i + 1 + 1) ∧ Q (i + 1) z.mem) :
    RDemonicExec w L_peak (.loop (.lt idx count) body)
      ⟨growLoopRegs regs result cur idx zero one f 0, m₀, f + 1⟩ ((regs count - 1) * (T + 2) + 2)
      fun z => z.regs = growLoopRegs regs result cur idx zero one f (regs count - 1) ∧
        z.frontier = f + regs count ∧ Q (regs count - 1) z.mem := by
  have hcnt (i : ℕ) : growLoopRegs regs result cur idx zero one f i count = regs count := by
    obtain ⟨hcr, hcc, hci, hcz, hco⟩ := hcd
    rw [growLoopRegs_ne hci hcc, Function.update_of_ne hcr, Function.update_of_ne hco,
      Function.update_of_ne hcz]
  have hidx_val (i : ℕ) : growLoopRegs regs result cur idx zero one f i idx = i + 1 :=
    Function.update_self ..
  refine (RDemonicExec.loop_rel
    (fun i z => z.regs = growLoopRegs regs result cur idx zero one f i ∧
      z.frontier = f + (i + 1) ∧ Q i z.mem) (regs count - 1) T
    (fun i hi z ⟨hr, _, _⟩ => by
      change z.regs idx < z.regs count
      rw [hr, hidx_val, hcnt]; omega)
    (fun z ⟨hr, hfr, _⟩ => ⟨by omega, by
      change ¬z.regs idx < z.regs count
      rw [hr, hidx_val, hcnt]; omega⟩)
    (fun i hi z ⟨hr, hfr, hm⟩ => by cases z; subst hr hfr; exact hstep i hi _ hm)
    ⟨rfl, rfl, hm₀⟩).mono le_rfl fun _ ⟨hr, hfr, hm⟩ => ⟨hr, by omega, hm⟩

private theorem growLoop_inc {w L_peak f i : ℕ} {regs : Fin r → ℕ} {m : ℕ → ℕ}
    {P : RData r → Prop} (hci : cur ≠ idx) (hco : cur ≠ one) (hio : idx ≠ one) (hro : result ≠ one)
    (hfr : f + (i + 1) + 1 ≤ L_peak) (hfit : Fits w (i + 1 + 1))
    (hp : P ⟨growLoopRegs regs result cur idx zero one f (i + 1), m, f + (i + 1 + 1)⟩) :
    RDemonicExec (B := .exact) w L_peak (.op (.exactBin .add idx idx one))
      ⟨Function.update (growLoopRegs regs result cur idx zero one f i) cur (f + (i + 1)),
        m, f + (i + 1) + 1⟩ 1 P :=
  (RDemonicExec.exactBin hfr (by
    dsimp only; rw [BinOp.evalExact, Function.update_of_ne hci.symm, Function.update_of_ne hco.symm,
      growLoopRegs_ne hio.symm hco.symm, Function.update_of_ne hro.symm, Function.update_self]
    simp [growLoopRegs]) hfit).mono le_rfl fun _ hz => by
      subst hz
      have hregs : Function.update (Function.update
          (growLoopRegs regs result cur idx zero one f i) cur (f + (i + 1))) idx (i + 1 + 1) =
          growLoopRegs regs result cur idx zero one f (i + 1) := by
        simp only [growLoopRegs, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
        rw [Function.update_comm hci.symm, Function.update_idem]
        split_ifs <;> first | rfl | rw [Function.update_idem]
      simpa only [RData.set, hregs, Nat.add_assoc] using hp

end GrowLoop

/-- Derived exact-basis (`Basis.exact`) subroutine looping single-word `.grow` `regs count` times in
`4 * count + 5` instructions, storing the old `frontier` in `result` when `0 < regs count`. -/
def growDirtyCode (count result cur idx zero one : Fin r) : RCode .exact r :=
  .seq (.op (.const zero 0)) <| .seq (.op (.const one 1)) <|
  .branch (.lt zero count)
    (.seq (.seq (.grow result) (.op (.const idx 1)))
      (.loop (.lt idx count) (.seq (.grow cur) (.op (.exactBin .add idx idx one)))))
    (.op (.copy zero zero))

theorem growDirtyCode_not_readsWidth (count result cur idx zero one : Fin r) :
    ¬(growDirtyCode count result cur idx zero one).ReadsWidth := by
  simp [growDirtyCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin]

/-- **Derived `Θ(k + 1)` demonic growth (`growDirtyCode_exec`).** -/
theorem growDirtyCode_exec {w L_peak : ℕ} {count result cur idx zero one : Fin r} {x : RData r}
    (hx : x.Bounded w) (hd : [count, result, cur, idx, zero, one].Nodup) (h1 : Fits w 1)
    (hL_peak : x.frontier + x.regs count ≤ L_peak) (hw : Fits w (x.frontier + x.regs count)) :
    let f := x.frontier; let k := x.regs count
    RDemonicExec w L_peak (growDirtyCode count result cur idx zero one) x (4 * k + 5) fun y =>
      y.Bounded w ∧ DemonicGrow w f k x.mem y.mem ∧ y.frontier = f + k ∧
        y.regs result = (if k = 0 then x.regs result else f) ∧
        ∀ j, j ≠ result → j ≠ cur → j ≠ idx → j ≠ zero → j ≠ one → y.regs j = x.regs j := by
  intro f k; have hfk : Fits w k := hx.regs_fits count
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, ← ne_eq,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨hcr, hcc, hci, hcz, hco⟩, ⟨hrc, hri, hrz, hro⟩, ⟨hci', hcz', hco'⟩,
    ⟨hiz, hio⟩, hzo, -⟩ := hd
  refine (seq_const (T := 1 + (4 * k + 3)) (by omega) (fits_zero w) <|
    seq_const (by simp only [RData.set_frontier]; omega) h1 ?_).mono (by omega) fun _ h => h
  set x₂ := (x.set zero 0).set one 1
  have hx₂_k : x₂.regs count = k := by simp [x₂, hcz, hco, k]
  have hx₂_z : x₂.regs zero = 0 := by simp [x₂, hzo]
  by_cases hk0 : k = 0
  · refine (RDemonicExec.branch_neg (by simp [Cond.Holds, hx₂_z, hx₂_k, hk0])
      (RDemonicExec.copy (by simp only [x₂, RData.set_frontier]; omega))).mono (by omega) ?_
    rintro _ rfl
    exact ⟨((hx.set (fits_zero w)).set h1).set (hx₂_z ▸ fits_zero w),
      by simpa [x₂, hk0] using DemonicGrow.zero w f hx.2.2, by simp [x₂, f, hk0],
      by simp [x₂, hk0, hrz, hro, hzo],
      fun j _ _ _ hjz hjo => by simp [x₂, hjz, hjo, hzo]⟩
  · have hpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hrun := (RDemonicExec.grow_seq (w := w) (L_peak := L_peak) (dst := result) (x := x₂)
        (by dsimp only [x₂, RData.set]; omega)
        (hw.of_le (by dsimp only [x₂, RData.set]; omega)) fun m₁ hm₁ =>
        (RDemonicExec.const (d := idx) (v := 1) (by dsimp only [x₂, RData.set]; omega) h1).mono
          le_rfl (Q := fun z => ∃ m, DemonicGrow w f 1 x.mem m ∧
            z = ⟨growLoopRegs x.regs result cur idx zero one f 0, m, f + 1⟩)
          fun _ h => ⟨m₁, hm₁, h⟩).seq fun _ ⟨m₁, hm₁, h⟩ => h ▸
      growLoop_exec (fun i m => DemonicGrow w f (i + 1) x.mem m) hpos hL_peak
        ⟨hcr, hcc, hci, hcz, hco⟩ hm₁
        fun i hi m hg => by
          change i < k - 1 at hi
          exact RDemonicExec.grow_seq (by dsimp only; omega) (hw.of_le (by dsimp only; omega))
            fun m' hm' => growLoop_inc hci' hco' hio hro (by omega) (hfk.of_le (by omega))
              ⟨rfl, rfl, hg.trans_one hm'⟩
    refine (RDemonicExec.branch_pos (by simp [Cond.Holds, hx₂_z, hx₂_k, hpos]) hrun).mono
      (by change 1 + 1 + ((k - 1) * (1 + 1 + 2) + 2) + 1 ≤ 4 * k + 3; omega)
      fun y ⟨hr, hfr, hg⟩ => ?_
    have hg' : DemonicGrow w f k x.mem y.mem := (show k - 1 + 1 = k by omega) ▸ hg
    refine ⟨⟨⟨?_, (hx.grow (dst := result) hw hg').1.2⟩, hfr ▸ hw, hfr ▸ hg'.2.2⟩,
      hg', hfr, by rw [hr, growLoopRegs_ne hri hrc, Function.update_self]; simp [hk0, f],
      fun j hjr hjc hji hjz hjo => by
        rw [hr, growLoopRegs_ne hji hjc, Function.update_of_ne hjr, Function.update_of_ne hjo,
          Function.update_of_ne hjz]⟩
    have hb := ((hx.1.set (i := zero) (fits_zero w)).set (i := one) h1).set
      (i := result) hx.frontier_fits
    have hfk' : Fits w (k - 1 + 1) := hfk.of_le (by omega)
    rw [RData.toData_regs, hr]; dsimp only [growLoopRegs]
    split_ifs
    · exact (hb.set (i := idx) hfk').1
    · exact ((hb.set (i := cur) (hw.of_le (by
        change x.frontier + (x.regs count - 1) ≤ x.frontier + x.regs count; omega))).set
        (i := idx) hfk').1

/-- Deterministic post-state of `growZeroCode`. -/
def growZeroPost (count result cur idx zero one : Fin r) (x : RData r) : RData r :=
  ⟨Function.update (Function.update (Function.update (Function.update (Function.update
      x.regs zero 0) one 1) result (if x.regs count = 0 then x.regs result else x.frontier))
      idx (x.regs count)) cur 0,
   x.mem, x.frontier + x.regs count⟩

/-- Derived exact-basis (`Basis.exact`) subroutine growing by `regs count` words via 1-word `.grow`
and immediately zeroing each newly grown word in `5 * count + 6` instructions. -/
def growZeroCode (count result cur idx zero one : Fin r) : RCode .exact r :=
  .seq (.op (.const zero 0)) <| .seq (.op (.const one 1)) <| .seq (.op (.const idx 0)) <|
  .branch (.lt zero count)
    (.seq (.seq (.grow result) (.seq (.op (.store result zero)) (.op (.const idx 1))))
      (.seq (.loop (.lt idx count)
        (.seq (.grow cur) (.seq (.op (.store cur zero)) (.op (.exactBin .add idx idx one)))))
        (.op (.const cur 0))))
    (.op (.const cur 0))

theorem growZeroCode_not_readsWidth (count result cur idx zero one : Fin r) :
    ¬(growZeroCode count result cur idx zero one).ReadsWidth := by
  simp [growZeroCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin]

/-- **Derived `Θ(k + 1)` zero-initialized growth (`growZeroCode_exec`).** -/
theorem growZeroCode_exec {w L_peak : ℕ} {count result cur idx zero one : Fin r} {x : RData r}
    (hx : x.Bounded w) (hd : [count, result, cur, idx, zero, one].Nodup) (h1 : Fits w 1)
    (hL_peak : x.frontier + x.regs count ≤ L_peak) (hw : Fits w (x.frontier + x.regs count)) :
    RDemonicExec w L_peak (growZeroCode count result cur idx zero one) x (5 * x.regs count + 6)
      (· = growZeroPost count result cur idx zero one x) := by
  set f := x.frontier; set k := x.regs count; have hfk : Fits w k := hx.regs_fits count
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, ← ne_eq,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨hcr, hcc, hci, hcz, hco⟩, ⟨_, hri, hrz, hro⟩, ⟨hci', hcz', hco'⟩,
    ⟨hiz, hio⟩, hzo, -⟩ := hd
  refine (seq_const (T := 1 + (1 + (5 * k + 3))) (by omega) (fits_zero w) <|
    seq_const (by simp only [RData.set_frontier]; omega) h1 <|
    seq_const (by simp only [RData.set_frontier]; omega) (fits_zero w) ?_).mono
      (by omega) fun _ h => h
  set x₃ := ((x.set zero 0).set one 1).set idx 0
  have hx₃_k : x₃.regs count = k := by simp [x₃, hci, hco, hcz, k]
  have hx₃_z : x₃.regs zero = 0 := by simp [x₃, hiz.symm, hzo]
  by_cases hk0 : k = 0
  · refine (RDemonicExec.branch_neg (by simp [Cond.Holds, hx₃_z, hx₃_k, hk0])
      (RDemonicExec.const (by simp only [x₃, RData.set_frontier]; omega) (fits_zero w))).mono
      (by omega) ?_
    rintro _ rfl; have hk0' : x.regs count = 0 := hk0
    have hnoop : Function.update (Function.update (Function.update x.regs zero 0) one 1)
        result (x.regs result) = Function.update (Function.update x.regs zero 0) one 1 :=
      Function.update_eq_self_iff.mpr (by rw [Function.update_of_ne hro, Function.update_of_ne hrz])
    exact RData.ext (by simp only [x₃, growZeroPost, RData.set_regs, hk0', ↓reduceIte, hnoop])
      rfl (by simp [x₃, growZeroPost, hk0'])
  · have hpos : 0 < k := Nat.pos_of_ne_zero hk0
    have eg₀ := seq_grow_store_zero (L_peak := L_peak) (dst := result) (x := x₃)
      hx.2.2 hrz.symm hx₃_z (by dsimp only [x₃, RData.set]; omega)
      (hw.of_le (by dsimp only [x₃, RData.set]; omega)) <|
      (RDemonicExec.const (d := idx) (v := 1) (by dsimp only [x₃, RData.set]; omega) h1).mono
        le_rfl (Q := (· = ⟨growLoopRegs x.regs result cur idx zero one f 0, x.mem, f + 1⟩))
        fun _ h => by
          subst h; dsimp only [x₃, RData.set, growLoopRegs]
          rw [Function.update_comm hri.symm, Function.update_idem]; rfl
    have hloop := growLoop_exec (body := .seq (.grow cur)
        (.seq (.op (.store cur zero)) (.op (.exactBin .add idx idx one))))
      (fun _ m => m = x.mem) hpos hL_peak ⟨hcr, hcc, hci, hcz, hco⟩ (rfl : x.mem = x.mem)
        fun i hi m hm => by
        subst hm; change i < k - 1 at hi
        exact seq_grow_store_zero (T := 1)
          (fun a ha => hx.zero_above (by change f + (i + 1) ≤ a at ha; omega)) hcz'.symm
          (by dsimp only; rw [growLoopRegs_ne hiz.symm hcz'.symm, Function.update_of_ne hrz.symm,
            Function.update_of_ne hzo, Function.update_self])
          (by change f + (i + 1) + 1 ≤ L_peak; omega)
          (hw.of_le (by change f + (i + 1) + 1 ≤ f + k; omega))
          (growLoop_inc hci' hco' hio hro (by omega) (hfk.of_le (by omega)) ⟨rfl, rfl, rfl⟩)
    refine (RDemonicExec.branch_pos (by simp [Cond.Holds, hx₃_z, hx₃_k, hpos])
      (eg₀.seq_eq (hloop.seq fun y ⟨hr, hfr, hm⟩ =>
        (RDemonicExec.const (hfr ▸ hL_peak) (fits_zero w)).mono le_rfl fun _ h => by
            subst h; refine RData.ext ?_ hm hfr
            simp only [RData.set_regs, hr, growZeroPost, show x.regs count ≠ 0 from hk0, ↓reduceIte]
            dsimp only [growLoopRegs]
            rw [Function.update_comm hci'.symm, show k - 1 + 1 = k by omega]
            split_ifs <;> [rw [Function.update_comm hci'];
              rw [Function.update_idem, Function.update_comm hci']]))).mono
      (by change 1 + (1 + 1) + ((k - 1) * (1 + (1 + 1) + 2) + 2 + 1) + 1 ≤ 5 * k + 3; omega)
      fun _ h => h

/-- Deterministic post-state of `shrinkCode`. -/
def shrinkPost (count idx zero one : Fin r) (x : RData r) : RData r :=
  ⟨Function.update (Function.update (Function.update x.regs zero 0) one 1) idx (x.regs count),
   clear x.mem (x.frontier - x.regs count) (x.regs count), x.frontier - x.regs count⟩

/-- Derived exact-basis (`Basis.exact`) subroutine looping single-word `.shrink` `regs count` times
in `4 * count + 5` instructions (`regs count ≤ frontier`). -/
def shrinkCode (count idx zero one : Fin r) : RCode .exact r :=
  .seq (.op (.const zero 0)) <| .seq (.op (.const one 1)) <| .seq (.op (.const idx 0)) <|
  .loop (.lt idx count) (.seq .shrink (.op (.exactBin .add idx idx one)))

theorem shrinkCode_not_readsWidth (count idx zero one : Fin r) :
    ¬(shrinkCode count idx zero one).ReadsWidth := by
  simp [shrinkCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin]
/-- **Derived `Θ(k + 1)` multi-word shrink (`shrinkCode_exec`).** -/
theorem shrinkCode_exec {w L_peak : ℕ} {count idx zero one : Fin r} {x : RData r}
    (hx : x.Bounded w) (hd : [count, idx, zero, one].Nodup) (h1 : Fits w 1)
    (hL_peak : x.frontier ≤ L_peak) (hk_le : x.regs count ≤ x.frontier) :
    RDemonicExec w L_peak (shrinkCode count idx zero one) x (4 * x.regs count + 5)
      (· = shrinkPost count idx zero one x) := by
  set f := x.frontier; set k := x.regs count; have hfk : Fits w k := hx.regs_fits count
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, ← ne_eq,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨hci, hcz, hco⟩, ⟨hiz, hio⟩, hzo, -⟩ := hd
  let base := Function.update (Function.update x.regs zero 0) one 1
  let xs (i : ℕ) : RData r := ⟨Function.update base idx i, clear x.mem (f - i) i, f - i⟩
  have hloop := RDemonicExec.loop (B := .exact) (w := w) (L_peak := L_peak) (cond := .lt idx count)
    (body := .seq .shrink (.op (.exactBin .add idx idx one))) xs k 2
    (by dsimp only [xs]; omega)
    (fun i hi => by simp [Cond.Holds, xs, base, hci, hcz, hco, k, hi])
    (by simp [Cond.Holds, xs, base, hci, hcz, hco, k])
    fun i hi => RDemonicExec.seq_eq
      (RDemonicExec.shrink (x := xs i)
        (by dsimp only [xs]; omega)
        (by dsimp only [xs]; omega) rfl)
      ((RDemonicExec.exactBin (v := i + 1) (by dsimp only [xs]; omega)
        (by simp [BinOp.evalExact, xs, base, hio.symm]) (hfk.of_le (by omega))).mono le_rfl
        fun _ h => h ▸ RData.ext (by simp [xs]) (clear_shrink_step (by omega))
          (by dsimp only [xs, RData.set_frontier]; omega))
  have hinit : ((x.set zero 0).set one 1).set idx 0 = xs 0 := by ext <;> simp [xs, base, clear, f]
  exact (seq_const hL_peak (fits_zero w) <| seq_const hL_peak h1 <|
    seq_const hL_peak (fits_zero w) (hinit.symm ▸ hloop)).mono (by omega) fun _ h => h

end Cslib.WordRAM.Resizable
