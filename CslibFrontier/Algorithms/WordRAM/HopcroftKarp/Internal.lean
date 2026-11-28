/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.HopcroftKarp.Layout
import CslibFrontier.Computability.WordRAM.Allocation
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Internal workspace predicates and setup helpers for word-RAM Hopcroft–Karp

Scratch registers (`19 .. 33`), value encodings (`encodeOptFin`, `encodeDist`), in-memory
matching/distance predicates (`MateMem`, `DistMem`), and shared subroutines (`clearAt`,
`initBaseRegsFromCSR`) used privately by the `HopcroftKarp` sub-modules (`BFS`, `DFSStep`, `DFS`,
`MatrixCSR`, and `HopcroftKarp`). This module is imported privately by the umbrella module
`CslibFrontier.Algorithms.WordRAM.HopcroftKarp` so its declarations do not leak into the public
surface.
-/

public section

namespace Cslib.Algorithms.WordRAM.HopcroftKarp.Internal

open Cslib.WordRAM
open Cslib.Algorithms.Lean.MaxFlow
open Cslib.Algorithms.WordRAM.HopcroftKarp
open Cslib.Algorithms.WordRAM.HopcroftKarp.Reg

/-- Scratch register `19`: outer phase-loop active flag. -/
abbrev phaseActive : Fin 34 := ⟨19, by decide⟩
/-- Scratch register `20`: current augmenting-path layer depth `k`. -/
abbrev rk : Fin 34 := ⟨20, by decide⟩
/-- Scratch register `21`: flag set when BFS reaches an unmatched right vertex. -/
abbrev rfound : Fin 34 := ⟨21, by decide⟩
/-- Scratch register `22`: BFS queue head cursor / DFS root scan cursor. -/
abbrev qHead : Fin 34 := ⟨22, by decide⟩
/-- Scratch register `23`: BFS queue tail index. -/
abbrev qTail : Fin 34 := ⟨23, by decide⟩
/-- Scratch register `24`: end index of the current BFS layer in the queue. -/
abbrev layerEnd : Fin 34 := ⟨24, by decide⟩
/-- Scratch register `25`: current BFS distance / explicit DFS stack depth. -/
abbrev rd : Fin 34 := ⟨25, by decide⟩
/-- Scratch register `26`: number of disjoint augmenting paths collected in the phase. -/
abbrev augLen : Fin 34 := ⟨26, by decide⟩
/-- Scratch register `27` (`Reg.acc`): inner loop-active flag for `bfsCode` and `dfsLoop`. -/
abbrev active : Fin 34 := acc
/-- Scratch register `28`: general loop and CSR edge index. -/
abbrev idx : Fin 34 := ⟨28, by decide⟩
/-- Scratch register `29`: general loop upper-bound register. -/
abbrev limit : Fin 34 := ⟨29, by decide⟩
/-- Scratch register `30`: scratch memory-address register. -/
abbrev addr : Fin 34 := ⟨30, by decide⟩
/-- Scratch register `31`: primary scratch value register. -/
abbrev val : Fin 34 := ⟨31, by decide⟩
/-- Scratch register `32`: secondary scratch value register. -/
abbrev val2 : Fin 34 := ⟨32, by decide⟩
/-- Scratch register `33`: general temporary scratch value register. -/
abbrev tmp : Fin 34 := ⟨33, by decide⟩

/-- Encode `Option (Fin m)` into `{0, …, m}` with `none ↦ m`. -/
@[expose] def encodeOptFin {m : ℕ} : Option (Fin m) → ℕ
  | some u => u.val
  | none => m

/-- Encode `Option ℕ` layer distances with `none ↦ 0` and `some j ↦ j + 1`. -/
@[expose] def encodeDist : Option ℕ → ℕ
  | none => 0
  | some j => j + 1

/-- In-memory right-vertex mate table `colMate[0..r)` starting at `bOff + m + 1 + numEdges`. -/
@[expose] def MateMem (inst : SparseInstance) (bOff : ℕ)
    (mate : Vector (Option (Fin inst.m)) inst.r) (mem : ℕ → ℕ) : Prop :=
  ∀ v : Fin inst.r, mem (bOff + inst.m + 1 + inst.numEdges + v.val) = encodeOptFin (vget mate v)

theorem MateMem.of_outside {inst : SparseInstance} {bOff : ℕ}
    {mate : Vector (Option (Fin inst.m)) inst.r} {mem mem' : ℕ → ℕ}
    (h : MateMem inst bOff mate mem)
    (hf : ∀ a, bOff + inst.m + 1 + inst.numEdges ≤ a ∧
        a < bOff + inst.m + 1 + inst.numEdges + inst.r → mem' a = mem a) :
    MateMem inst bOff mate mem' :=
  fun v => (hf _ ⟨by omega, by have := v.isLt; omega⟩).trans (h v)

/-- In-memory left-vertex layer-distance table `dist[0..m)` starting at `bDist`. -/
@[expose] def DistMem (inst : SparseInstance) (bOff : ℕ)
    (dist : Vector (Option ℕ) inst.m) (mem : ℕ → ℕ) : Prop :=
  ∀ u : Fin inst.m,
    mem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + u.val) = encodeDist (vget dist u)

theorem DistMem.of_outside {inst : SparseInstance} {bOff : ℕ}
    {dist : Vector (Option ℕ) inst.m} {mem mem' : ℕ → ℕ}
    (h : DistMem inst bOff dist mem)
    (hf : ∀ a, bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m ≤ a ∧
        a < bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m → mem' a = mem a) :
    DistMem inst bOff dist mem' :=
  fun u => (hf _ ⟨by omega, by have := u.isLt; omega⟩).trans (h u)

theorem DistMem.vset {inst : SparseInstance} {bOff : ℕ}
    {dist : Vector (Option ℕ) inst.m} {mem mem' : ℕ → ℕ}
    (h : DistMem inst bOff dist mem) (u : Fin inst.m) (d : Option ℕ)
    (hself : mem' (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + u.val) = encodeDist d)
    (hother : ∀ w₀ : Fin inst.m, w₀ ≠ u →
      mem' (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + w₀.val) =
        mem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + w₀.val)) :
    DistMem inst bOff (Cslib.Algorithms.Lean.MaxFlow.vset dist u d) mem' := by
  intro w₀
  rcases eq_or_ne w₀ u with rfl | hne
  · simpa using hself
  · rw [hother w₀ hne, vget_vset_ne _ _ hne.symm]
    exact h w₀

/-- Zero-fill `[x.regs baseReg, x.regs baseReg + x.regs lenReg)` via `Cslib.WordRAM.zeroFill`. -/
def clearAt (baseReg lenReg : Fin 34) : Code .standard 34 :=
  .seq (ram[ addr ← baseReg; limit ← baseReg + lenReg ]) (zeroFill addr limit zero one)

theorem exec_clearAt {w base len : ℕ} (baseReg lenReg : Fin 34)
    (hb_lt : baseReg.val < 29) (hl_lt : lenReg.val < 29) (x : Data 34)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hbase : x.regs baseReg = base) (hlen : x.regs lenReg = len)
    (hfit : Fits w (base + len)) :
    ∃ y, ExecWithin w (clearAt baseReg lenReg) x y (4 * len + 4) ∧
      (∀ i : Fin 34, i.val < 29 → y.regs i = x.regs i) ∧
      (∀ k < len, y.mem (base + k) = 0) ∧
      (∀ a, ¬(base ≤ a ∧ a < base + len) → y.mem a = x.mem a) := by
  subst hbase hlen
  have hla : lenReg ≠ addr := fun h => by
    subst h
    simp at hl_lt
  have hstep₁ : ∃ s₁, ExecWithin w (ram[ addr ← baseReg; limit ← baseReg + lenReg ] :
      Code .standard 34) x s₁ 2 ∧
      s₁ = (x.set addr (x.regs baseReg)).set limit (x.regs baseReg + x.regs lenReg) := by
    refine WP.exists_execWithin ?_
    wram_exec [hla, hfit]
    rfl
  obtain ⟨s₁, he₁, rfl⟩ := hstep₁
  let st := (x.set addr (x.regs baseReg)).set limit (x.regs baseReg + x.regs lenReg)
  have hs₁_addr : st.regs addr = x.regs baseReg := by simp [st]
  have hs₁_lim : st.regs limit = x.regs baseReg + x.regs lenReg := by simp [st]
  have hs₁_0 : st.regs zero = 0 := by wram_simp [st, h0]
  have hs₁_1 : st.regs one = 1 := by wram_simp [st, h1]
  have hzf := (zeroFill_exec (w := w) (cur := addr) (stop := limit) (zero := zero) (one := one)
    (x := st) (by decide) (by decide) (by decide) hs₁_0 hs₁_1
    (by rw [hs₁_addr, hs₁_lim]; omega) (by rwa [hs₁_lim])).within
  refine ⟨_, (he₁.seq hzf).mono (by rw [hs₁_addr, hs₁_lim]; omega), fun i hi => ?_,
    fun k hk => ?_, fun a ha => ?_⟩
  · have hia : i ≠ addr := by
      rintro rfl
      simp at hi
    have hil : i ≠ limit := by
      rintro rfl
      simp at hi
    simp [st, Function.update_of_ne hia, hil]
  · dsimp only
    rw [hs₁_addr, hs₁_lim, Nat.add_sub_cancel_left]
    exact clear_of_owns (by simp only [Block.Owns]; omega)
  · dsimp only
    rw [hs₁_addr, hs₁_lim, Nat.add_sub_cancel_left]
    exact clear_of_not_owns (by simp only [Block.Owns]; omega)

/-- Populate `bEdgesReg .. outBase` from `zero, one, two, rm, rr, rE, bOffReg`. -/
def initBaseRegsFromCSR : Code .standard 34 := ram[
  bEdgesReg ← bOffReg + rm; bEdgesReg ← bEdgesReg + one;
  bColMateReg ← bEdgesReg + rE;
  bMLReg ← bColMateReg + rr;
  bDistReg ← bMLReg + rm;
  bQueueReg ← bDistReg + rm;
  bVisReg ← bQueueReg + rm;
  bStackUReg ← bVisReg + rr;
  bStackVReg ← bStackUReg + rm; bStackVReg ← bStackVReg + two;
  bStackPosReg ← bStackVReg + rm; bStackPosReg ← bStackPosReg + two;
  bAugUReg ← bStackPosReg + rm; bAugUReg ← bAugUReg + two;
  bAugVReg ← bAugUReg + rr;
  outBase ← bAugVReg + rr ]

theorem exec_initBaseRegsFromCSR {w bOff : ℕ} (inst : SparseInstance) (x : Data 34)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1) (h2 : x.regs two = 2)
    (hrm : x.regs rm = inst.m) (hrr : x.regs rr = inst.r) (hrE : x.regs rE = inst.numEdges)
    (hbOff : x.regs bOffReg = bOff)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ y, ExecWithin w initBaseRegsFromCSR x y 16 ∧
      BaseRegs inst bOff y ∧ y.mem = x.mem := by
  refine WP.exists_execWithin ?_
  wram_exec [initBaseRegsFromCSR, h1, h2, hrm, hrr, hrE, hbOff]
  refine ⟨?_, rfl⟩
  constructor <;> wram_simp [h0, h1, h2, hrm, hrr, hrE, hbOff] <;> omega

end Cslib.Algorithms.WordRAM.HopcroftKarp.Internal
