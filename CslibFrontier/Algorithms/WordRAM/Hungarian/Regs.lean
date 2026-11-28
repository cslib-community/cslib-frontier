/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.ListOutput

/-!
# Public registers and cost-matrix memory layout for the Word-RAM Hungarian method

Defines the public `Reg` constants, the `BaseRegs` register-frame invariant, and the `CostMem`
row-major cost-matrix assertion used by `coreCode` and client programs.
-/

public section

namespace Cslib.Algorithms.WordRAM.Hungarian

open Cslib.WordRAM

namespace Reg

/-- Constant `0`. -/
abbrev zero : Fin 28 := ⟨0, by decide⟩
/-- Constant `1`. -/
abbrev one : Fin 28 := ⟨1, by decide⟩
/-- Constant `2`. -/
abbrev two : Fin 28 := ⟨2, by decide⟩
/-- Side size `n`. -/
abbrev rn : Fin 28 := ⟨3, by decide⟩
/-- Matrix entry count `n * n`. -/
abbrev rnn : Fin 28 := ⟨4, by decide⟩
/-- Shift magnitude `M`. -/
abbrev rM : Fin 28 := ⟨5, by decide⟩
/-- Base of `n × n` shifted cost matrix `C`. -/
abbrev baseC : Fin 28 := ⟨6, by decide⟩
/-- Base of row potentials `y` (`n` words). -/
abbrev baseY : Fin 28 := ⟨7, by decide⟩
/-- Base of negated column potentials `-z` (`n` words). -/
abbrev baseNZ : Fin 28 := ⟨8, by decide⟩
/-- Base of column mates `colMate` (`n` words). -/
abbrev baseColMate : Fin 28 := ⟨9, by decide⟩
/-- Base of tree-column flags `used` (`n` words). -/
abbrev baseUsed : Fin 28 := ⟨10, by decide⟩
/-- Base of tree-row flags `tree` (`n` words). -/
abbrev baseTree : Fin 28 := ⟨11, by decide⟩
/-- Base of column slacks `minv` (`n` words). -/
abbrev baseMinv : Fin 28 := ⟨12, by decide⟩
/-- Base of predecessor rows `bestRow` (`n` words). -/
abbrev baseBestRow : Fin 28 := ⟨13, by decide⟩
/-- Output header cell (`1` word), followed immediately by `rowMate`. -/
abbrev outBase : Fin 28 := ⟨14, by decide⟩
/-- Base of row mates `rowMate` (`n` words, at `outBase + 1`). -/
abbrev baseRowMate : Fin 28 := ⟨15, by decide⟩
/-- Accumulator / encoded minimum cost output register. -/
abbrev acc : Fin 28 := ⟨23, by decide⟩

end Reg

open Reg

/-- Register frame holding constants, problem dimensions, and all contiguous array base addresses
starting at `bC`. -/
structure BaseRegs (n bC M : ℕ) (x : Data 28) : Prop where
  /-- `zero = 0`. -/
  hzero : x.regs zero = 0
  /-- `one = 1`. -/
  hone : x.regs one = 1
  /-- `two = 2`. -/
  htwo : x.regs two = 2
  /-- `rn = n`. -/
  hrn : x.regs rn = n
  /-- `rnn = n * n`. -/
  hrnn : x.regs rnn = n * n
  /-- `rM = M`. -/
  hrM : x.regs rM = M
  /-- `baseC = bC`. -/
  hbaseC : x.regs baseC = bC
  /-- `baseY = bC + n * n`. -/
  hbaseY : x.regs baseY = bC + n * n
  /-- `baseNZ = bC + n * n + n`. -/
  hbaseNZ : x.regs baseNZ = bC + n * n + n
  /-- `baseColMate = bC + n * n + 2 * n`. -/
  hbaseColMate : x.regs baseColMate = bC + n * n + 2 * n
  /-- `baseUsed = bC + n * n + 3 * n`. -/
  hbaseUsed : x.regs baseUsed = bC + n * n + 3 * n
  /-- `baseTree = bC + n * n + 4 * n`. -/
  hbaseTree : x.regs baseTree = bC + n * n + 4 * n
  /-- `baseMinv = bC + n * n + 5 * n`. -/
  hbaseMinv : x.regs baseMinv = bC + n * n + 5 * n
  /-- `baseBestRow = bC + n * n + 6 * n`. -/
  hbaseBestRow : x.regs baseBestRow = bC + n * n + 6 * n
  /-- `outBase = bC + n * n + 7 * n`. -/
  houtBase : x.regs outBase = bC + n * n + 7 * n
  /-- `baseRowMate = bC + n * n + 7 * n + 1`. -/
  hbaseRowMate : x.regs baseRowMate = bC + n * n + 7 * n + 1


/-- Memory holds the `n × n` unsigned cost matrix `C` row-major at `bC`. -/
@[expose] def CostMem {n : ℕ} (bC : ℕ) (C : Fin n × Fin n → ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ u v : Fin n, mem (bC + (u.val * n + v.val)) = C (u, v)

end Cslib.Algorithms.WordRAM.Hungarian
