/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Program
public import CslibFrontier.Computability.WordRAM.WordStack

/-!
# Actual five-word query-stack operations

Every pushed task writes all five words before a pop can read them. The caller may
start with dirty stack memory. These execution lemmas instantiate `Cslib.WordRAM.writeWords`
and `Cslib.WordRAM.WordStack` to charge the address arithmetic, stores, loads and top update,
and preserve all other memory and registers.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM

/-- The five actual stores performed when appending one native task. -/
@[expose] def writeTask (F n k c u e p : ℕ) (μ : ℕ → ℕ) : ℕ → ℕ :=
  writeWords μ (F + n * 5) ![k, c, u, e, p]

/-- The new task's descriptor is exactly the five words supplied by the computed child. -/
theorem writeTask_read (F n k c u e p : ℕ) (μ : ℕ → ℕ) :
    writeTask F n k c u e p μ (F + n * 5) = k ∧
    writeTask F n k c u e p μ (F + n * 5 + 1) = c ∧
    writeTask F n k c u e p μ (F + n * 5 + 2) = u ∧
    writeTask F n k c u e p μ (F + n * 5 + 3) = e ∧
    writeTask F n k c u e p μ (F + n * 5 + 4) = p := by
  have h := Block.realizes_writeWords μ (F + n * 5) ![k, c, u, e, p]
  exact ⟨h 0, h 1, h 2, h 3, h 4⟩

/-- All words outside the newly appended five-word record retain their old contents. -/
theorem writeTask_frame (F n k c u e p : ℕ) (μ : ℕ → ℕ) (q : ℕ)
    (hq : ¬(F + n * 5 ≤ q ∧ q < F + n * 5 + 5)) :
    writeTask F n k c u e p μ q = μ q :=
  writeWords_of_not_owns hq

/-- Registers modified by one real task push. -/
@[expose] def PushLocal (i : Fin registers) : Prop := WordStack.PushLocal Reg.top Reg.cursor i

instance (i : Fin registers) : Decidable (PushLocal i) :=
  inferInstanceAs (Decidable (WordStack.PushLocal Reg.top Reg.cursor i))

/-- Source field registers of `push`. -/
abbrev pushFields : Fin 5 → Fin registers :=
  ![Reg.depth, Reg.childCode, Reg.childUsed, Reg.childStars, Reg.childPower]

/-- Target field registers of `pop`. -/
abbrev popFields : Fin 5 → Fin registers :=
  ![Reg.depth, Reg.code, Reg.used, Reg.stars, Reg.power]

/-- A push preserves every register outside `PushLocal`. -/
theorem push_preserves (i : Fin registers) : ¬PushLocal i → push.Preserves i :=
  WordStack.push_preserves Reg.stack Reg.top Reg.cursor Reg.five BoxTable.Reg.one pushFields

/-- Store and append one complete task within twelve native instructions. -/
theorem exec_push {w F n k c u e p : ℕ} (x : Data registers)
    (hF : x.regs Reg.stack = F) (hn : x.regs Reg.top = n)
    (hk : x.regs Reg.depth = k) (hc : x.regs Reg.childCode = c)
    (hu : x.regs Reg.childUsed = u) (he : x.regs Reg.childStars = e)
    (hp : x.regs Reg.childPower = p) (h5 : x.regs Reg.five = 5)
    (h1 : x.regs BoxTable.Reg.one = 1) (hfit : Fits w (F + 5 * (n + 1) + 8)) :
    ∃ y, ExecWithin w push x y 12 ∧ y.regs Reg.top = n + 1 ∧
      y.mem = writeTask F n k c u e p x.mem ∧
      (∀ i, ¬PushLocal i → y.regs i = x.regs i) := by
  obtain ⟨y, hy, hytop, hymem, _, hyregs⟩ :=
    WordStack.pushWords_exec Reg.stack Reg.top Reg.cursor Reg.five BoxTable.Reg.one pushFields x
      (by decide) (by decide) (by decide) (by decide) hF hn h5 h1 (hfit.of_le (by omega))
  have hwords : (fun i => x.regs (pushFields i)) = ![k, c, u, e, p] := by
    funext i
    match i with
    | 0 => exact hk
    | 1 => exact hc
    | 2 => exact hu
    | 3 => exact he
    | 4 => exact hp
  rw [hwords] at hymem
  exact ⟨y, hy.within, hytop, hymem, hyregs⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
