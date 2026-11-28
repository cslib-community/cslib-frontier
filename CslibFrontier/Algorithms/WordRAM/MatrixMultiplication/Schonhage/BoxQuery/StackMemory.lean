/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Stack
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Prefixes

/-!
# Readback of the actual native query frontier

Each pending prefix is represented by its five computed scalar fields via
`Cslib.WordRAM.RecordSpec` and `Cslib.WordRAM.WordStack.Holds`. List heads occupy the top
physical record, so the native push prepends a task and pop removes that head.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Five-word flat memory specification of one pending prefix `xs : List Term` under `η`. -/
abbrev prefixTaskSpec {L : ℕ} (η : OutStr L) : RecordSpec (List Term) 5 where
  toWords xs := ![xs.length, prefixCode xs, usedFrom η 0 xs, starsFrom η 0 xs, 10 ^ xs.length]

/-- Pending logical prefixes in top-first order, with no initial-zero-memory premise. -/
abbrev StackMemory {L : ℕ} (η : OutStr L) (F : ℕ) :
    List (List Term) → (ℕ → ℕ) → Prop :=
  WordStack.Holds (prefixTaskSpec η) F

/-- Changes outside the occupied stack prefix preserve every pending task. -/
theorem StackMemory.transport {L F : ℕ} {η : OutStr L} {tasks : List (List Term)}
    {μ ν : ℕ → ℕ} (h : StackMemory η F tasks μ)
    (hf : ∀ q, F ≤ q → q < F + 5 * tasks.length → ν q = μ q) :
    StackMemory η F tasks ν :=
  h.frame fun q hq hq' => hf q hq (by omega)

/-- Appending the actual five computed fields prepends precisely that logical task. -/
theorem StackMemory.push {L F : ℕ} {η : OutStr L} {tasks : List (List Term)}
    {μ : ℕ → ℕ} (h : StackMemory η F tasks μ) (xs : List Term) :
    StackMemory η F (xs :: tasks)
      (writeTask F tasks.length xs.length (prefixCode xs) (usedFrom η 0 xs)
        (starsFrom η 0 xs) (10 ^ xs.length) μ) :=
  h.push_write xs

/-- Registers modified while popping a five-word prefix task. -/
@[expose] def PopLocal (i : Fin registers) : Prop :=
  WordStack.PopLocal Reg.top Reg.cursor popFields i

instance (i : Fin registers) : Decidable (PopLocal i) :=
  inferInstanceAs (Decidable (WordStack.PopLocal Reg.top Reg.cursor popFields i))

/-- Pop the occupied top prefix task `xs` from `StackMemory η F (xs :: rest)` in twelve
native instructions, loading its five scalar fields and preserving the remaining stack `rest`. -/
theorem StackMemory.exec_pop {w L F : ℕ} {η : OutStr L} {xs : List Term}
    {rest : List (List Term)} {x : Data registers}
    (hstack : StackMemory η F (xs :: rest) x.mem)
    (hF : x.regs Reg.stack = F) (hn : x.regs Reg.top = rest.length + 1)
    (h5 : x.regs Reg.five = 5) (h1 : x.regs BoxTable.Reg.one = 1)
    (hfit : Fits w (F + 5 * (rest.length + 1) + 8)) :
    ∃ y, ExecWithin w pop x y 12 ∧ y.regs Reg.top = rest.length ∧
      StackMemory η F rest y.mem ∧
      y.regs Reg.depth = xs.length ∧ y.regs Reg.code = prefixCode xs ∧
      y.regs Reg.used = usedFrom η 0 xs ∧ y.regs Reg.stars = starsFrom η 0 xs ∧
      y.regs Reg.power = 10 ^ xs.length ∧ y.mem = x.mem ∧
      (∀ i, ¬PopLocal i → y.regs i = x.regs i) := by
  obtain ⟨y, hy, hytop, hystack, hyfields, hymem, hyregs⟩ :=
    WordStack.pop_exec (prefixTaskSpec η) Reg.stack Reg.top Reg.cursor Reg.five BoxTable.Reg.one
      popFields rest xs x
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      hF hn h5 h1 hstack (hfit.of_le (by omega))
  exact ⟨y, hy.within, hytop, hystack,
    hyfields 0, hyfields 1, hyfields 2, hyfields 3, hyfields 4, hymem, hyregs⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
