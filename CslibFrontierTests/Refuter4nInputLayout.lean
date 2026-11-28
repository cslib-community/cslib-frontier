/-
Copyright (c) 2026 Christian Reitwiessner, Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Ryan Anderson
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Algorithms.WordRAM.Refuter4n.InputLayout
public meta import CslibFrontier.Algorithms.WordRAM.Refuter4n.InputLayout
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n

/-!
# Tests for the input layout and charged initial state of the `4n - 9d` refuter
-/

set_option linter.hashCommand false

public section

namespace CslibFrontierTests.Refuter4nInputLayout

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.WordRAM
open Cslib.Circuits.Boolean.AffineDisperser4n Cslib.Circuits.Boolean.SemiCircuit
open Cslib.Algorithms.WordRAM.Refuter4n

/-- A `0`-line circuit on `2` bits: the output is `x₀`. -/
def projCircuit : Circuit (fullSignature 2 Bool) 2 1 :=
  ⟨Program.empty, fun _ => Wire.input ⟨0, by decide⟩⟩

/-- One XOR line on `3` bits (gate name `3`). -/
def xor3Circuit : Circuit (fullSignature 2 Bool) 3 1 :=
  ⟨Program.gate Program.empty
    ⟨FullOp.fn fun xs => xs 0 ^^ xs 1,
      fun i => if _ : i.val = 0 then Wire.input ⟨0, by decide⟩ else Wire.input ⟨1, by decide⟩⟩,
    fun _ => Wire.gate ⟨0, by decide⟩⟩

/-- Three lines on `2` bits: `g₀ = ¬x₀` (a unary line, folded into the literal `¬x₀`),
`g₁ = g₀ ∧ x₁` (binary; the negation is absorbed into its truth table) and the constant
`g₂ = true`; the output is `g₁`. -/
def mixCircuit : Circuit (fullSignature 2 Bool) 2 1 :=
  let p1 := (Program.empty : Program (fullSignature 2 Bool) 2 0).gate
    ⟨FullOp.fn fun xs => !xs 0, fun _ => Wire.input ⟨0, by decide⟩⟩
  let p2 := p1.gate ⟨FullOp.fn fun xs => xs 0 && xs 1,
    fun i => if _ : i.val = 0 then Wire.gate ⟨0, by decide⟩ else Wire.input ⟨1, by decide⟩⟩
  let p3 := p2.gate ⟨FullOp.con true, fun i => i.elim0⟩
  ⟨p3, fun _ => Wire.gate ⟨1, by decide⟩⟩

/-- No inputs and one constant line `g₀ = true` (the `phi` loop runs no iteration). -/
def constCircuit : Circuit (fullSignature 2 Bool) 0 1 :=
  ⟨(Program.empty : Program (fullSignature 2 Bool) 0 0).gate ⟨FullOp.con true, fun i => i.elim0⟩,
    fun _ => Wire.gate ⟨0, by decide⟩⟩

/-! The input layout: `[n, s]`, three words per line, the output wire word. -/

#guard encode projCircuit == [2, 0, 0]
#guard encode constCircuit == [0, 1, 17, 0, 0, 0]
#guard encode xor3Circuit == [3, 1, 6, 0, 1, 3]
#guard encode mixCircuit == [2, 3, 3, 0, 0, 8, 2, 1, 17, 0, 0, 3]

/-- Whether `mem` holds the words of `P` at the addresses of `L` (`Stored`, as a check). -/
def storedB (L : Layout) (P : PackedState) (mem : ℕ → ℕ) : Bool :=
  mem L.base == P.params && mem (L.base + 1) == P.aux && mem (L.base + 2) == P.gates &&
    mem (L.base + 3) == P.out && mem (L.base + 4) == P.pairs.length &&
    ((List.range P.gateRows.length).all fun J =>
      mem (L.rowAddr J 0) == (P.gateRows.getD J ⟨0, 0, 0⟩).tt &&
      mem (L.rowAddr J 1) == (P.gateRows.getD J ⟨0, 0, 0⟩).left &&
      mem (L.rowAddr J 2) == (P.gateRows.getD J ⟨0, 0, 0⟩).right) &&
    ((List.range P.eqnRows.length).all fun e => mem (L.eqnAddr e) == P.eqnRows.getD e 0) &&
    ((List.range P.phiRows.length).all fun i => mem (L.phiAddr i) == P.phiRows.getD i 0) &&
    ((List.range P.pairs.length).all fun k =>
      mem (L.pairAddr k 0) == (P.pairs.getD k (0, 0)).1 &&
      mem (L.pairAddr k 1) == (P.pairs.getD k (0, 0)).2)

/-- Run `initCode` on the input of `C` at width `w` and check the stored state and the step
count against `initTime C`. -/
def runCheck {n : ℕ} (C : Circuit (fullSignature 2 Bool) n 1) (w : ℕ) : Bool :=
  match initCode.eval w 100 (.init (encode C) : Data 24) with
  | some (y, t) => storedB (layout C) (initialPacked C) y.mem && decide (t ≤ initTime C)
  | none => false

/-! Executions of the program at the smallest admitted width `max (n + s + 2) 7 = 7`: zero lines
(the line loop runs no iteration), zero inputs (the `phi` loop runs no iteration), one binary
line, and unary, binary and constant lines; and at a larger width. -/

#guard runCheck projCircuit 7
#guard runCheck constCircuit 7
#guard runCheck xor3Circuit 7
#guard runCheck mixCircuit 7
#guard runCheck mixCircuit 12

/-- The input words determine the circuit (module client of `encode_injective`). -/
example (C₁ C₂ : Circuit (fullSignature 2 Bool) 2 1) (h : encode C₁ = encode C₂) : C₁ = C₂ :=
  encode_injective h

/-- The width `7` is admitted for `xor3Circuit` (`n + C.size + 2 = 6`). -/
example : FitsWidth xor3Circuit 7 := ⟨by decide, by decide⟩

/-- At that width every input word fits (module client of `inputFits_encode`). -/
example : InputFits 7 (encode xor3Circuit) := inputFits_encode _ ⟨by decide, by decide⟩

/-- At that width the workspace fits (module client of `fits_workEnd`). -/
example : Fits 7 (workEnd xor3Circuit) := fits_workEnd _ ⟨by decide, by decide⟩

/-- The charged decoding stores the packed initial state (module client of `exec_initCode`), for
the `0`-line circuit. -/
example : ∃ y, ExecWithin 7 initCode (.init (encode projCircuit)) y (initTime projCircuit) ∧
    Stored (layout projCircuit) (initialPacked projCircuit) y.mem ∧
    ∀ a, (a < (layout projCircuit).base ∨ workEnd projCircuit ≤ a) →
      y.mem a = (Data.init (encode projCircuit) : Data 24).mem a :=
  exec_initCode _ ⟨by decide, by decide⟩

/-- The same for the circuit with no inputs (the `phi` loop runs no iteration), at width `7`. -/
example : ∃ y, ExecWithin 7 initCode (.init (encode constCircuit)) y (initTime constCircuit) ∧
    Stored (layout constCircuit) (initialPacked constCircuit) y.mem := by
  obtain ⟨y, he, hs, -⟩ := exec_initCode constCircuit (w := 7) ⟨by decide, by decide⟩
  exact ⟨y, he, hs⟩

/-- The same for `mixCircuit`, at width `7`, in at most `6 · 2 + 73 · 3 + 50 = 281`
instructions. -/
example : ∃ y, ExecWithin 7 initCode (.init (encode mixCircuit)) y 281 ∧
    Stored (layout mixCircuit) (initialPacked mixCircuit) y.mem := by
  obtain ⟨y, he, hs, -⟩ := exec_initCode mixCircuit (w := 7) ⟨by decide, by decide⟩
  exact ⟨y, he, hs⟩

end CslibFrontierTests.Refuter4nInputLayout
