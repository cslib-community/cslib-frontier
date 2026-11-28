/-
Copyright (c) 2026 Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Anderson
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

/-! The input layout: `[n, s]`, three words per line, the output wire word. -/

#guard encode projCircuit == [2, 0, 0]
#guard encode xor3Circuit == [3, 1, 6, 0, 1, 3]
#guard encode mixCircuit == [2, 3, 3, 0, 0, 8, 2, 1, 17, 0, 0, 3]

/-! The decoder: literal codes and gate rows. `xor3`: gate `3` with row `⟨6, 2, 3⟩` and code
`2 · (3 + 2) = 10`. `mix`: `¬x₀` has code `2 · 2 + 1 = 5`; the AND with the absorbed negation has
truth table `0010₂ = 2`, row `⟨2, 2, 3⟩` and code `10`; the constant `true` has code `2`. -/

#guard decodeLines 2 (progTriples projCircuit.program) == []
#guard decodeLines 3 (progTriples xor3Circuit.program) == [(10, some ⟨6, 2, 3⟩)]
#guard decodeLines 2 (progTriples mixCircuit.program) ==
  [(5, none), (10, some ⟨2, 2, 3⟩), (2, none)]

/-! The decoded rows and output agree with `initialPacked` (block 1). -/

#guard ((decodeLines 2 (progTriples mixCircuit.program)).getD 1 (0, none)).2.getD ⟨0, 0, 0⟩ ==
  (initialPacked mixCircuit).gateRows.getD 3 ⟨0, 0, 0⟩
#guard wireLit 2 ((decodeLines 2 (progTriples mixCircuit.program)).map Prod.fst)
  (wireCode (mixCircuit.outputs 0)) == (initialPacked mixCircuit).out

/-- Whether `mem` holds the words of `P` at the addresses of `L` (`Stored`, as a check). -/
def storedB (L : Layout) (P : PackedState) (mem : ℕ → ℕ) : Bool :=
  mem L.base == P.params && mem (L.base + 1) == P.aux && mem (L.base + 2) == P.gates &&
    mem (L.base + 3) == P.out && mem (L.base + 4) == P.pairs.length &&
    ((List.range P.gateRows.length).all fun J =>
      mem (L.rowAddr J 0) == (P.gateRows.getD J ⟨0, 0, 0⟩).tt &&
      mem (L.rowAddr J 1) == (P.gateRows.getD J ⟨0, 0, 0⟩).left &&
      mem (L.rowAddr J 2) == (P.gateRows.getD J ⟨0, 0, 0⟩).right) &&
    ((List.range P.eqnRows.length).all fun e => mem (L.eqnAddr e) == P.eqnRows.getD e 0) &&
    ((List.range P.phiRows.length).all fun i => mem (L.phiAddr i) == P.phiRows.getD i 0)

/-- Run `initCode` on the input of `C` at width `w` and check the stored state and the step
count against `initTime C`. -/
def runCheck {n : ℕ} (C : Circuit (fullSignature 2 Bool) n 1) (w : ℕ) : Bool :=
  match initCode.eval w 100 (.init (encode C) : Data 24) with
  | some (y, t) => storedB (layout C) (initialPacked C) y.mem && decide (t ≤ initTime C)
  | none => false

/-! Executions of the program: zero lines (the line loop runs no iteration), one binary line, and
unary, binary and constant lines. -/

#guard runCheck projCircuit 7
#guard runCheck xor3Circuit 9
#guard runCheck mixCircuit 10

/-- The width `n + C.size + 5 = 9` is admitted for `xor3Circuit` (module client of
`fitsWidth_of_le`). -/
example : FitsWidth xor3Circuit 9 := fitsWidth_of_le _ (by decide)

/-- At that width every input word fits (module client of `inputFits_encode`). -/
example : InputFits 9 (encode xor3Circuit) := inputFits_encode _ (fitsWidth_of_le _ (by decide))

/-- The charged decoding stores the packed initial state (module client of `exec_initCode`), for
the `0`-line circuit. -/
example : ∃ y, ExecWithin 7 initCode (.init (encode projCircuit)) y (initTime projCircuit) ∧
    Stored (layout projCircuit) (initialPacked projCircuit) y.mem ∧
    ∀ a, (a < (layout projCircuit).base ∨ workEnd projCircuit ≤ a) →
      y.mem a = (Data.init (encode projCircuit) : Data 24).mem a :=
  exec_initCode _ (fitsWidth_of_le _ (by decide))

/-- The same for `mixCircuit`, at width `10`, in at most `6 · 2 + 73 · 3 + 50 = 281`
instructions. -/
example : ∃ y, ExecWithin 10 initCode (.init (encode mixCircuit)) y 281 ∧
    Stored (layout mixCircuit) (initialPacked mixCircuit) y.mem := by
  obtain ⟨y, he, hs, -⟩ := exec_initCode mixCircuit (w := 10) (fitsWidth_of_le _ (by decide))
  exact ⟨y, he, hs⟩

/-- The decoded gate rows are the rows of the gates of the initial state (module client of
`snd_getD_decodeLines`). -/
example : ((decodeLines 2 (progTriples mixCircuit.program)).getD 1 (0, none)).2 =
    if 2 + 1 ∈ (initialState mixCircuit).gates then
      some (rowOf ((initialState mixCircuit).gate (2 + 1))) else none :=
  snd_getD_decodeLines mixCircuit (by decide)

end CslibFrontierTests.Refuter4nInputLayout
