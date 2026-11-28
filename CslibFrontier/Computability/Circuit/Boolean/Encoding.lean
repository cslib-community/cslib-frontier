/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Boolean.Basic
public import CslibFrontier.Computability.Circuit.Encoding.Basic

/-!
# Binary encodings of De Morgan circuits

`CslibFrontier.Computability.Circuit.Encoding.Basic` defines signature-polymorphic gate-list coding
(`Line.code`, `Program.code`, `Circuit.code`), well-formedness and decoding (`Program.IsCodeFrom`,
`Program.ofCode`, `Circuit.ofCode`), and binary serialization (`Circuit.encGate`,
`Circuit.encCode`, `Circuit.encCircuit`).

For the De Morgan basis, an operation is written as its number `Boolean.Op.toNat` in unary and a
wire number in binary (`Boolean.encGate`). A circuit with `n` inputs and `m` outputs is encoded by
`n` in unary, then its framed gates in program order, then its framed output wires
(`Boolean.encCircuit`) [Arora and Barak, Section 6.1][AroraBarak09].

## Main definitions

* `Cslib.Circuits.Boolean.Op.toNat`, `Cslib.Circuits.Boolean.encOp`,
  `Cslib.Circuits.Boolean.encGate`, `Cslib.Circuits.Boolean.encCode`,
  `Cslib.Circuits.Boolean.encCircuit`: binary encodings of De Morgan operations, gates, codes, and
  circuits.

## Main results

* `Cslib.Circuits.Boolean.le_length_encCircuit`: the encoding of a De Morgan circuit is at least as
  long as its number of inputs.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM

/-- The number of an operation of the De Morgan basis: `0` and `1` for the constants `false` and
`true`, then `2`, `3`, `4` for NOT, AND, OR. -/
def Op.toNat : Op → ℕ
  | .const false => 0
  | .const true => 1
  | .not => 2
  | .and => 3
  | .or => 4

/-- The numbering `Op.toNat` of De Morgan operations is injective. -/
theorem Op.toNat_injective : Function.Injective Op.toNat := by
  decide

/-- Operations of the De Morgan basis encoded by their number `Op.toNat` in unary. -/
def encOp : Op ↪ List Bool :=
  ⟨fun op => encUnary op.toNat, encUnary.injective.comp Op.toNat_injective⟩

/-- A gate of the De Morgan basis as data: its operation by `encOp`, then the framed binary numbers
of the wires it reads. -/
abbrev encGate : Op × List ℕ ↪ List Bool := Circuit.encGate encOp

/-- The code of a De Morgan circuit: its framed gates in program order, then its framed output
wires, all wire numbers in binary. -/
abbrev encCode : List (Op × List ℕ) × List ℕ ↪ List Bool := Circuit.encCode encOp

/-- **Binary encoding of De Morgan circuits** with `m` outputs and any number `n` of inputs: `n` in
unary, then the code of the circuit (`encCode`), that is, its gates in program order and its output
wires, with wire numbers in binary. -/
abbrev encCircuit (m : ℕ) : (Σ n, Circuit signature n m) ↪ List Bool :=
  Circuit.encCircuit (σ := signature) encOp m

/-- Unfolding formula for `encCircuit m c`. -/
theorem encCircuit_apply {m : ℕ} (c : Σ n, Circuit signature n m) :
    encCircuit m c = encPair encUnary encCode (c.1, c.2.code) := rfl

/-- The encoding of a circuit is at least as long as its number of inputs. -/
theorem le_length_encCircuit {m : ℕ} (c : Σ n, Circuit signature n m) :
    c.1 ≤ (encCircuit m c).length :=
  Circuit.le_length_encCircuit (σ := signature) encOp c

end Cslib.Circuits.Boolean
