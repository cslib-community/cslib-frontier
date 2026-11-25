/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Encoding
public import CslibFrontier.Computability.Circuit.Boolean.Unbounded
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Encodings of circuits with unbounded fan-in

An operation of the unbounded fan-in basis is written as a number in unary: `0` for negation,
`2 m + 1` for the conjunction of `m` arguments and `2 m + 2` for their disjunction
(`Unbounded.Op.toNat`). Circuits are then encoded by the encoding of circuits over an arbitrary
signature (`Cslib.Circuits.Circuit.encCircuit`): the number of inputs in unary, the gates in program
order with wire numbers in binary, and the output wires. The arity of a gate is written in unary,
but a gate of a circuit lists as many wires as its arity, so the encoding of a circuit is at most a
constant factor longer than with the arity in binary.

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.Op.toNat`, `Cslib.Circuits.Boolean.Unbounded.encOp`: the
  operations in unary.
* `Cslib.Circuits.Boolean.Unbounded.encCircuit`: circuits over the unbounded fan-in basis.
* `Cslib.Circuits.Boolean.Unbounded.ExtOp.toNat`, `Cslib.Circuits.Boolean.Unbounded.encExtOp`,
  `Cslib.Circuits.Boolean.Unbounded.encExtCircuit`: unary operation encoding and binary circuit
  encoding for the extended unbounded fan-in basis (`Unbounded.extSignature`).

## Main results

* `Cslib.Circuits.Boolean.Unbounded.Op.toNat_injective`,
  `Cslib.Circuits.Boolean.Unbounded.ExtOp.toNat_injective`: the numberings are injective.
* `Cslib.Circuits.Boolean.Unbounded.computableInPolyTime_and`,
  `Cslib.Circuits.Boolean.Unbounded.computableInPolyTime_or`,
  `Cslib.Circuits.Boolean.Unbounded.computableInPolyTime_extOp_toNat`,
  `Cslib.Circuits.Boolean.Unbounded.computableInPolyTime_extOr`: polynomial-time operation
  encoding and decoding.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Unbounded

open Turing.MultiTapeTM

/-- The number of an operation: `0` for negation, `2 m + 1` for the conjunction of `m` arguments
and `2 m + 2` for their disjunction. -/
def Op.toNat : Op → ℕ
  | .not => 0
  | .and m => 2 * m + 1
  | .or m => 2 * m + 2

/-- The numbering `Op.toNat` is injective. -/
theorem Op.toNat_injective : Function.Injective Op.toNat := by
  rintro (_ | m | m) (_ | m' | m') h <;> simp only [Op.toNat] at h <;> first | rfl | omega |
    (congr 1; omega)

/-- Operations of the unbounded fan-in basis, encoded by their number `Op.toNat` in unary. -/
def encOp : Op ↪ List Bool :=
  ⟨fun op => encUnary op.toNat, encUnary.injective.comp Op.toNat_injective⟩

/-- **Binary encoding of circuits over the unbounded fan-in basis** with `m` outputs: the number of
inputs in unary, then the gates in program order and the output wires, with wire numbers in binary
(`Cslib.Circuits.Circuit.encCircuit`). -/
abbrev encCircuit (m : ℕ) : (Σ n, Circuit signature n m) ↪ List Bool :=
  Circuit.encCircuit (σ := signature) encOp m

/-- Writing the conjunction of `m` arguments is polynomial-time from `m` in unary. -/
theorem computableInPolyTime_and :
    ComputableInPolyTime (fun m : ℕ => (Op.and m : Op)) encUnary encOp :=
  ComputableInPolyTime.of_enc_eq (f := fun m : ℕ => 2 * m + 1) (by fun_prop) fun _ => rfl

/-- Writing the disjunction of `m` arguments is polynomial-time from `m` in unary. -/
theorem computableInPolyTime_or :
    ComputableInPolyTime (fun m : ℕ => (Op.or m : Op)) encUnary encOp :=
  ComputableInPolyTime.of_enc_eq (f := fun m : ℕ => 2 * m + 2) (by fun_prop) fun _ => rfl

/-! ### Extended unbounded fan-in basis (`ExtOp`) -/

/-- The number of an extended operation: `0` for negation, `3 m + 1` for conjunction of `m`
arguments, `3 m + 2` for disjunction of `m` arguments, and `3 m + 3` for the extra gate (such as
`MOD_q` or `MAJ`) of `m` arguments. -/
def ExtOp.toNat : ExtOp → ℕ
  | .ac .not => 0
  | .ac (.and m) => 3 * m + 1
  | .ac (.or m) => 3 * m + 2
  | .gate m => 3 * m + 3

/-- The numbering `ExtOp.toNat` is injective. -/
theorem ExtOp.toNat_injective : Function.Injective ExtOp.toNat := by
  rintro ((_ | m | m) | m) ((_ | m' | m') | m') h <;>
    simp only [ExtOp.toNat] at h <;>
    first | rfl | omega | (congr 1; omega) | (congr 1; congr 1; omega)

/-- Operations of the extended unbounded fan-in basis, encoded by their number `ExtOp.toNat` in
unary. -/
def encExtOp : ExtOp ↪ List Bool :=
  ⟨fun op => encUnary op.toNat, encUnary.injective.comp ExtOp.toNat_injective⟩

/-- **Binary encoding of circuits over the extended unbounded fan-in basis**
(`Unbounded.extSignature`) with `m` outputs: the number of inputs in unary, then the gates in
program order and the output wires, with wire numbers in binary
(`Cslib.Circuits.Circuit.encCircuit`). -/
abbrev encExtCircuit (m : ℕ) : (Σ n, Circuit extSignature n m) ↪ List Bool :=
  Circuit.encCircuit (σ := extSignature) encExtOp m

/-- Reading the unary code number of an extended operation is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_extOp_toNat :
    ComputableInPolyTime ExtOp.toNat encExtOp encUnary :=
  ComputableInPolyTime.of_enc_eq (f := id) (by fun_prop) fun _ => rfl

/-- Writing the disjunction of `m` arguments in `ExtOp` is polynomial-time from `m` in unary. -/
theorem computableInPolyTime_extOr :
    ComputableInPolyTime (fun m : ℕ => (ExtOp.ac (.or m) : ExtOp)) encUnary encExtOp :=
  ComputableInPolyTime.of_enc_eq (f := fun m : ℕ => 3 * m + 2) (by fun_prop) fun _ => rfl

end Cslib.Circuits.Boolean.Unbounded
