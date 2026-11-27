/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Hash.Keccak
public import CslibFrontier.Computability.Circuit.Boolean.NativeEvaluation
public import CslibFrontier.Computability.Circuit.Boolean.Parity
public import CslibFrontier.Computability.Circuit.Pi
import CslibFrontier.Foundations.Data.BitString.Block
import Batteries.Data.Vector.Lemmas
import CslibFrontier.Tactic.FinIndex

/-!
# Retained Boolean circuit for Keccak-p[1600, 24]

This module constructs Keccak-p[1600, 24] directly over the De Morgan basis and compiles that
fixed circuit with the retained native circuit evaluator. State bit `64 * (5 * y + x) + z` is
exactly FIPS 202's `A[x, y, z]`. The circuit reuses the executable `theta`, `rho`, `pi`, `chi`,
`iota`, and round-constant semantics from `CslibFrontier.Crypto.Primitives.Hash.Keccak`; it does
not introduce a second permutation or sponge specification.

`keccakP1600Compiler` retains its multitape machine and the evaluator's exact input, output, time,
workspace, and complete generated transition-table `staticBits` coordinates. The general theorem
`NativeCompiler.staticBits_eq_descLen` identifies that last coordinate with the first-order
description length. No finite-function or truth-table compiler is used.

## Main definitions

* `Cslib.Crypto.Keccak.stateBits`, `stateOfBits`: the FIPS flat 1600-bit state view.
* `Cslib.Crypto.Keccak.keccakP1600Circuit`: the direct 24-round De Morgan circuit.
* `Cslib.Crypto.Keccak.keccakP1600Compiler`: its retained native multitape compiler.

## Main results

* `Cslib.Crypto.Keccak.stateBits_stateOfBits`, `stateOfBits_stateBits`: the flat view is exact.
* `Cslib.Crypto.Keccak.eval_keccakP1600Circuit`: all-input refinement to the executable
  Keccak-p[1600, 24] semantics.
-/

public section

namespace Cslib.Crypto.Keccak

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM
open Turing.MultiTapeTM.Internal
open Turing.MultiTapeTM.Internal.NativeCompiler

/-- Flatten a Keccak-p[1600] lane array in FIPS 202 order: lane `5 * y + x`, then its 64
least-significant-bit-first coordinates. -/
@[expose] def stateBits (A : State) : BitString 1600 := fun i =>
  (BitString.blocksEquiv (α := Bool) (m := 25) (k := 64)).symm
    (fun lane z => (A.get lane).getLsbD z.val) i

/-- Reconstruct the Keccak-p[1600] lane array from its FIPS 202 flat bit order. -/
@[expose] def stateOfBits (bits : BitString 1600) : State :=
  Vector.ofFn fun lane => laneOfBits (BitString.block (m := 25) (k := 64) bits lane)

@[simp] private theorem block_stateBits (A : State) :
    BitString.block (m := 25) (k := 64) (stateBits A) =
      fun lane z => (A.get lane).getLsbD z.val := by
  unfold stateBits
  exact BitString.block_blocksEquiv_symm _

@[simp] private theorem get_stateOfBits (bits : BitString 1600) (lane : Fin 25) :
    (stateOfBits bits).get lane = laneOfBits (BitString.block bits lane) := by
  unfold stateOfBits
  exact Vector.get_ofFn _ _

/-- Flattening a reconstructed Keccak state returns every input bit. -/
@[simp] theorem stateBits_stateOfBits (bits : BitString 1600) :
    stateBits (stateOfBits bits) = bits := by
  apply (BitString.blocksEquiv (α := Bool) (m := 25) (k := 64)).injective
  funext lane z
  change BitString.block (stateBits (stateOfBits bits)) lane z = BitString.block bits lane z
  simp only [block_stateBits, get_stateOfBits, getLsbD_laneOfBits _ _ z.isLt]

/-- Reconstructing a flattened Keccak state returns every lane. -/
@[simp] theorem stateOfBits_stateBits (A : State) : stateOfBits (stateBits A) = A := by
  refine Vector.ext fun lane hlane => ?_
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  change ((stateOfBits (stateBits A)).get ⟨lane, hlane⟩).getLsbD z =
    (A.get ⟨lane, hlane⟩).getLsbD z
  rw [get_stateOfBits, getLsbD_laneOfBits _ _ hz, block_stateBits]

local macro "keccakBitIndex%(" x:term "," y:term "," z:term ")" : term =>
  `((⟨64 * (5 * ($y).val + ($x).val) + ($z).val, by omega⟩ : Fin 1600))

local macro "keccakFlatX%(" i:term ")" : term =>
  `((coordinate (($i).val / 64) : Fin 5))

local macro "keccakFlatY%(" i:term ")" : term =>
  `((⟨($i).val / 64 / 5, by omega⟩ : Fin 5))

local macro "keccakFlatZ%(" i:term ")" : term =>
  `((⟨($i).val % 64, Nat.mod_lt _ (by decide)⟩ : Fin 64))

local macro "keccakRotateSource%(" r:term "," z:term ")" : term =>
  `((⟨if ($z).val < $r % 64 then 64 - $r % 64 + ($z).val else ($z).val - $r % 64, by
      split <;> omega⟩ : Fin 64))

local macro "keccakXorCircuit%" : term =>
  `((⟨Program.empty.appendXor (.input 0) (.input 1), fun _ => .gate (Fin.last 3)⟩ :
    Circuit signature 2 1))

local macro "keccakXor3Circuit%" : term =>
  `(let first : Circuit signature 3 1 :=
      Circuit.wiring signature fun _ : Fin 1 => (0 : Fin 3)
    let lastTwo : Circuit signature 3 1 := (keccakXorCircuit%).comp
      (Circuit.wiring signature fun i : Fin 2 => i.succ)
    ((keccakXorCircuit%).comp (first.append lastTwo) : Circuit signature 3 1))

local macro "keccakXor5Circuit%" : term =>
  `(let first : Circuit signature 5 1 := (keccakXorCircuit%).comp
      (Circuit.wiring signature fun i : Fin 2 => i.castLE (by omega))
    let second : Circuit signature 5 1 := (keccakXorCircuit%).comp
      (Circuit.wiring signature fun i : Fin 2 => ⟨2 + i, by omega⟩)
    let firstFour : Circuit signature 5 1 :=
      (keccakXorCircuit%).comp (first.append second)
    let last : Circuit signature 5 1 :=
      Circuit.wiring signature fun _ : Fin 1 => (4 : Fin 5)
    ((keccakXorCircuit%).comp (firstFour.append last) : Circuit signature 5 1))

local macro "keccakChiBitCircuit%" : term =>
  `(let first : Circuit signature 3 1 :=
      Circuit.wiring signature fun _ : Fin 1 => (0 : Fin 3)
    let negSecond : Circuit signature 3 1 :=
      (Circuit.oneGate (σ := signature) Boolean.Op.not fun _ => (0 : Fin 1)).comp
      (Circuit.wiring signature fun _ : Fin 1 => (1 : Fin 3))
    let third : Circuit signature 3 1 :=
      Circuit.wiring signature fun _ : Fin 1 => (2 : Fin 3)
    let product : Circuit signature 3 1 :=
      (Circuit.oneGate (σ := signature) Boolean.Op.and id).comp (negSecond.append third)
    ((keccakXorCircuit%).comp (first.append product) : Circuit signature 3 1))

local macro "keccakNotCircuit%" : term =>
  `((Circuit.oneGate (σ := signature) Boolean.Op.not id : Circuit signature 1 1))

local macro "keccakColumnBitCircuit%(" x:term "," z:term ")" : term =>
  `((keccakXor5Circuit%).comp
    (Circuit.wiring signature (fun y : Fin 5 => keccakBitIndex%($x, y, $z))))

local macro "keccakThetaBitCircuit%(" x:term "," y:term "," z:term ")" : term =>
  `(let current : Circuit signature 1600 1 :=
      Circuit.wiring signature fun _ : Fin 1 => keccakBitIndex%($x, $y, $z)
    let prior : Circuit signature 1600 1 :=
      keccakColumnBitCircuit%(coordinate (($x).val + 4), $z)
    let next : Circuit signature 1600 1 := keccakColumnBitCircuit%(
      coordinate (($x).val + 1), keccakRotateSource%(1, $z))
    ((keccakXor3Circuit%).comp (current.append (prior.append next)) :
      Circuit signature 1600 1))

local macro "keccakThetaCircuit%" : term =>
  `((Circuit.pi fun i => keccakThetaBitCircuit%(
    keccakFlatX%(i), keccakFlatY%(i), keccakFlatZ%(i)) :
      Circuit signature 1600 1600))

local macro "keccakRhoCircuit%" : term =>
  `((Circuit.wiring signature fun i =>
    keccakBitIndex%(keccakFlatX%(i), keccakFlatY%(i),
      keccakRotateSource%(rotationOffset (keccakFlatX%(i)) (keccakFlatY%(i)),
        keccakFlatZ%(i))) : Circuit signature 1600 1600))

local macro "keccakPiCircuit%" : term =>
  `((Circuit.wiring signature fun i =>
    keccakBitIndex%(
      coordinate ((keccakFlatX%(i)).val + 3 * (keccakFlatY%(i)).val),
      keccakFlatX%(i), keccakFlatZ%(i)) : Circuit signature 1600 1600))

local macro "keccakChiCircuit%" : term =>
  `((Circuit.pi fun i => (keccakChiBitCircuit%).comp
    (Circuit.wiring signature fun j : Fin 3 =>
      match j.val with
      | 0 => keccakBitIndex%(keccakFlatX%(i), keccakFlatY%(i), keccakFlatZ%(i))
      | 1 => keccakBitIndex%(
        coordinate ((keccakFlatX%(i)).val + 1), keccakFlatY%(i), keccakFlatZ%(i))
      | _ => keccakBitIndex%(
        coordinate ((keccakFlatX%(i)).val + 2), keccakFlatY%(i), keccakFlatZ%(i))) :
      Circuit signature 1600 1600))

local macro "keccakIotaBitCircuit%(" constant:term "," x:term "," y:term "," z:term ")" : term =>
  `(let input : Circuit signature 1600 1 :=
      Circuit.wiring signature fun _ : Fin 1 => keccakBitIndex%($x, $y, $z)
    (if 5 * ($y).val + ($x).val = 0 && ($constant).getLsbD ($z).val then
      (keccakNotCircuit%).comp input
    else input : Circuit signature 1600 1))

local macro "keccakIotaCircuit%(" constant:term ")" : term =>
  `((Circuit.pi fun i => keccakIotaBitCircuit%(
    $constant, keccakFlatX%(i), keccakFlatY%(i), keccakFlatZ%(i)) :
      Circuit signature 1600 1600))

local macro "keccakRoundCircuit%(" constant:term ")" : term =>
  `(((keccakIotaCircuit%($constant)).comp
    ((keccakChiCircuit%).comp
      ((keccakPiCircuit%).comp ((keccakRhoCircuit%).comp (keccakThetaCircuit%)))) :
        Circuit signature 1600 1600))

private def bitIndex (x y : Fin 5) (z : Fin 64) : Fin 1600 :=
  keccakBitIndex%(x, y, z)

private theorem stateBits_bitIndex (A : State) (x y : Fin 5) (z : Fin 64) :
    stateBits A (bitIndex x y z) = (getLane A x y).getLsbD z.val := by
  have hindex : bitIndex x y z = finProdFinEquiv (laneIndex x y, z) := by
    apply Fin.ext
    change 64 * (5 * y.val + x.val) + z.val = z.val + 64 * (5 * y.val + x.val)
    omega
  rw [hindex]
  change BitString.block (stateBits A) (laneIndex x y) z = _
  rw [block_stateBits]
  rfl

private def flatX (i : Fin 1600) : Fin 5 := keccakFlatX%(i)

private def flatY (i : Fin 1600) : Fin 5 := keccakFlatY%(i)

private def flatZ (i : Fin 1600) : Fin 64 := keccakFlatZ%(i)

private theorem bitIndex_flat (i : Fin 1600) : bitIndex (flatX i) (flatY i) (flatZ i) = i := by
  fin_index [bitIndex, flatX, flatY, flatZ, coordinate]

@[simp] private theorem flatX_bitIndex (x y : Fin 5) (z : Fin 64) :
    flatX (bitIndex x y z) = x := by
  fin_index [flatX, bitIndex, coordinate]

@[simp] private theorem flatY_bitIndex (x y : Fin 5) (z : Fin 64) :
    flatY (bitIndex x y z) = y := by
  fin_index [flatY, bitIndex]

@[simp] private theorem flatZ_bitIndex (x y : Fin 5) (z : Fin 64) :
    flatZ (bitIndex x y z) = z := by
  fin_index [flatZ, bitIndex]

@[simp] private theorem coordinate_laneIndex (x y : Fin 5) :
    coordinate (laneIndex x y).val = x := by
  fin_index [coordinate, laneIndex]

@[simp] private theorem laneIndex_div_five (x y : Fin 5) :
    (laneIndex x y).val / 5 = y.val := by
  unfold laneIndex
  change (5 * y.val + x.val) / 5 = y.val
  omega

private def rotateSource (r : ℕ) (z : Fin 64) : Fin 64 :=
  keccakRotateSource%(r, z)

private theorem getLsbD_rotateLeft_eq (lane : Lane) (r : ℕ) (z : Fin 64) :
    (lane.rotateLeft r).getLsbD z.val = lane.getLsbD (rotateSource r z).val := by
  rw [BitVec.getLsbD_rotateLeft]
  simp only [z.isLt, decide_true, Bool.true_and]
  unfold rotateSource
  split <;> rfl

@[simp] private theorem finAppend_one_one_zero {α : Type*} (u v : Fin 1 → α) :
    Fin.append u v (0 : Fin 2) = u 0 := rfl

@[simp] private theorem finAppend_one_one_one {α : Type*} (u v : Fin 1 → α) :
    Fin.append u v (1 : Fin 2) = v 0 := rfl

private def xorCircuit : Circuit signature 2 1 :=
  keccakXorCircuit%

@[simp] private theorem eval_xorCircuit (x : BitString 2) :
    xorCircuit.eval interpretation x 0 = (x 0 ^^ x 1) :=
  Program.trace_appendXor Program.empty (.input 0) (.input 1) x

private def xor3Circuit : Circuit signature 3 1 :=
  let first := Circuit.wiring signature fun _ : Fin 1 => (0 : Fin 3)
  let lastTwo := xorCircuit.comp (Circuit.wiring signature fun i : Fin 2 => i.succ)
  xorCircuit.comp (first.append lastTwo)

@[simp] private theorem eval_xor3Circuit (x : BitString 3) :
    xor3Circuit.eval interpretation x 0 = (x 0 ^^ (x 1 ^^ x 2)) := by
  rw [xor3Circuit, Circuit.eval_comp, eval_xorCircuit, Circuit.eval_append]
  simp only [Circuit.eval_wiring, Function.comp_apply, finAppend_one_one_zero,
    finAppend_one_one_one, Circuit.eval_comp, eval_xorCircuit]
  norm_num [Fin.ext_iff]

private def xor5Circuit : Circuit signature 5 1 :=
  let first := xorCircuit.comp
    (Circuit.wiring signature fun i : Fin 2 => i.castLE (by omega))
  let second := xorCircuit.comp
    (Circuit.wiring signature fun i : Fin 2 => ⟨2 + i, by omega⟩)
  let firstFour := xorCircuit.comp (first.append second)
  let last := Circuit.wiring signature fun _ : Fin 1 => (4 : Fin 5)
  xorCircuit.comp (firstFour.append last)

@[simp] private theorem eval_xor5Circuit (x : BitString 5) :
    xor5Circuit.eval interpretation x 0 = (((x 0 ^^ x 1) ^^ (x 2 ^^ x 3)) ^^ x 4) := by
  rw [xor5Circuit, Circuit.eval_comp, eval_xorCircuit, Circuit.eval_append]
  simp only [Circuit.eval_wiring, Function.comp_apply, finAppend_one_one_zero,
    finAppend_one_one_one, Circuit.eval_comp, eval_xorCircuit, Circuit.eval_append]
  norm_num [Fin.ext_iff]

private def chiBitCircuit : Circuit signature 3 1 :=
  let first := Circuit.wiring signature fun _ : Fin 1 => (0 : Fin 3)
  let negSecond := (Circuit.oneGate (σ := signature) Boolean.Op.not id).comp
    (Circuit.wiring signature fun _ : Fin 1 => (1 : Fin 3))
  let third := Circuit.wiring signature fun _ : Fin 1 => (2 : Fin 3)
  let product := (Circuit.oneGate (σ := signature) Boolean.Op.and id).comp
    (negSecond.append third)
  xorCircuit.comp (first.append product)

@[simp] private theorem eval_chiBitCircuit (x : BitString 3) :
    chiBitCircuit.eval interpretation x 0 = (x 0 ^^ (!x 1 && x 2)) := by
  rw [chiBitCircuit, Circuit.eval_comp, eval_xorCircuit, Circuit.eval_append]
  simp only [Circuit.eval_wiring, Function.comp_apply, finAppend_one_one_zero,
    finAppend_one_one_one, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_oneGate,
    interpretation, id_eq]

private def notCircuit : Circuit signature 1 1 :=
  Circuit.oneGate Boolean.Op.not id

@[simp] private theorem eval_notCircuit (x : BitString 1) :
    notCircuit.eval interpretation x 0 = !x 0 := by
  rfl

private def columnBitCircuit (x : Fin 5) (z : Fin 64) : Circuit signature 1600 1 :=
  xor5Circuit.comp (Circuit.wiring signature fun y : Fin 5 => bitIndex x y z)

@[simp] private theorem eval_columnBitCircuit (A : State) (x : Fin 5) (z : Fin 64) :
    (columnBitCircuit x z).eval interpretation (stateBits A) 0 =
      ((((getLane A x 0).getLsbD z.val ^^ (getLane A x 1).getLsbD z.val) ^^
        (getLane A x 2).getLsbD z.val ^^ (getLane A x 3).getLsbD z.val) ^^
        (getLane A x 4).getLsbD z.val) := by
  simp [columnBitCircuit, stateBits_bitIndex]

private def thetaBitCircuit (x y : Fin 5) (z : Fin 64) : Circuit signature 1600 1 :=
  let current := Circuit.wiring signature fun _ : Fin 1 => bitIndex x y z
  let prior := columnBitCircuit (coordinate (x.val + 4)) z
  let next := columnBitCircuit (coordinate (x.val + 1)) (rotateSource 1 z)
  xor3Circuit.comp (current.append (prior.append next))

private def thetaCircuit : Circuit signature 1600 1600 :=
  Circuit.pi fun i => thetaBitCircuit (flatX i) (flatY i) (flatZ i)

private def rhoCircuit : Circuit signature 1600 1600 :=
  Circuit.wiring signature fun i =>
    bitIndex (flatX i) (flatY i)
      (rotateSource (rotationOffset (flatX i) (flatY i)) (flatZ i))

private def piCircuit : Circuit signature 1600 1600 :=
  Circuit.wiring signature fun i =>
    bitIndex (coordinate ((flatX i).val + 3 * (flatY i).val)) (flatX i) (flatZ i)

private def chiCircuit : Circuit signature 1600 1600 :=
  Circuit.pi fun i => chiBitCircuit.comp (Circuit.wiring signature fun j : Fin 3 =>
    match j.val with
    | 0 => bitIndex (flatX i) (flatY i) (flatZ i)
    | 1 => bitIndex (coordinate ((flatX i).val + 1)) (flatY i) (flatZ i)
    | _ => bitIndex (coordinate ((flatX i).val + 2)) (flatY i) (flatZ i))

private def iotaBitCircuit (constant : Lane) (x y : Fin 5) (z : Fin 64) :
    Circuit signature 1600 1 :=
  let input := Circuit.wiring signature fun _ : Fin 1 => bitIndex x y z
  if 5 * y.val + x.val = 0 && constant.getLsbD z.val then notCircuit.comp input else input

private def iotaCircuit (constant : Lane) : Circuit signature 1600 1600 :=
  Circuit.pi fun i => iotaBitCircuit constant (flatX i) (flatY i) (flatZ i)

private def roundCircuit (constant : Lane) : Circuit signature 1600 1600 :=
  (iotaCircuit constant).comp
    (chiCircuit.comp (piCircuit.comp (rhoCircuit.comp thetaCircuit)))

/-- The direct De Morgan circuit for the 24 FIPS 202 Keccak-p[1600] rounds. -/
@[expose] def keccakP1600Circuit : Circuit signature 1600 1600 :=
  roundConstants.foldl (fun circuit constant => (keccakRoundCircuit%(constant)).comp circuit)
    (Circuit.id signature 1600)

private theorem keccakP1600Circuit_eq : keccakP1600Circuit =
    roundConstants.foldl (fun circuit constant => (roundCircuit constant).comp circuit)
      (Circuit.id signature 1600) := by
  rfl

private theorem eval_thetaBitCircuit (A : State) (x y : Fin 5) (z : Fin 64) :
    (thetaBitCircuit x y z).eval interpretation (stateBits A) 0 =
      stateBits (theta A) (bitIndex x y z) := by
  simp only [thetaBitCircuit, Circuit.eval_comp, Circuit.eval_append, eval_xor3Circuit,
    Circuit.eval_wiring]
  change (stateBits A (bitIndex x y z) ^^
      ((columnBitCircuit (coordinate (x.val + 4)) z).eval interpretation (stateBits A) 0 ^^
        (columnBitCircuit (coordinate (x.val + 1)) (rotateSource 1 z)).eval
          interpretation (stateBits A) 0)) = _
  rw [stateBits_bitIndex, stateBits_bitIndex, eval_columnBitCircuit, eval_columnBitCircuit]
  simp only [theta, getLane, Vector.get_ofFn, coordinate_laneIndex,
    BitVec.getLsbD_xor, getLsbD_rotateLeft_eq, Bool.xor_assoc]

private theorem eval_thetaCircuit (A : State) :
    thetaCircuit.eval interpretation (stateBits A) = stateBits (theta A) := by
  funext i
  rw [thetaCircuit, Circuit.eval_pi]
  change (thetaBitCircuit (flatX i) (flatY i) (flatZ i)).eval
      interpretation (stateBits A) 0 = _
  rw [eval_thetaBitCircuit]
  exact congrArg (stateBits (theta A)) (bitIndex_flat i)

private theorem eval_rhoCircuit_bit (A : State) (x y : Fin 5) (z : Fin 64) :
    rhoCircuit.eval interpretation (stateBits A) (bitIndex x y z) =
      stateBits (rho A) (bitIndex x y z) := by
  simp only [rhoCircuit, Circuit.eval_wiring, Function.comp_apply, flatX_bitIndex,
    flatY_bitIndex, flatZ_bitIndex, stateBits_bitIndex]
  unfold rho getLane
  rw [Vector.get_ofFn, coordinate_laneIndex]
  have hy : (⟨(laneIndex x y).val / 5, by omega⟩ : Fin 5) = y :=
    Fin.ext (laneIndex_div_five x y)
  simp only [hy]
  exact (getLsbD_rotateLeft_eq (A.get (laneIndex x y)) (rotationOffset x y) z).symm

private theorem eval_rhoCircuit (A : State) :
    rhoCircuit.eval interpretation (stateBits A) = stateBits (rho A) := by
  funext i
  calc
    rhoCircuit.eval interpretation (stateBits A) i =
        rhoCircuit.eval interpretation (stateBits A)
          (bitIndex (flatX i) (flatY i) (flatZ i)) :=
      congrArg (rhoCircuit.eval interpretation (stateBits A)) (bitIndex_flat i).symm
    _ = stateBits (rho A) (bitIndex (flatX i) (flatY i) (flatZ i)) :=
      eval_rhoCircuit_bit A _ _ _
    _ = stateBits (rho A) i := congrArg (stateBits (rho A)) (bitIndex_flat i)

private theorem eval_piCircuit_bit (A : State) (x y : Fin 5) (z : Fin 64) :
    piCircuit.eval interpretation (stateBits A) (bitIndex x y z) =
      stateBits (pi A) (bitIndex x y z) := by
  simp only [piCircuit, Circuit.eval_wiring, Function.comp_apply, flatX_bitIndex,
    flatY_bitIndex, flatZ_bitIndex, stateBits_bitIndex]
  unfold pi getLane
  rw [Vector.get_ofFn, coordinate_laneIndex]
  simp only [laneIndex_div_five]

private theorem eval_piCircuit (A : State) :
    piCircuit.eval interpretation (stateBits A) = stateBits (pi A) := by
  funext i
  calc
    piCircuit.eval interpretation (stateBits A) i =
        piCircuit.eval interpretation (stateBits A)
          (bitIndex (flatX i) (flatY i) (flatZ i)) :=
      congrArg (piCircuit.eval interpretation (stateBits A)) (bitIndex_flat i).symm
    _ = stateBits (pi A) (bitIndex (flatX i) (flatY i) (flatZ i)) :=
      eval_piCircuit_bit A _ _ _
    _ = stateBits (pi A) i := congrArg (stateBits (pi A)) (bitIndex_flat i)

private theorem eval_chiBitAtCircuit (A : State) (x y : Fin 5) (z : Fin 64) :
    (chiBitCircuit.comp (Circuit.wiring signature fun j : Fin 3 =>
      match j.val with
      | 0 => bitIndex x y z
      | 1 => bitIndex (coordinate (x.val + 1)) y z
      | _ => bitIndex (coordinate (x.val + 2)) y z)).eval interpretation (stateBits A) 0 =
      stateBits (chi A) (bitIndex x y z) := by
  rw [Circuit.eval_comp, eval_chiBitCircuit]
  simp only [Circuit.eval_wiring, Function.comp_apply]
  norm_num
  rw [stateBits_bitIndex, stateBits_bitIndex, stateBits_bitIndex,
    stateBits_bitIndex]
  unfold chi getLane
  rw [Vector.get_ofFn, coordinate_laneIndex]
  have hy : (⟨(laneIndex x y).val / 5, by omega⟩ : Fin 5) = y :=
    Fin.ext (laneIndex_div_five x y)
  simp only [hy, BitVec.getLsbD_xor, BitVec.getLsbD_not, BitVec.getLsbD_and]
  simp only [z.isLt, decide_true, Bool.true_and]

private theorem eval_chiCircuit (A : State) :
    chiCircuit.eval interpretation (stateBits A) = stateBits (chi A) := by
  funext i
  rw [chiCircuit, Circuit.eval_pi]
  change (chiBitCircuit.comp (Circuit.wiring signature fun j : Fin 3 =>
      match j.val with
      | 0 => bitIndex (flatX i) (flatY i) (flatZ i)
      | 1 => bitIndex (coordinate ((flatX i).val + 1)) (flatY i) (flatZ i)
      | _ => bitIndex (coordinate ((flatX i).val + 2)) (flatY i) (flatZ i))).eval
    interpretation (stateBits A) 0 = _
  exact (eval_chiBitAtCircuit A (flatX i) (flatY i) (flatZ i)).trans
    (congrArg (stateBits (chi A)) (bitIndex_flat i))

private theorem eval_iotaBitCircuit (constant : Lane) (A : State)
    (x y : Fin 5) (z : Fin 64) :
    (iotaBitCircuit constant x y z).eval interpretation (stateBits A) 0 =
      stateBits (iota constant A) (bitIndex x y z) := by
  rw [stateBits_bitIndex]
  by_cases hlane : 5 * y.val + x.val = 0
  · have hlaneIndex : laneIndex x y = 0 := Fin.ext hlane
    cases hconstant : constant.getLsbD z.val <;>
      simp only [iotaBitCircuit, hlane, hconstant, decide_true, Bool.true_and,
        Bool.false_eq_true, ite_false, ite_true, Circuit.eval_comp, eval_notCircuit,
        Circuit.eval_wiring, Function.comp_apply, stateBits_bitIndex]
    · unfold iota getLane
      rw [Vector.get_ofFn]
      simp only [laneIndex, hlane, ite_true, BitVec.getLsbD_xor, hconstant, Bool.xor_false]
    · unfold iota getLane
      rw [Vector.get_ofFn]
      simp only [laneIndex, hlane, ite_true, BitVec.getLsbD_xor, hconstant]
      cases (A.get 0).getLsbD z.val <;> rfl
  · have hlaneIndex : laneIndex x y ≠ 0 := fun h => hlane (Fin.ext_iff.mp h)
    have hcoords : ¬(y = 0 ∧ x = 0) := by
      rintro ⟨rfl, rfl⟩
      exact hlane rfl
    simp only [iotaBitCircuit, hlane, decide_false, Bool.false_and, Bool.false_eq_true,
      ite_false, Circuit.eval_wiring, Function.comp_apply, stateBits_bitIndex]
    unfold iota getLane
    rw [Vector.get_ofFn]
    simp only [laneIndex, hlane, ite_false]

private theorem eval_iotaCircuit (constant : Lane) (A : State) :
    (iotaCircuit constant).eval interpretation (stateBits A) = stateBits (iota constant A) := by
  funext i
  rw [iotaCircuit, Circuit.eval_pi]
  change (iotaBitCircuit constant (flatX i) (flatY i) (flatZ i)).eval
      interpretation (stateBits A) 0 = _
  rw [eval_iotaBitCircuit]
  exact congrArg (stateBits (iota constant A)) (bitIndex_flat i)

private theorem eval_roundCircuit (constant : Lane) (A : State) :
    (roundCircuit constant).eval interpretation (stateBits A) = stateBits (round constant A) := by
  simp only [roundCircuit, round, Circuit.eval_comp, eval_thetaCircuit, eval_rhoCircuit,
    eval_piCircuit, eval_chiCircuit, eval_iotaCircuit]

private theorem eval_roundsCircuit (constants : List Lane) (A : State) :
    (constants.foldl (fun circuit constant => (roundCircuit constant).comp circuit)
      (Circuit.id signature 1600)).eval interpretation (stateBits A) =
      stateBits (constants.foldl (fun state constant => round constant state) A) := by
  induction constants using List.reverseRecOn generalizing A with
  | nil => rfl
  | append_singleton constants constant ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, Circuit.eval_comp]
    rw [ih, eval_roundCircuit]

/-- The fixed direct circuit agrees on every 1600-bit input with the executable FIPS 202
Keccak-p[1600, 24] permutation. -/
theorem eval_keccakP1600Circuit (bits : BitString 1600) :
    keccakP1600Circuit.eval interpretation bits =
      stateBits (keccakP1600Rounds24 (stateOfBits bits)) := by
  calc
    keccakP1600Circuit.eval interpretation bits =
        keccakP1600Circuit.eval interpretation (stateBits (stateOfBits bits)) :=
      congrArg (keccakP1600Circuit.eval interpretation) (stateBits_stateOfBits bits).symm
    _ = (roundConstants.foldl
          (fun circuit constant => (roundCircuit constant).comp circuit)
          (Circuit.id signature 1600)).eval interpretation (stateBits (stateOfBits bits)) :=
      congrArg (fun circuit => circuit.eval interpretation (stateBits (stateOfBits bits)))
        keccakP1600Circuit_eq
    _ = stateBits (roundConstants.foldl
          (fun state constant => round constant state) (stateOfBits bits)) :=
      eval_roundsCircuit roundConstants (stateOfBits bits)
    _ = stateBits (keccakP1600Rounds24 (stateOfBits bits)) := rfl

-- Elaborating the retained 24-round circuit traverses a deeply nested, fixed composition tree.
set_option maxRecDepth 2048 in
/-- Retained native multitape compiler for executable Keccak-p[1600, 24]. Its `computes`, `time`,
`workspace`, `inputBits`, `outputBits`, and `staticBits` fields are the concrete certificate. -/
@[expose] noncomputable def keccakP1600Compiler : NativeCompiler
    (fun bits : BitString 1600 => stateBits (keccakP1600Rounds24 (stateOfBits bits)))
    (encBitString 1600) (encBitString 1600) :=
  (evalCircuitCompiler keccakP1600Circuit).ofOutputEq fun input =>
    congrArg (encBitString 1600) (eval_keccakP1600Circuit input).symm

end Cslib.Crypto.Keccak
