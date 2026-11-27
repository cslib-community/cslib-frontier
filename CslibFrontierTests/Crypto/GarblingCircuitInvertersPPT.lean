/-
Copyright (c) 2026 Samuel Schlesinger, Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module

import CslibFrontier.Crypto.Primitives.Garbling.CircuitInvertersPPT

/-!
# Tests for strict-PPT certification of conventional-circuit inverters

Checked instantiations and boundary tests for
`CslibFrontier.Crypto.Primitives.Garbling.CircuitInvertersPPT`, as a client under module
encapsulation:

* concrete `ValidCircuit`, `ValidTopo`, and `ValidShape` encodings (through the public equation
  `encValidShape_apply`), separating circuits by
  shape/topology while confirming `phiSize` identifies distinct wirings of the same shape;
* strict polynomial-time (`ComputableInPolyTime`) and `IsPPTOn` certificates for `phiTopo`,
  `phiSize`, `phiCirc`, `evalCirc`, `mTopo`, `mSize`, `mTopoInv`, `mSizeInv`, and a concrete
  `Scheme.IsCircuitScheme`;
* negative validity and length-mismatch boundary checks showing why `Topo.IsValid` and
  `y.length = t.m` are necessary for `sizeTopo` and `mTopoGates`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GarblingCircuitInvertersPPT

open Cslib Cslib.Crypto Cslib.Crypto.Garbling Cslib.Probability Turing.MultiTapeTM

/-! ## Concrete circuits, shapes, and encodings -/

private def sampleCircuitA : ConventionalCircuit where
  n := 3
  m := 1
  q := 2
  A := ![1, 2]
  B := ![2, 4]
  G i := if i.val = 0 then (· && ·) else xor

private def sampleCircuitB : ConventionalCircuit where
  n := 3
  m := 1
  q := 2
  A := ![1, 2]
  B := ![3, 4]
  G i := if i.val = 0 then (· && ·) else xor

private def smallCircuit : ConventionalCircuit where
  n := 2
  m := 1
  q := 1
  A := ![1]
  B := ![2]
  G _ := (· && ·)

private theorem sampleCircuitA_isValid : sampleCircuitA.IsValid := by decide
private theorem sampleCircuitB_isValid : sampleCircuitB.IsValid := by decide
private theorem smallCircuit_isValid : smallCircuit.IsValid := by decide

def validA : ValidCircuit := ⟨sampleCircuitA, sampleCircuitA_isValid⟩
def validB : ValidCircuit := ⟨sampleCircuitB, sampleCircuitB_isValid⟩
def validSmall : ValidCircuit := ⟨smallCircuit, smallCircuit_isValid⟩

/-- `encValidShape` writes a shape `(n, m, q)` as three unary blocks: the shape `(3, 1, 2)` of
`validA` is the word `encShapeData (3, 1, 2)`. -/
theorem encValidShape_phiSize_validA :
    encValidShape (phiSize.phi validA) = encShapeData (3, 1, 2) :=
  encValidShape_apply _

/-- Two circuits with identical shape `(3, 1, 2)` share `encValidShape` after `phiSize.phi`
even though their topologies and encodings differ, while a `(2, 1, 1)` circuit has a distinct
encoded shape. -/
theorem phiSize_same_and_distinct :
    encValidShape (phiSize.phi validA) = encValidShape (phiSize.phi validB) ∧
      encValidTopo (phiTopo.phi validA) ≠ encValidTopo (phiTopo.phi validB) ∧
      encValidShape (phiSize.phi validA) ≠ encValidShape (phiSize.phi validSmall) := by
  refine ⟨by rw [encValidShape_apply, encValidShape_apply]; rfl, ?_, ?_⟩
  · intro h
    have h' : phiTopo.phi validA = phiTopo.phi validB := encValidTopo.injective h
    have heq : (phiTopo.phi validA).1.gateList = (phiTopo.phi validB).1.gateList :=
      congrArg (fun t : ValidTopo => t.1.gateList) h'
    exact absurd heq (by decide)
  · intro h
    have h' : phiSize.phi validA = phiSize.phi validSmall := encValidShape.injective h
    have heq : (phiSize.phi validA).n = (phiSize.phi validSmall).n :=
      congrArg ValidShape.n h'
    exact absurd heq (by decide)

/-! ## Strict polynomial-time & PPT certificates instantiated -/

/-- A concrete circuit garbling scheme over `ValidCircuit`. -/
def plainCircuitScheme : Scheme ValidCircuit where
  inLen f := f.1.n
  outLen f := f.1.m
  size f := f.1.q
  ev f x := f.1.evalCirc x
  coinLen _ _ _ _ := 0
  gb _ f _ := ⟨[], [], List.replicate f.1.m false⟩
  encode _ x := x
  evalGarbled _ x := x
  decode d y := if y.length = d.length then some y else none

theorem plainCircuitScheme_isCircuitScheme : plainCircuitScheme.IsCircuitScheme :=
  ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl⟩

theorem plainCircuitScheme_inLen_polyTime :
    ComputableInPolyTime plainCircuitScheme.inLen encValidCircuit encUnary :=
  plainCircuitScheme_isCircuitScheme.inLen_polyTime

theorem plainCircuitScheme_outLen_polyTime :
    ComputableInPolyTime plainCircuitScheme.outLen encValidCircuit encUnary :=
  plainCircuitScheme_isCircuitScheme.outLen_polyTime

theorem plainCircuitScheme_ev_polyTime :
    ComputableInPolyTime (fun p : ValidCircuit × List Bool => plainCircuitScheme.ev p.1 p.2)
      (encPair encValidCircuit encBits) encBits :=
  plainCircuitScheme_isCircuitScheme.ev_polyTime

theorem phiTopo_isPPTOn :
    IsPPTOn encValidCircuit encValidTopo (fun f => pure (phiTopo.phi f)) :=
  phiTopo_polyTime.isPPTOn

theorem phiSize_isPPTOn :
    IsPPTOn encValidCircuit encValidShape (fun f => pure (phiSize.phi f)) :=
  phiSize_polyTime.isPPTOn

theorem phiCirc_isPPTOn :
    IsPPTOn encValidCircuit encValidCircuit (fun f => pure (phiCirc.phi f)) :=
  phiCirc_polyTime.isPPTOn

theorem mTopo_isPPTOn :
    IsPPTOn (encPair encValidTopo encBits) (encQuery ValidCircuit encValidCircuit)
      (fun p => pure (mTopo p.1 p.2)) :=
  mTopo_polyTime.isPPTOn

theorem mSize_isPPTOn :
    IsPPTOn (encPair encValidShape encBits) (encQuery ValidCircuit encValidCircuit)
      (fun p => pure (mSize p.1 p.2)) :=
  mSize_polyTime.isPPTOn

theorem mTopoInv_isPPTOn :
    IsPPTOn encValidTopo encValidCircuit (fun t => pure (mTopoInv t)) :=
  mTopoInv_polyTime.isPPTOn

theorem mSizeInv_isPPTOn :
    IsPPTOn encValidShape encValidCircuit (fun s => pure (mSizeInv s)) :=
  mSizeInv_polyTime.isPPTOn

theorem mTopo_mSize_concrete_roundtrip :
    let t := phiTopo.phi validA
    let s := phiSize.phi validA
    (mTopo t [true]).fn.1.evalCirc (mTopo t [true]).input = [true] ∧
      (mSize s [true]).fn.1.evalCirc (mSize s [true]).input = [true] ∧
      phiTopo.phi (mTopoInv t) = t ∧
      phiSize.phi (mSizeInv s) = s := by
  decide

/-! ## Negative validity and boundary checks -/

/-- A topology with `n = 1 < 2` fails `Topo.IsValid`: the canonical `sizeTopo` wiring `A = 1,
B = 2` would read an output/gate wire as an input wire. -/
private def oneInputTopo : Topo where
  n := 1
  m := 1
  q := 1
  A := ![1]
  B := ![2]

theorem oneInputTopo_not_valid : ¬ oneInputTopo.IsValid := by decide

/-- A topology with `q < m` fails `Topo.IsValid`, and `mTopoGates` cannot produce a `2`-bit
output `y = [true, false]` from a `1`-gate circuit (`evalCirc` returns only `1` bit). -/
private def tooFewGatesTopo : Topo where
  n := 2
  m := 2
  q := 1
  A := ![1]
  B := ![2]

theorem tooFewGates_not_valid_and_inversion_fails :
    ¬ tooFewGatesTopo.IsValid ∧
      (ofTopo tooFewGatesTopo (mTopoGates tooFewGatesTopo [true, false])).evalCirc [false, false] ≠
        [true, false] := by
  decide

/-- When the target string `y` does not have length `t.m`, `mTopo` does not invert to `y`. -/
theorem mTopo_wrong_output_length_fails :
    (mTopo (phiTopo.phi validA) [true, false]).fn.1.evalCirc
      (mTopo (phiTopo.phi validA) [true, false]).input ≠ [true, false] := by
  decide

/-- A topology feeding an output wire into a subsequent gate fails `Topo.IsValid`
(`B_le_n_add_q_sub_m` violated). -/
private def outputFedIntoGateTopo : Topo where
  n := 2
  m := 2
  q := 2
  A := ![1, 2]
  B := ![2, 3]

theorem outputFedIntoGateTopo_not_valid : ¬ outputFedIntoGateTopo.IsValid := by decide

end CslibFrontierTests.Crypto.GarblingCircuitInvertersPPT
