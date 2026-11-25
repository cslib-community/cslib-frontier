/-
Copyright (c) 2026 Samuel Schlesinger, Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.Efficient
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.PPT
import CslibFrontier.Tactic.PolyTime

/-!
# Strict polynomial-time certification for conventional-circuit inverters

Following Bellare, Hoang and Rogaway [BellareHoangRogaway2012], Section 4.1, Proposition 1, this
module certifies that the conventional-circuit side-information readers and explicit inverters of
`CslibFrontier.Crypto.Primitives.Garbling.CircuitInverters` run in deterministic strict
polynomial time (`ComputableInPolyTime`), and hence in uniform strict PPT (`IsPPTOn` via
`ComputableInPolyTime.isPPTOn`).

`CslibFrontier.Crypto.Primitives.Garbling.Efficient` already provides the circuit and topology
encodings (`encValidCircuit`, `encValidTopo`, `encQuery`) and certificates for circuit evaluation
(`evalCirc_polyTime`) and topology extraction (`phiTopo_polyTime`). This module supplies:

* `encShapeData` and `encValidShape`: unary word encodings for valid circuit shapes `(n, m, q)`
  (unary encoding of `q` ensures the `q`-gate circuit built by `mSize` has polynomial length);
* `phiSize_polyTime` and `phiCirc_polyTime`: polynomial-time extraction of `phiSize` and `phiCirc`;
* `sizeTopo_polyTime`, `mTopo_polyTime`, `mSize_polyTime`, `mTopoInv_polyTime`, and
  `mSizeInv_polyTime`: strict polynomial-time certificates for the four Proposition 1 inverters
  (`mTopo`, `mSize`, `mTopoInv`, `mSizeInv`);
* `Scheme.IsCircuitScheme.inLen_polyTime`, `.outLen_polyTime`, and `.ev_polyTime`: convenience
  certificates for circuit garbling schemes over `ValidCircuit`.

The paper's Proposition 1 states linear running time in the RAM model; here we prove strict
polynomial time on multi-tape Turing machines (`ComputableInPolyTime`).

## Main definitions

* `Cslib.Crypto.Garbling.encShapeData`, `Cslib.Crypto.Garbling.encValidShape`: word encodings
  for `ValidShape`.

## Main results

* `Cslib.Crypto.Garbling.phiSize_polyTime`, `Cslib.Crypto.Garbling.phiCirc_polyTime`:
  `phiSize.phi` and `phiCirc.phi` are polynomial-time computable on `encValidCircuit`.
* `Cslib.Crypto.Garbling.mTopo_polyTime`, `Cslib.Crypto.Garbling.mSize_polyTime`,
  `Cslib.Crypto.Garbling.mTopoInv_polyTime`, `Cslib.Crypto.Garbling.mSizeInv_polyTime`: the four
  explicit side-information inverters of [BellareHoangRogaway2012], Section 4.1, Proposition 1 run
  in strict polynomial time.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto.Garbling

open Turing.MultiTapeTM Probability

/-! ## Encodings and side-information readers -/

/-- The data of a valid circuit shape: `n`, `m`, and `q` all encoded in unary. Encoding `q` in
unary ensures that the `q`-gate circuit built by `mSize` has length polynomial in the input. -/
abbrev encShapeData : (ℕ × ℕ × ℕ) ↪ List Bool :=
  encPair encUnary (encPair encUnary encUnary)

/-- Valid circuit shapes `(n, m, q)` encoded as words via `encShapeData`. -/
def encValidShape : ValidShape ↪ List Bool :=
  ⟨fun s => encShapeData (s.n, s.m, s.q), fun s s' h => by
    obtain ⟨hn, hrest⟩ := Prod.ext_iff.mp (encShapeData.injective h)
    obtain ⟨hm, hq⟩ := Prod.ext_iff.mp hrest
    cases s
    cases s'
    simp only at hn hm hq
    subst hn hm hq
    rfl⟩

/-- The data `(n, m, q)` of a valid shape is read from its word in polynomial time. -/
theorem shapeData_polyTime :
    ComputableInPolyTime (fun s : ValidShape => (s.n, s.m, s.q)) encValidShape encShapeData :=
  .of_eq fun _ => rfl

/-- The shape side information `Φ_size(f) = (n, m, q)` is computed in polynomial time from
`encValidCircuit`. -/
theorem phiSize_polyTime : ComputableInPolyTime phiSize.phi encValidCircuit encValidShape := by
  have hd := circuitData_polyTime
  have hq : ComputableInPolyTime (fun f : ValidCircuit => f.1.q) encValidCircuit encUnary :=
    ((ComputableInPolyTime.length_list _).comp hd.snd'.snd').of_enc_eq fun f =>
      congrArg encUnary (ConventionalCircuit.length_gateList f.1).symm
  exact (hd.fst'.prod (hd.snd'.fst'.prod hq)).of_enc_eq fun _ => rfl

/-- The full-circuit side information `Φ_circ(f) = f` is computed in polynomial time on
`encValidCircuit`. -/
theorem phiCirc_polyTime : ComputableInPolyTime phiCirc.phi encValidCircuit encValidCircuit :=
  ComputableInPolyTime.id'

/-! ## Circuit-scheme reader certificates -/

namespace Scheme.IsCircuitScheme

variable {G : Scheme ValidCircuit}

/-- For any circuit garbling scheme, `G.inLen` is polynomial-time computable on `encValidCircuit`.
-/
theorem inLen_polyTime (hG : G.IsCircuitScheme) :
    ComputableInPolyTime G.inLen encValidCircuit encUnary :=
  circuitData_polyTime.fst'.of_enc_eq fun f => congrArg encUnary (hG.1 f).1

/-- For any circuit garbling scheme, `G.outLen` is polynomial-time computable on
`encValidCircuit`. -/
theorem outLen_polyTime (hG : G.IsCircuitScheme) :
    ComputableInPolyTime G.outLen encValidCircuit encUnary :=
  circuitData_polyTime.snd'.fst'.of_enc_eq fun f => congrArg encUnary (hG.1 f).2.1

/-- For any circuit garbling scheme, `G.ev` is polynomial-time computable on
`(encValidCircuit, encBits)`. -/
theorem ev_polyTime (hG : G.IsCircuitScheme) :
    ComputableInPolyTime (fun p : ValidCircuit × List Bool => G.ev p.1 p.2)
      (encPair encValidCircuit encBits) encBits :=
  evalCirc_polyTime.of_enc_eq fun ⟨f, x⟩ => congrArg encBits (hG.2 f x)

end Scheme.IsCircuitScheme

/-! ## Proposition 1 inverters -/

/-- The gate-table entry constructed by `mTopo` for gate `idx` with argument wires `entry.1` and
parameters `par = ((n, m, q), y)`. -/
private def mTopoGateData (par : (ℕ × ℕ × ℕ) × List Bool) (entry : (ℕ × ℕ) × ℕ) :
    ℕ × ℕ × List Bool :=
  let n := par.1.1
  let m := par.1.2.1
  let q := par.1.2.2
  let g := n + 1 + entry.2
  let bit := if g ≤ n + q - m then false else par.2.getD (g - (n + q - m) - 1) false
  (entry.1.1, entry.1.2, [bit, bit, bit, bit])

private theorem mTopoGateData_polyTime :
    ComputableInPolyTime (fun p : ((ℕ × ℕ × ℕ) × List Bool) × ((ℕ × ℕ) × ℕ) =>
        mTopoGateData p.1 p.2)
      (encPair (encPair encShapeData encBits) (encPair (encPair encNat encNat) encUnary))
      (encPair encNat (encPair encNat encBits)) := by
  let E := encPair (encPair encShapeData encBits) (encPair (encPair encNat encNat) encUnary)
  have hpar := ComputableInPolyTime.fst (encPair encShapeData encBits)
    (encPair (encPair encNat encNat) encUnary)
  have hentry := ComputableInPolyTime.snd (encPair encShapeData encBits)
    (encPair (encPair encNat encNat) encUnary)
  have hn : ComputableInPolyTime (fun p => p.1.1.1) E encUnary := hpar.fst'.fst'
  have hm : ComputableInPolyTime (fun p => p.1.1.2.1) E encUnary := hpar.fst'.snd'.fst'
  have hq : ComputableInPolyTime (fun p => p.1.1.2.2) E encUnary := hpar.fst'.snd'.snd'
  have hy : ComputableInPolyTime (fun p => p.1.2) E encBits := hpar.snd'
  have ha : ComputableInPolyTime (fun p => p.2.1.1) E encNat := hentry.fst'.fst'
  have hb : ComputableInPolyTime (fun p => p.2.1.2) E encNat := hentry.fst'.snd'
  have hidx : ComputableInPolyTime (fun p => p.2.2) E encUnary := hentry.snd'
  have hg := (hn.unary_add' (.const 1)).unary_add' hidx
  have hc := (hn.unary_add' hq).unary_sub' hm
  have hpos := (hg.unary_sub' hc).unary_sub' (.const 1)
  have hval := hy.bitsGetDWithInput hpos false
  have hbit : ComputableInPolyTime (fun p =>
      if p.1.1.1 + 1 + p.2.2 ≤ p.1.1.1 + p.1.1.2.2 - p.1.1.2.1 then false
      else p.1.2.getD (p.1.1.1 + 1 + p.2.2 - (p.1.1.1 + p.1.1.2.2 - p.1.1.2.1) - 1) false)
      E encBool :=
    ComputableInPolyTime.ite_decide (ComputableInPolyTime.unary_le' hg hc) (.const false) hval
  have htab : ComputableInPolyTime (fun p =>
      let bit := if p.1.1.1 + 1 + p.2.2 ≤ p.1.1.1 + p.1.1.2.2 - p.1.1.2.1 then false
        else p.1.2.getD (p.1.1.1 + 1 + p.2.2 - (p.1.1.1 + p.1.1.2.2 - p.1.1.2.1) - 1) false
      [bit, bit, bit, bit]) E encBits :=
    ComputableInPolyTime.bitsCons hbit
      (ComputableInPolyTime.bitsCons hbit
        (ComputableInPolyTime.bitsCons hbit
          (ComputableInPolyTime.bitsCons hbit (.const []))))
  exact (ha.prod (hb.prod htab)).of_enc_eq fun ⟨par, entry⟩ => rfl

private theorem gateList_ofTopo_mTopoGates (t : Topo) (y : List Bool) :
    (ofTopo t (mTopoGates t y)).gateList =
      t.gateList.zipIdx.map (mTopoGateData ((t.n, t.m, t.q), y)) := by
  apply List.ext_getElem
  · simp [ConventionalCircuit.gateList, Topo.gateList, ofTopo]
  · intro i hi hi'
    simp only [ConventionalCircuit.gateList, ofTopo, List.getElem_ofFn, List.getElem_map,
      List.getElem_zipIdx, Topo.gateList, Nat.zero_add, mTopoGateData, mTopoGates,
      List.getD_eq_getElem?_getD]

/-- The `(Φ_topo, ev)`-inverter `mTopo` of [BellareHoangRogaway2012], Section 4.1, Proposition 1
runs in strict polynomial time on `(encValidTopo, encBits)`. -/
theorem mTopo_polyTime :
    ComputableInPolyTime (fun p : ValidTopo × List Bool => mTopo p.1 p.2)
      (encPair encValidTopo encBits) (encQuery ValidCircuit encValidCircuit) := by
  let E := encPair encValidTopo encBits
  have ht := topoData_polyTime.comp (ComputableInPolyTime.fst encValidTopo encBits)
  have hn : ComputableInPolyTime (fun p : ValidTopo × List Bool => p.1.1.n) E encUnary := ht.fst'
  have hm : ComputableInPolyTime (fun p : ValidTopo × List Bool => p.1.1.m) E encUnary :=
    ht.snd'.fst'
  have hgates : ComputableInPolyTime (fun p : ValidTopo × List Bool => p.1.1.gateList) E
      (encList (encPair encNat encNat)) := ht.snd'.snd'
  have hq : ComputableInPolyTime (fun p : ValidTopo × List Bool => p.1.1.q) E encUnary :=
    ((ComputableInPolyTime.length_list _).comp hgates).of_enc_eq fun p =>
      congrArg encUnary (Topo.length_gateList p.1.1).symm
  have hy : ComputableInPolyTime (fun p : ValidTopo × List Bool => p.2) E encBits :=
    ComputableInPolyTime.snd encValidTopo encBits
  have hpar := (hn.prod (hm.prod hq)).prod hy
  have hzip := (ComputableInPolyTime.zipIdx (encPair encNat encNat)).comp hgates
  have hgateList : ComputableInPolyTime
      (fun p : ValidTopo × List Bool => (ofTopo p.1.1 (mTopoGates p.1.1 p.2)).gateList) E
      (encList (encPair encNat (encPair encNat encBits))) :=
    (ComputableInPolyTime.mapWith mTopoGateData_polyTime hpar hzip).of_enc_eq fun p =>
      congrArg (encList (encPair encNat (encPair encNat encBits)))
        (gateList_ofTopo_mTopoGates p.1.1 p.2)
  have hcirc : ComputableInPolyTime
      (fun p : ValidTopo × List Bool => (mTopo p.1 p.2).fn) E encValidCircuit :=
    (hn.prod (hm.prod hgateList)).of_enc_eq fun p => encValidCircuit_apply (mTopo p.1 p.2).fn
  have hinp : ComputableInPolyTime (fun p : ValidTopo × List Bool => (mTopo p.1 p.2).input) E
      encBits :=
    ((ComputableInPolyTime.bitsReplicate false).comp hn).of_enc_eq fun _ => rfl
  exact (hcirc.prod hinp).of_enc_eq fun ⟨t, y⟩ => (encQuery_apply _ _ (mTopo t y)).symm

/-- The canonical topology constructor `sizeTopo` mapping a valid shape `(n, m, q)` to the
valid topology with `A(g) = 1, B(g) = 2` runs in strict polynomial time from `encValidShape` to
`encValidTopo`. -/
theorem sizeTopo_polyTime :
    ComputableInPolyTime (fun s : ValidShape => (⟨sizeTopo s, sizeTopo_isValid s⟩ : ValidTopo))
      encValidShape encValidTopo := by
  have hd := shapeData_polyTime
  have hgates : ComputableInPolyTime (fun s : ValidShape => (sizeTopo s).gateList) encValidShape
      (encList (encPair encNat encNat)) :=
    (ComputableInPolyTime.replicate hd.snd'.snd' (.const (1, 2))).of_enc_eq fun s => by
      refine congrArg (encList (encPair encNat encNat)) ?_
      apply List.ext_getElem
      · simp [Topo.gateList, sizeTopo]
      · intro i hi hi'
        simp [Topo.gateList, sizeTopo]
  exact (hd.fst'.prod (hd.snd'.fst'.prod hgates)).of_enc_eq fun s =>
    encValidTopo_apply ⟨sizeTopo s, sizeTopo_isValid s⟩

/-- The `(Φ_size, ev)`-inverter `mSize` of [BellareHoangRogaway2012], Section 4.1, Proposition 1
runs in strict polynomial time on `(encValidShape, encBits)`. -/
theorem mSize_polyTime :
    ComputableInPolyTime (fun p : ValidShape × List Bool => mSize p.1 p.2)
      (encPair encValidShape encBits) (encQuery ValidCircuit encValidCircuit) :=
  (mTopo_polyTime.comp
    ((sizeTopo_polyTime.comp (ComputableInPolyTime.fst encValidShape encBits)).prod
      (ComputableInPolyTime.snd encValidShape encBits))).of_enc_eq fun _ => rfl

/-- The `Φ_topo`-inverter `mTopoInv` of [BellareHoangRogaway2012], Section 4.1, Proposition 1 runs
in strict polynomial time on `encValidTopo`. -/
theorem mTopoInv_polyTime :
    ComputableInPolyTime mTopoInv encValidTopo encValidCircuit := by
  have hm : ComputableInPolyTime (fun t : ValidTopo => t.1.m) encValidTopo encUnary :=
    topoData_polyTime.snd'.fst'
  have hy : ComputableInPolyTime (fun t : ValidTopo => List.replicate t.1.m false)
      encValidTopo encBits :=
    (ComputableInPolyTime.bitsReplicate false).comp hm
  have hq : ComputableInPolyTime (fun t : ValidTopo => mTopo t (List.replicate t.1.m false))
      encValidTopo (encQuery ValidCircuit encValidCircuit) :=
    mTopo_polyTime.comp ((ComputableInPolyTime.id').prod hy)
  exact encQuery_fn_polyTime ValidCircuit encValidCircuit hq

/-- The `Φ_size`-inverter `mSizeInv` of [BellareHoangRogaway2012], Section 4.1, Proposition 1 runs
in strict polynomial time on `encValidShape`. -/
theorem mSizeInv_polyTime :
    ComputableInPolyTime mSizeInv encValidShape encValidCircuit :=
  (mTopoInv_polyTime.comp sizeTopo_polyTime).of_enc_eq fun _ => rfl

end Cslib.Crypto.Garbling
