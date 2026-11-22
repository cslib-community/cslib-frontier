/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Yao.Security
public import CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Efficient
public import CslibFrontier.Crypto.Primitives.Garbling.HalfGates.PrvSim
public import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Efficient
public import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Privacy

/-!
# Steps for Yao's protocol in the ideal OT hybrid model over concrete garbling schemes

This module instantiates `Scheme.PrvSimSecureUniversal.yaoOneSidedHybridSemiHonestSecure` and
`Scheme.PrvSimSecureUniversal.yaoHybridSemiHonestSecure` as steps in the ideal `batchOTWorld`
oblivious-transfer hybrid model (#6045), rather than plain-model Theorem 7 of [LindellPinkas2009]
(ePrint 2004/175, §4.2, p. 15) or Theorem 14 of [BellareHoangRogaway2012] (§7.1, p. 35), which
compose with a concrete semi-honest 1-out-of-2 oblivious-transfer protocol, for the library's two
garbling schemes whose `prv.sim` simulator `simWord` serves every adversary:

* `PseudorandomFunction.yaoOneSidedHybridSemiHonestSecure_pointPermute` and
  `PseudorandomFunction.yaoHybridSemiHonestSecure_pointPermute`: point-and-permute garbling
  `PointPermute.scheme family` of valid conventional circuits, with the topology as side
  information, for every pseudorandom function `family`;
* `CircularCorrelationRobust.yaoOneSidedHybridSemiHonestSecure_halfGates` and
  `CircularCorrelationRobust.yaoHybridSemiHonestSecure_halfGates`: half-gates garbling
  `HalfGates.scheme hash` of XOR–AND circuits, with the circuit as side information, for every
  circular correlation robust hash family `hash`.

Each rests only on its named assumption, `PseudorandomFunction` or `CircularCorrelationRobust`,
both standard, with the public parameters drawn by a PPT sampler: the novel
`Scheme.PrvSimSecureUniversal` is proved here for the scheme, not assumed. All four are steps in
the ideal `batchOTWorld` oblivious-transfer hybrid model (#6045), with the other deviations that
`Scheme.PrvSimSecureUniversal.yaoOneSidedHybridSemiHonestSecure` and
`Scheme.PrvSimSecureUniversal.yaoHybridSemiHonestSecure` list. Neither scheme is the
double-encryption construction of [LindellPinkas2009] (§4.1, p. 12): point-and-permute garbling is
this library's variant of `Garble1` of [BellareHoangRogaway2012], and half-gates garbling is the
scheme of [ZahurRosulekEvans2015] with the differences that
`CircularCorrelationRobust.prvSim_halfGates` lists.

## Main results

* `Cslib.Crypto.PseudorandomFunction.yaoOneSidedHybridSemiHonestSecure_pointPermute`
* `Cslib.Crypto.CircularCorrelationRobust.yaoOneSidedHybridSemiHonestSecure_halfGates`
* `Cslib.Crypto.PseudorandomFunction.yaoHybridSemiHonestSecure_pointPermute`
* `Cslib.Crypto.CircularCorrelationRobust.yaoHybridSemiHonestSecure_halfGates`

## References

* [Y. Lindell, B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009], cited in the ePrint version 2004/175 of June 26, 2006:
  §4.1 (p. 12) and Protocol 2 & Theorem 7 (§4.2, p. 15).
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012],
  §3.4 (p. 9) and §7.1 (Fig. 16, p. 34; Theorem 14, p. 35).
* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole: Reducing Data Transfer in Garbled
  Circuits using Half Gates*][ZahurRosulekEvans2015], §2 (p. 5) and §4.1 (pp. 10–12).
-/

public section

namespace Cslib.Crypto

open Garbling Protocols.MPC Probability Turing.MultiTapeTM

private theorem prvSimUniversal_pointPermute {family : List Bool → List Bool → List Bool}
    (h : PseudorandomFunction family) :
    (PointPermute.scheme family).PrvSimSecureUniversal phiTopo encValidCircuit encValidTopo :=
  ⟨PointPermute.simWord family, PointPermute.isPPTOn_simWord h.polyTime,
    fun _ _ _ hB => h.negligible_prvSimAdvantage_simWord hB⟩

private theorem prvSimUniversal_halfGates {hash : List Bool → List Bool → List Bool}
    (h : CircularCorrelationRobust hash) :
    (HalfGates.scheme hash).PrvSimSecureUniversal (SideInfo.circ (HalfGates.scheme hash))
      encXorAndCircuit encXorAndCircuit :=
  ⟨HalfGates.simWord hash, HalfGates.isPPTOn_simWord h.polyTime,
    fun _ _ _ hB => h.negligible_prvSimAdvantage_simWord hB⟩

/-- Step in the ideal `batchOTWorld` oblivious-transfer hybrid model (#6045), not plain-model
Theorem 7 of [LindellPinkas2009] (ePrint 2004/175, §4.2, p. 15) or Theorem 14 of
[BellareHoangRogaway2012] (§7.1, p. 35), which compose with a concrete semi-honest 1-out-of-2
oblivious-transfer protocol: one-sided Yao's protocol (`Yao.oneSidedFamily`, where party `0`
outputs `[]` and party `1` outputs the decoded circuit result) over point-and-permute garbling is
semi-honest secure in the `batchOTWorld` hybrid across every static coalition `I : Finset (Fin 2)`,
for every pseudorandom function `family` and every PPT sampler of the public parameters, with the
other deviations that `Scheme.PrvSimSecureUniversal.yaoOneSidedHybridSemiHonestSecure` lists. The
garbling simulator is `PointPermute.simWord family`
(`PseudorandomFunction.negligible_prvSimAdvantage_simWord`), with the topology as side
information. -/
theorem PseudorandomFunction.yaoOneSidedHybridSemiHonestSecure_pointPermute
    {family : List Bool → List Bool → List Bool} (h : PseudorandomFunction family)
    {samp : ℕ → ProbComp (Yao.Params (PointPermute.scheme family))}
    (hsamp : IsPPTOn encUnary (Yao.encParams encValidCircuit) samp) (I : Finset (Fin 2)) :
    (Yao.oneSidedFamily (PointPermute.scheme family)).SemiHonestSecure
      (fun n => ProbComp.eval (samp n)) I (Yao.oneSidedEncoding _ encValidCircuit) :=
  (prvSimUniversal_pointPermute h).yaoOneSidedHybridSemiHonestSecure
    (PointPermute.scheme_isEfficient h.polyTime) rfl (PointPermute.scheme_isValid family).correct
    phiTopo_polyTime hsamp I

/-- Step in the ideal `batchOTWorld` oblivious-transfer hybrid model (#6045), not plain-model
Theorem 7 of [LindellPinkas2009] (ePrint 2004/175, §4.2, p. 15) or Theorem 14 of
[BellareHoangRogaway2012] (§7.1, p. 35), which compose with a concrete semi-honest 1-out-of-2
oblivious-transfer protocol: one-sided Yao's protocol (`Yao.oneSidedFamily`, where party `0`
outputs `[]` and party `1` outputs the decoded circuit result) over half-gates garbling is
semi-honest secure in the `batchOTWorld` hybrid across every static coalition `I : Finset (Fin 2)`,
for every circular correlation robust hash family `hash` and every PPT sampler of the public
parameters, with the other deviations that
`Scheme.PrvSimSecureUniversal.yaoOneSidedHybridSemiHonestSecure` lists. The garbling simulator is
`HalfGates.simWord hash` (`CircularCorrelationRobust.negligible_prvSimAdvantage_simWord`), with the
circuit as side information. -/
theorem CircularCorrelationRobust.yaoOneSidedHybridSemiHonestSecure_halfGates
    {hash : List Bool → List Bool → List Bool} (h : CircularCorrelationRobust hash)
    {samp : ℕ → ProbComp (Yao.Params (HalfGates.scheme hash))}
    (hsamp : IsPPTOn encUnary (Yao.encParams encXorAndCircuit) samp) (I : Finset (Fin 2)) :
    (Yao.oneSidedFamily (HalfGates.scheme hash)).SemiHonestSecure
      (fun n => ProbComp.eval (samp n)) I (Yao.oneSidedEncoding _ encXorAndCircuit) :=
  (prvSimUniversal_halfGates h).yaoOneSidedHybridSemiHonestSecure
    (HalfGates.scheme_isEfficient h.polyTime) rfl (HalfGates.scheme_correct hash) .id' hsamp I

/-- Step in the ideal `batchOTWorld` oblivious-transfer hybrid model (#6045), not plain-model
Theorem 7 of [LindellPinkas2009] (ePrint 2004/175, §4.2, p. 15, which composes with a concrete
semi-honest 1-out-of-2 oblivious-transfer protocol): Yao's protocol over point-and-permute
garbling is semi-honest secure in the `batchOTWorld` hybrid against the corruption of either
party, for every pseudorandom function `family` and every PPT sampler of the public parameters,
with the other deviations that `Scheme.PrvSimSecureUniversal.yaoHybridSemiHonestSecure` lists. The
garbling simulator is `PointPermute.simWord family`, which serves every adversary
(`PseudorandomFunction.negligible_prvSimAdvantage_simWord`), with the topology as side
information. -/
theorem PseudorandomFunction.yaoHybridSemiHonestSecure_pointPermute
    {family : List Bool → List Bool → List Bool} (h : PseudorandomFunction family)
    {samp : ℕ → ProbComp (Yao.Params (PointPermute.scheme family))}
    (hsamp : IsPPTOn encUnary (Yao.encParams encValidCircuit) samp) (i : Fin 2) :
    (Yao.family (PointPermute.scheme family)).SemiHonestSecure (fun n => ProbComp.eval (samp n))
      {i} (Yao.encoding _ encValidCircuit) :=
  (prvSimUniversal_pointPermute h).yaoHybridSemiHonestSecure
    (PointPermute.scheme_isEfficient h.polyTime) rfl (PointPermute.scheme_isValid family).correct
    phiTopo_polyTime hsamp i

/-- Step in the ideal `batchOTWorld` oblivious-transfer hybrid model (#6045), not plain-model
Theorem 7 of [LindellPinkas2009] (ePrint 2004/175, §4.2, p. 15, which composes with a concrete
semi-honest 1-out-of-2 oblivious-transfer protocol): Yao's protocol over half-gates garbling is
semi-honest secure in the `batchOTWorld` hybrid against the corruption of either party, for every
circular correlation robust hash family `hash` and every PPT sampler of the public parameters,
with the other deviations that `Scheme.PrvSimSecureUniversal.yaoHybridSemiHonestSecure` lists. The
garbling simulator is `HalfGates.simWord hash`, which serves every adversary
(`CircularCorrelationRobust.negligible_prvSimAdvantage_simWord`), with the circuit as side
information. -/
theorem CircularCorrelationRobust.yaoHybridSemiHonestSecure_halfGates
    {hash : List Bool → List Bool → List Bool} (h : CircularCorrelationRobust hash)
    {samp : ℕ → ProbComp (Yao.Params (HalfGates.scheme hash))}
    (hsamp : IsPPTOn encUnary (Yao.encParams encXorAndCircuit) samp) (i : Fin 2) :
    (Yao.family (HalfGates.scheme hash)).SemiHonestSecure (fun n => ProbComp.eval (samp n))
      {i} (Yao.encoding _ encXorAndCircuit) :=
  (prvSimUniversal_halfGates h).yaoHybridSemiHonestSecure
    (HalfGates.scheme_isEfficient h.polyTime) rfl (HalfGates.scheme_correct hash) .id' hsamp i

end Cslib.Crypto
