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
# Yao's protocol over point-and-permute and half-gates garbling

`Scheme.PrvSimSecureUniversal.yaoSemiHonestSecure`, for the library's two garbling schemes whose
`prv.sim` simulator `simWord` serves every adversary:

* `PseudorandomFunction.yaoSemiHonestSecure_pointPermute`: point-and-permute garbling
  `PointPermute.scheme family` of valid conventional circuits, with the topology as side
  information, for every pseudorandom function `family`;
* `CircularCorrelationRobust.yaoSemiHonestSecure_halfGates`: half-gates garbling
  `HalfGates.scheme hash` of XOR–AND circuits, with the circuit as side information, for every
  circular correlation robust hash family `hash`.

Each rests only on its named assumption, `PseudorandomFunction` or `CircularCorrelationRobust`,
both standard, with the public parameters drawn by a PPT sampler: the novel
`Scheme.PrvSimSecureUniversal` is proved here for the scheme, not assumed. Both
are steps towards Theorem 7 of [LindellPinkas2009] in the oblivious-transfer hybrid model, with the
differences that `Scheme.PrvSimSecureUniversal.yaoSemiHonestSecure` lists. Neither scheme is the
double-encryption construction of [LindellPinkas2009] (§4.1, p. 12): point-and-permute garbling is
this library's variant of `Garble1` of [BellareHoangRogaway2012], and half-gates garbling is the
scheme of [ZahurRosulekEvans2015] with the differences that
`CircularCorrelationRobust.prvSim_halfGates` lists.

## Main results

* `Cslib.Crypto.PseudorandomFunction.yaoSemiHonestSecure_pointPermute`
* `Cslib.Crypto.CircularCorrelationRobust.yaoSemiHonestSecure_halfGates`

## References

* [Y. Lindell, B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009]
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole: Reducing Data Transfer in Garbled
  Circuits using Half Gates*][ZahurRosulekEvans2015]
-/

public section

namespace Cslib.Crypto

open Garbling Protocols.MPC Probability Turing.MultiTapeTM

/-- **Yao's protocol over point-and-permute garbling is semi-honest secure** in the
oblivious-transfer hybrid model, against the corruption of either party, for every pseudorandom
function `family` and every PPT sampler of the public parameters: a step towards Theorem 7 of
[LindellPinkas2009], with the differences that `Scheme.PrvSimSecureUniversal.yaoSemiHonestSecure`
lists. The garbling simulator is `PointPermute.simWord family`, which serves every adversary
(`PseudorandomFunction.negligible_prvSimAdvantage_simWord`), with the topology as side
information. -/
theorem PseudorandomFunction.yaoSemiHonestSecure_pointPermute
    {family : List Bool → List Bool → List Bool} (h : PseudorandomFunction family)
    {samp : ℕ → ProbComp (Yao.Params (PointPermute.scheme family))}
    (hsamp : IsPPTOn encUnary (Yao.encParams encValidCircuit) samp) (i : Fin 2) :
    (Yao.family (PointPermute.scheme family)).SemiHonestSecure (fun n => ProbComp.eval (samp n))
      {i} (Yao.encoding _ encValidCircuit) :=
  Scheme.PrvSimSecureUniversal.yaoSemiHonestSecure (Φ := phiTopo) (encΛ := encValidTopo)
    ⟨PointPermute.simWord family, PointPermute.isPPTOn_simWord h.polyTime,
      fun _ _ _ hB => h.negligible_prvSimAdvantage_simWord hB⟩
    (PointPermute.scheme_isEfficient h.polyTime) rfl (PointPermute.scheme_isValid family).correct
    phiTopo_polyTime hsamp i

/-- **Yao's protocol over half-gates garbling is semi-honest secure** in the oblivious-transfer
hybrid model, against the corruption of either party, for every circular correlation robust hash
family `hash` and every PPT sampler of the public parameters: a step towards Theorem 7 of
[LindellPinkas2009], with the differences that `Scheme.PrvSimSecureUniversal.yaoSemiHonestSecure`
lists. The garbling simulator is `HalfGates.simWord hash`, which serves every adversary
(`CircularCorrelationRobust.negligible_prvSimAdvantage_simWord`), with the circuit as side
information. -/
theorem CircularCorrelationRobust.yaoSemiHonestSecure_halfGates
    {hash : List Bool → List Bool → List Bool} (h : CircularCorrelationRobust hash)
    {samp : ℕ → ProbComp (Yao.Params (HalfGates.scheme hash))}
    (hsamp : IsPPTOn encUnary (Yao.encParams encXorAndCircuit) samp) (i : Fin 2) :
    (Yao.family (HalfGates.scheme hash)).SemiHonestSecure (fun n => ProbComp.eval (samp n))
      {i} (Yao.encoding _ encXorAndCircuit) :=
  Scheme.PrvSimSecureUniversal.yaoSemiHonestSecure (Φ := SideInfo.circ (HalfGates.scheme hash))
    (encΛ := encXorAndCircuit)
    ⟨HalfGates.simWord hash, HalfGates.isPPTOn_simWord h.polyTime,
      fun _ _ _ hB => h.negligible_prvSimAdvantage_simWord hB⟩
    (HalfGates.scheme_isEfficient h.polyTime) rfl (HalfGates.scheme_correct hash) .id' hsamp i

end Cslib.Crypto
