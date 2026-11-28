/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Truncated
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.DescribedContraction
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.EntryContraction
public import CslibFrontier.Computability.GenericRAM.Native.IndexFold
import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContractionPolyTime
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContractionSchedule
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# The reduction of truncation order `ℓ` as a native machine

The reduction of `CslibFrontier/Computability/Circuit/Frontier/TensorNetwork/Truncated.lean`
(`Cslib.Circuits.Frontier.DescribedNetwork.interpContract`) contracts specialized networks over
`A_P = (ℤ / 2 ^ P)[U] / (f)` and interpolates. This file runs it as one native machine around any
native certificate of the contraction over `A_P` (`engineCertificate`), with the precision `P` and
the truncation order `ℓ` in unary.

**Polynomial-time steps.** Specializing a network at a point (`DescribedNetwork.specNet_polyTime`),
the binary-digit points (`DescribedNetwork.digitPoints_polyTime`), the inputs of the contractions
(`coreInput_polyTime`) and reading the truncated contraction off the interpolant
(`interpRecover_polyTime`, `engineRecover_polyTime`) are polynomial-time.

**The loop.** The machine visits the digit points with the binary-index fold
`Cslib.GenericRAM.IndexFold`, keeping the index, the input and the values so far; each round
calls the given certificate once (`engineStep`, `engineStepCertificate`, `run_engineStep`). Then it
interpolates (`engineRecover`).

**Direct summation.** A native certificate of the entries gives one of the specialized entries
(`specEntryCertificate`: the entry, then Horner's rule), hence direct summation over `A_P` of a
specialized network (`directCoreCertificate`). Through the reduction at the modulus
`FastContraction.modulus n` for `n = (ℓ - 1) k + 1` points, which has enough residues
(`le_two_pow_length_modulus`), this computes the truncated contraction on every input
(`truncDirectCertificate`). Its cost is that of direct summation.

The time and space of the loop are bounded in
`CslibFrontier/Computability/Circuit/Frontier/TensorNetwork/TruncatedResources.lean`. With the
contraction of Theorem D.1 at `ℓ = 1` over `A_P` in place of direct summation, that bound gives
Theorem D.1 at truncation order `ℓ` (#1538).

## Main definitions

* `Cslib.Circuits.Frontier.encSpecDesc`, `Cslib.Circuits.Frontier.encTrunc`,
  `Cslib.Circuits.Frontier.encCore`, `Cslib.Circuits.Frontier.encEngine`,
  `Cslib.Circuits.Frontier.encEngineState`: encodings.
* `Cslib.Circuits.Frontier.specEntryCertificate`: the native evaluator of specialized entries.
* `Cslib.Circuits.Frontier.engineCertificate`: the reduction around a contraction over `A_P`.
* `Cslib.Circuits.Frontier.directCoreCertificate`: direct summation over `A_P`.
* `Cslib.Circuits.Frontier.truncDirectCertificate`: the truncated contraction by direct summation.

## Main results

* `Cslib.Circuits.Frontier.DescribedNetwork.specNet_polyTime`,
  `Cslib.Circuits.Frontier.interpRecover_polyTime`: polynomial-time steps.
* `Cslib.Circuits.Frontier.run_engineStep`, `Cslib.Circuits.Frontier.interpContract_eq_run`: the
  loop computes the reduction.
* `Cslib.Circuits.Frontier.interpContract_direct_eq`: direct summation through the reduction is
  the truncated contraction.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53).
-/

public section

namespace Cslib.Circuits.Frontier

open Turing.MultiTapeTM Cslib.GenericRAM GaloisRingArith

variable {T : Type} (encT : T ↪ List Bool)

/-- The encoding of the data `(P, ℓ, fl, ζ)` of a specialization: `P` and `ℓ` in unary, the
coefficients of the modulus and the point in binary. -/
abbrev encSpecData : ℕ × ℕ × List ℕ × List ℕ ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair (encList encNat) (encList encNat)))

/-- The encoding of a specialized descriptor: the original descriptor, then the data of the
specialization. -/
abbrev encSpecDesc : SpecDesc T ↪ List Bool := encPair encT encSpecData

variable {encT}

/-- The first `ℓ` coefficients as constant coefficient lists, from `ℓ` in unary. -/
theorem constCoeffs_polyTime :
    ComputableInPolyTime (fun q : ℕ × List ℕ => constCoeffs q.1 q.2)
      (encPair encUnary (encList encNat)) encPoly :=
  ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.range.comp (ComputableInPolyTime.fst _ _))
    (ComputableInPolyTime.cons'
      (computableInPolyTime_getD
        (ComputableInPolyTime.fst (encPair encUnary (encList encNat)) encUnary).snd'
        (ComputableInPolyTime.snd _ _))
      (ComputableInPolyTime.const []))

/-- **Horner's rule on the first `ℓ` coefficients**, from the data of a specialization and a
coefficient list, with `P` and `ℓ` in unary. -/
theorem horner_polyTime :
    ComputableInPolyTime
      (fun (((P, ℓ, fl, ζ), c) : (ℕ × ℕ × List ℕ × List ℕ) × List ℕ) =>
        peval P fl (constCoeffs ℓ c) ζ)
      (encPair encSpecData (encList encNat)) (encList encNat) := by
  have hd := ComputableInPolyTime.fst encSpecData (encList encNat)
  have h := computableInPolyTime_peval hd.fst' hd.snd'.snd'.fst'
    (constCoeffs_polyTime.comp
      (hd.snd'.fst'.prod (ComputableInPolyTime.snd encSpecData (encList encNat))))
    hd.snd'.snd'.snd'
  exact h

variable (entry : T → List Bool → List ℕ)

/-- **The native evaluator of specialized entries**, from a native certificate of the entries:
evaluate the original entry, then apply Horner's rule in `A_P`. -/
@[expose] noncomputable def specEntryCertificate
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) :
    NativeCertificate (fun q : SpecDesc T × List Bool => specEntry entry q.1 q.2)
      (encPair (encSpecDesc encT) encBits) (encList encNat) :=
  ((NativeCertificate.ofPolyTime horner_polyTime).comp
    ((NativeCertificate.ofPolyTime
        ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _))).prod
      (ce.comp (NativeCertificate.ofPolyTime
        ((((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _))).prod
          (ComputableInPolyTime.snd _ _)))))).congr fun _ => rfl

namespace DescribedNetwork

/-- **Specializing is polynomial-time**: from the data `(P, ℓ, fl, ζ)` and the network to the
specialized network. -/
theorem specNet_polyTime :
    ComputableInPolyTime
      (fun (((P, ℓ, fl, ζ), G) : (ℕ × ℕ × List ℕ × List ℕ) × DescribedNetwork T) =>
        specNet P ℓ fl ζ G)
      (encPair encSpecData (encDescribed encT)) (encDescribed (encSpecDesc encT)) := by
  let encIn := encPair encSpecData (encDescribed encT)
  have hG := ComputableInPolyTime.snd encSpecData (encDescribed encT)
  have hs := ComputableInPolyTime.snd encIn (encPair (encList encNat) encT)
  have h := (ComputableInPolyTime.of_eq (encIn := encPair encUnary
    (encList (encPair (encList encNat) (encSpecDesc encT))))
    (encOut := encDescribed (encSpecDesc encT))
    (f := fun p : ℕ × List (List ℕ × SpecDesc T) => (⟨p.1, p.2⟩ : DescribedNetwork (SpecDesc T)))
    fun _ => rfl).comp ((numEdges_polyTime.comp hG).prod
      (ComputableInPolyTime.mapWithInput (f := fun q v => (v.1, (v.2, q.1)))
        (vertices_polyTime.comp hG)
        (hs.fst'.prod (hs.snd'.prod
          (ComputableInPolyTime.fst encIn (encPair (encList encNat) encT)).fst'))))
  exact h

/-- **The binary-digit points are polynomial-time**, from the number of coordinates and the
number of points in unary. -/
theorem digitPoints_polyTime :
    ComputableInPolyTime
      (fun q : ℕ × ℕ => (List.range q.2).map (FastContraction.digits q.1))
      (encPair encUnary encUnary) encElems :=
  ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.range.comp (ComputableInPolyTime.snd _ _))
    (FastContraction.digits_polyTime.comp
      ((ComputableInPolyTime.fst (encPair encUnary encUnary) encUnary).fst'.prod
        (ComputableInPolyTime.snd _ _)))

end DescribedNetwork

/-- **Reading off the interpolant is polynomial-time**, with `P` and `ℓ` in unary. -/
theorem interpRecover_polyTime :
    ComputableInPolyTime
      (fun ((P, ℓ, fl, pts, ys) : ℕ × ℕ × List ℕ × List (List ℕ) × List (List ℕ)) =>
        interpRecover P ℓ fl pts ys)
      (encPair encUnary (encPair encUnary (encPair (encList encNat) (encPair encElems encElems))))
      (encList encNat) := by
  let encR := encPair encUnary (encPair (encList encNat) (encPair encElems encElems))
  have hP := ComputableInPolyTime.fst encUnary encR
  have hr := ComputableInPolyTime.snd encUnary encR
  have hI := computableInPolyTime_interp hP hr.snd'.fst' hr.snd'.snd'.fst' hr.snd'.snd'.snd'
  have h1 := ComputableInPolyTime.fst (encPair encUnary encR) encUnary
  have hq : ComputableInPolyTime
      (fun q : (ℕ × ℕ × List ℕ × List (List ℕ) × List (List ℕ)) × ℕ =>
        ((interp q.1.1 q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2).getD q.2 []).getD 0 0 % 2 ^ q.1.1)
      (encPair (encPair encUnary encR) encUnary) encNat :=
    computableInPolyTime_mod_two_pow
      (computableInPolyTime_getD
        ((ComputableInPolyTime.listGetD (encA := encList encNat) []).comp
          ((hI.comp h1).prod (ComputableInPolyTime.snd _ _)))
        (ComputableInPolyTime.const 0)) (hP.comp h1)
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hr.fst') hq

/-! ### The reduction as a streaming loop -/

/-- The encoding of an input `(P, ℓ, r, G)` of the truncated contraction: `P` and `ℓ` in unary,
`r` in binary, then the network. -/
abbrev encTrunc (encT : T ↪ List Bool) : ℕ × ℕ × ℕ × DescribedNetwork T ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encNat (DescribedNetwork.encDescribed encT)))

/-- The encoding of an input `(P, fl, r, G')` of a contraction over `A_P` of specialized
networks: `P` in unary, the modulus, `r` in binary, then the specialized network. -/
abbrev encCore (encT : T ↪ List Bool) :
    ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc T) ↪ List Bool :=
  encPair encUnary (encPair (encList encNat)
    (encPair encNat (DescribedNetwork.encDescribed (encSpecDesc encT))))

/-- The input of the reduction: the modulus and the input `(P, ℓ, r, G)`. -/
abbrev encEngine (encT : T ↪ List Bool) : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T ↪ List Bool :=
  encPair (encList encNat) (encTrunc encT)

/-- The state `(k, (y, ys))` of the loop of the reduction: the index `k` in binary, framed, the
input `y` of the reduction (`encEngine`), framed, then the values `ys` so far, each framed, an
element of `A_P` as its coefficient list of framed binary numbers. The last component is the
layout of `encElems` but is spelled `encList (encList encNat)` so that the `omega` steps of
`TruncatedResources` see the expected encoding constructors after simplifying `encEngineState`. -/
abbrev encEngineState (encT : T ↪ List Bool) :
    ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ)) ↪ List Bool :=
  encPair encNat (encPair (encEngine encT) (encList (encList encNat)))

/-- The input `(P, fl, r, G')` of the contraction at the `k`-th digit point, for a modulus `fl` and
an input `(P, ℓ, r, G)`: `G'` is `G` specialized at that point. -/
@[expose] def coreInput :
    List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T → ℕ → ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc T)
  | (fl, P, ℓ, r, G), k =>
    (P, fl, r, DescribedNetwork.specNet P ℓ fl (FastContraction.digits fl.length k) G)

variable (core : ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc T) → List ℕ)

/-- **One round of the reduction** at the index `k`, for the modulus and input `y` and the values
`ys` so far: append the contraction at the `k`-th digit point. -/
@[expose] def engineStep :
    ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ)) →
      (List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ)
  | (k, (y, ys)) => (y, ys ++ [core (coreInput y k)])

/-- After `j` rounds, the values are the contractions at the first `j` digit points. -/
theorem run_engineStep (y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) (j : ℕ) :
    IndexFold.run (engineStep core) j (y, []) =
      (j, (y, (List.range j).map fun k => core (coreInput y k))) := by
  induction j with
  | zero => rfl
  | succ j ih => simp [IndexFold.run_succ, ih, IndexFold.step, engineStep, List.range_succ]

/-- **Recovery from a final state** `(k, ((fl, P, ℓ, r, G), ys))` of the loop: read the truncated
contraction off the interpolant of the values `ys` at the digit points. -/
@[expose] def engineRecover :
    ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ)) → List ℕ
  | (_, ((fl, P, ℓ, _, G), ys)) =>
    interpRecover P ℓ fl
      ((List.range (DescribedNetwork.pointCount ℓ G)).map (FastContraction.digits fl.length)) ys

/-- **The reduction is the streaming loop followed by recovery.** -/
theorem interpContract_eq_run (fl : List ℕ) (P ℓ r : ℕ) (G : DescribedNetwork T) :
    DescribedNetwork.interpContract core fl P ℓ r G =
      engineRecover (IndexFold.run (engineStep core) (DescribedNetwork.pointCount ℓ G)
        ((fl, P, ℓ, r, G), [])) := by
  rw [run_engineStep, DescribedNetwork.interpContract, List.map_map]
  rfl

/-- The binary digits are polynomial-time from the number in binary. -/
theorem digits_polyTime_binary :
    ComputableInPolyTime (fun q : ℕ × ℕ => FastContraction.digits q.1 q.2)
      (encPair encUnary encNat) (encList encNat) :=
  ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.range.comp (ComputableInPolyTime.fst _ _))
    (ComputableInPolyTime.ite (encMid := encNat)
      (ComputableInPolyTime.binary_testBit
        (ComputableInPolyTime.fst (encPair encUnary encNat) encUnary).snd'
        (ComputableInPolyTime.snd _ _))
      (ComputableInPolyTime.const 1) (ComputableInPolyTime.const 0))

/-- The number of points is polynomial-time, in unary. -/
theorem pointCount_polyTime :
    ComputableInPolyTime (fun ((_, _, ℓ, _, G) : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) =>
      DescribedNetwork.pointCount ℓ G) (encEngine encT) encUnary := by
  have hx := ComputableInPolyTime.snd (encList encNat) (encTrunc encT)
  have h := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.unary_sub' hx.snd'.fst' (ComputableInPolyTime.const 1))
      ((ComputableInPolyTime.length_list _).comp
        (DescribedNetwork.vertices_polyTime.comp hx.snd'.snd'.snd')))
    (ComputableInPolyTime.const 1)
  exact h

/-- The input of the contraction at a binary index is polynomial-time. -/
theorem coreInput_polyTime :
    ComputableInPolyTime
      (fun ((k, (y, _)) : ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ))) =>
        coreInput y k)
      (encEngineState encT) (encCore encT) := by
  let encRest := encPair (encEngine encT) (encList (encList encNat))
  have hy := (ComputableInPolyTime.snd encNat encRest).fst'
  have hfl := hy.fst'
  have hx := hy.snd'
  have hζ := digits_polyTime_binary.comp
    (((ComputableInPolyTime.length_list _).comp hfl).prod (ComputableInPolyTime.fst encNat encRest))
  have h := hx.fst'.prod (hfl.prod (hx.snd'.snd'.fst'.prod (DescribedNetwork.specNet_polyTime.comp
    ((hx.fst'.prod (hx.snd'.fst'.prod (hfl.prod hζ))).prod hx.snd'.snd'.snd'))))
  exact h

/-- The certificate of one round, from a certificate of the contraction over `A_P`. -/
@[expose] noncomputable def engineStepCertificate
    (cc : NativeCertificate core (encCore encT) (encList encNat)) :
    NativeCertificate (engineStep core) (encEngineState encT)
      (encPair (encEngine encT) (encList (encList encNat))) :=
  (NativeCertificate.ofPolyTime (ComputableInPolyTime.snd _ _).fst').prod
    ((NativeCertificate.ofPolyTime (ComputableInPolyTime.snoc (encList encNat))).comp
      ((NativeCertificate.ofPolyTime (ComputableInPolyTime.snd _ _).snd').prod
        (cc.comp (NativeCertificate.ofPolyTime coreInput_polyTime))))

/-- Recovery from the final state of the loop is polynomial-time. -/
theorem engineRecover_polyTime :
    ComputableInPolyTime (engineRecover (T := T))
      (encEngineState encT) (encList encNat) := by
  let S := ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ))
  let encS := encEngineState encT
  have hdata := ComputableInPolyTime.snd encNat (encPair (encEngine encT) encElems)
  have hy := hdata.fst'
  have hys := hdata.snd'
  have hfl : ComputableInPolyTime (fun p : S => p.2.1.1) encS (encList encNat) := hy.fst'
  have hP : ComputableInPolyTime (fun p : S => p.2.1.2.1) encS encUnary := hy.snd'.fst'
  have hℓ : ComputableInPolyTime (fun p : S => p.2.1.2.2.1) encS encUnary := hy.snd'.snd'.fst'
  have hpts : ComputableInPolyTime (fun p : S =>
      (List.range (DescribedNetwork.pointCount p.2.1.2.2.1 p.2.1.2.2.2.2)).map
        (FastContraction.digits p.2.1.1.length)) encS encElems :=
    DescribedNetwork.digitPoints_polyTime.comp
      (((ComputableInPolyTime.length_list _).comp hfl).prod (pointCount_polyTime.comp hy))
  have h := interpRecover_polyTime.comp (hP.prod (hℓ.prod (hfl.prod (hpts.prod hys))))
  exact h

/-- **The reduction as one native machine**, from a native certificate of the contraction over
`A_P` of specialized networks: the streaming loop over the digit points, keeping only the binary
index, the input and the values so far, then recovery. On input `(fl, (P, ℓ, r, G))` it computes
`interpContract core fl P ℓ r G`. -/
@[expose] noncomputable def engineCertificate
    (cc : NativeCertificate core (encCore encT) (encList encNat)) :
    NativeCertificate (fun ((fl, P, ℓ, r, G) : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) =>
        DescribedNetwork.interpContract core fl P ℓ r G)
      (encEngine encT) (encList encNat) :=
  ((NativeCertificate.ofPolyTime engineRecover_polyTime).comp
    (IndexFold.certificate
      (NativeCertificate.ofPolyTime (ComputableInPolyTime.unary_to_binary.comp pointCount_polyTime))
      (NativeCertificate.ofPolyTime
        (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const [])))
      (engineStepCertificate core cc))).congr fun ⟨fl, P, ℓ, r, G⟩ => by
    simp only [Function.comp_apply]
    rw [interpContract_eq_run]

/-! ### Direct summation as the contraction over `A_P` -/

/-- **Direct summation over a specialized network**, as a contraction over `A_P` with the input
`(P, fl, r, G')`, from a native certificate of the entries. -/
@[expose] noncomputable def directCoreCertificate
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) :
    NativeCertificate
      (fun ((P, fl, _, G') : ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc T)) =>
        DescribedNetwork.sumValue SumOps.galois (specEntry entry) (P, fl) G')
      (encCore encT) (encList encNat) :=
  EntryContraction.directCore (specEntry entry) (specEntryCertificate entry ce)

/-- `n ≤ 2 ^ deg f` for the modulus `FastContraction.modulus n`: it has enough residues for `n`
points. -/
theorem le_two_pow_length_modulus (n : ℕ) : n ≤ 2 ^ (FastContraction.modulus n).length := by
  have h4 := FastContraction.four_mul_log_le_length_modulus n
  have hlt := Nat.lt_pow_succ_log_self one_lt_two n
  rcases Nat.eq_zero_or_pos (Nat.log 2 n) with h0 | hpos
  · exact (show n ≤ 1 by simpa [h0] using hlt).trans Nat.one_le_two_pow
  · exact hlt.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- Choosing the modulus `FastContraction.modulus n` for `n = (ℓ - 1) k + 1` points is
polynomial-time. -/
theorem modulusChoice_polyTime :
    ComputableInPolyTime
      (fun ((P, ℓ, r, G) : ℕ × ℕ × ℕ × DescribedNetwork T) =>
        (FastContraction.modulus (DescribedNetwork.pointCount ℓ G), (P, ℓ, r, G)))
      (encTrunc encT) (encEngine encT) := by
  have h := (FastContraction.modulus_polyTime.comp ((pointCount_polyTime (encT := encT)).comp
    ((ComputableInPolyTime.const ([] : List ℕ)).prod ComputableInPolyTime.id'))).prod
    ComputableInPolyTime.id'
  exact h

/-- **Direct summation through the reduction computes the truncated contraction**, at the modulus
`FastContraction.modulus n` for `n = (ℓ - 1) k + 1` points. -/
theorem interpContract_direct_eq (P ℓ r : ℕ) (G : DescribedNetwork T) :
    DescribedNetwork.interpContract
        (fun ((P, fl, _, G') : ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc T)) =>
          DescribedNetwork.sumValue SumOps.galois (specEntry entry) (P, fl) G')
        (FastContraction.modulus (DescribedNetwork.pointCount ℓ G)) P ℓ r G =
      G.truncContraction entry P ℓ :=
  DescribedNetwork.interpContract_eq (entry := entry)
    (FastContraction.irreducible_modulus (DescribedNetwork.pointCount ℓ G)) G
    (le_two_pow_length_modulus _) fun _ _ => DescribedNetwork.val_sumValue_galois (specEntry entry)
      (P, FastContraction.modulus (DescribedNetwork.pointCount ℓ G)) _

/-- **The truncated contraction by direct summation**, as one native machine on every input
`(P, ℓ, r, G)`: the reduction with direct summation over `A_P` at the modulus
`FastContraction.modulus n`, for `n = (ℓ - 1) k + 1` points. It is correct everywhere; its cost is
that of direct summation, exponential in the number of edges. -/
@[expose] noncomputable def truncDirectCertificate
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) :
    NativeCertificate
      (fun ((P, ℓ, _, G) : ℕ × ℕ × ℕ × DescribedNetwork T) => G.truncContraction entry P ℓ)
      (encTrunc encT) (encList encNat) :=
  ((engineCertificate _ (directCoreCertificate entry ce)).comp
    (NativeCertificate.ofPolyTime modulusChoice_polyTime)).congr fun ⟨P, ℓ, r, G⟩ =>
      interpContract_direct_eq entry P ℓ r G

end Cslib.Circuits.Frontier
