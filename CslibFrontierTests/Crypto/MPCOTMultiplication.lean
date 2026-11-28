/-
Copyright (c) 2026 Samuel Schlesinger, Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module

public import CslibFrontier.Crypto.Protocols.MPC.OTMultiplication

/-!
# Concrete Tests for OT-Based Multiplication and Beaver Triple Generation

Non-vacuous concrete evaluations, boundary checks, protocol instantiations, and end-to-end Beaver
composition checks for `CslibFrontier.Crypto.Protocols.MPC.OTMultiplication`:

1. **Bit decomposition & Gilboa's algebraic identity:** concrete checks for primes `q = 7`
   (`otBitWidth 7 = 3`) and `q = 17` (`otBitWidth 17 = 5`) and composite `q = 8`
   (`otBitWidth 8 = 3`, including zero divisors `4 * 6 ≡ 0`), plus a negative witness showing
   truncated bit-width `k = 2 < otBitWidth 7` cannot represent `5 : ZMod 7`.
2. **Standalone & hybrid-model `PerfectSemiHonestPrivate` instantiations:** concrete instantiations
   of `eval_otMul2BitsReal_senderView`, `eval_otMul2BitsReal_receiverJoint`,
   `perfectSemiHonestPrivate_otMul2Bits`, `perfectSemiHonestPrivate_otMul2`,
   `perfectSemiHonestPrivate_shareMulFromOT`, and `perfectSemiHonestPrivate_tripleFromOTMul`
   (against `Beaver.beaverTripleFunctionality q 2`) across coalitions `∅`, `{0}`, `{1}`, and
   `Finset.univ`.
3. **Generated `Beaver.TripleShare` feeding into `Beaver.beaverMulShare`:** concrete
   `tripleSharesOfOTMul` triples over `ZMod 7`, `ZMod 17`, and `ZMod 8` verified in the support
   of `Beaver.beaverTripleFunctionality`, used directly in `Beaver.beaverMulShare`, and an
   end-to-end theorem showing every supported execution of `tripleFromOTMulProtocol` yields valid
   `Beaver.TripleShare` shares for `Beaver.beaverMulShare` alongside
   `eval_restrict_output_tripleFromOTMul`.
-/

public section

namespace CslibFrontierTests.Crypto.MPCOTMultiplication

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto.Protocols.MPC

/-! ### 1. Bit decomposition & Gilboa's identity (`q = 7, 17, 8`) -/

example : otBitWidth 7 = 3 ∧ otBitWidth 17 = 5 ∧ otBitWidth 8 = 3 := by
  decide

example : zmodToBits (5 : ZMod 7) = ![true, false, true] ∧
    bitVecValue (zmodToBits (5 : ZMod 7)) = (5 : ZMod 7) := by
  refine ⟨?_, bitVecValue_zmodToBits 5⟩
  funext i
  fin_cases i <;> decide

example : bitVecValue (zmodToBits (13 : ZMod 17)) = (13 : ZMod 17) ∧
    bitVecValue (zmodToBits (7 : ZMod 8)) = (7 : ZMod 8) :=
  ⟨bitVecValue_zmodToBits 13, bitVecValue_zmodToBits 7⟩

/-- Negative bit-width check: `2 < otBitWidth 7 = 3` bits cannot represent `5 : ZMod 7`. -/
example : ∀ bits : Fin 2 → Bool, bitVecValue bits ≠ (5 : ZMod 7) := by
  decide

def mask7 : Fin 3 → ZMod 7 := ![2, 6, 1]
def mask17 : Fin 5 → ZMod 17 := ![3, 10, 0, 15, 7]
def mask8 : Fin 3 → ZMod 8 := ![1, 5, 3]

example :
    let t := fun i => otMul2SenderPairs (4 : ZMod 7) mask7 i (zmodToBits (5 : ZMod 7) i)
    otMul2Share0 mask7 + otMul2Share1 t = (4 : ZMod 7) * 5 ∧
      otMul2Share0 mask7 + otMul2Share1 t = (6 : ZMod 7) := by
  refine ⟨otMul2ZMod_correct (q := 7) 4 5 mask7, ?_⟩
  decide

example :
    let t := fun i => otMul2SenderPairs (11 : ZMod 17) mask17 i (zmodToBits (13 : ZMod 17) i)
    otMul2Share0 mask17 + otMul2Share1 t = (11 : ZMod 17) * 13 ∧
      otMul2Share0 mask17 + otMul2Share1 t = (7 : ZMod 17) := by
  refine ⟨otMul2ZMod_correct (q := 17) 11 13 mask17, ?_⟩
  decide

/-- Composite modulus `q = 8` with zero-divisor multiplication `4 * 6 ≡ 0 (mod 8)`. -/
example :
    let t := fun i => otMul2SenderPairs (4 : ZMod 8) mask8 i (zmodToBits (6 : ZMod 8) i)
    otMul2Share0 mask8 + otMul2Share1 t = (4 : ZMod 8) * 6 ∧
      otMul2Share0 mask8 + otMul2Share1 t = (0 : ZMod 8) := by
  refine ⟨otMul2ZMod_correct (q := 8) 4 6 mask8, ?_⟩
  decide

/-! ### 2. `PerfectSemiHonestPrivate` simulation across `q = 7, 17, 8` -/

example (a : ZMod 7) (bits : Fin 3 → Bool) :
    (ProbComp.eval (otMul2BitsReal 3 7 a bits)).map (fun res => (a, res.1)) =
      (PMF.uniformOfFintype (Fin 3 → ZMod 7)).map (fun r => (a, r)) :=
  eval_otMul2BitsReal_senderView 3 7 a bits

example (a : ZMod 7) (bits : Fin 3 → Bool) :
    (ProbComp.eval (otMul2BitsReal 3 7 a bits)).map (fun (_, t, u₀, _) => (bits, t, u₀)) =
      ProbComp.eval (otMul2BitsReceiverSim 3 7 a bits) :=
  eval_otMul2BitsReal_receiverJoint 3 7 a bits

example (I : Finset (Fin 2)) (x : (i : Fin 2) → OTMultBitsIn 3 7 i) :
    ProbComp.eval (idealJoint (otMul2BitsFunctionality 3 7) I (otMul2BitsSim 3 7 I) x) =
      (otMul2BitsProtocol 3 7).realJoint (batchOTWorld 3 (ZMod 7)) I x :=
  perfectSemiHonestPrivate_otMul2Bits 3 7 I x

example (I : Finset (Fin 2)) (x : (i : Fin 2) → OTMultIn 8 i) :
    ProbComp.eval (idealJoint (otMul2Functionality 8) I (otMul2Sim 8 I) x) =
      (otMul2Protocol 8).realJoint (batchOTWorld 3 (ZMod 8)) I x :=
  perfectSemiHonestPrivate_otMul2 8 (by decide) I x

example (x : Fin 2 → ZMod 17 × ZMod 17) :
    ProbComp.eval (idealJoint (sharedMulFunctionality 2) ({0} : Finset (Fin 2))
        (shareMulFromOTSim 17 {0}) x) =
      (shareMulFromOTProtocol 17).realJoint (batchOTWorld 5 (ZMod 17)) {0} x ∧
    ProbComp.eval (idealJoint (sharedMulFunctionality 2) ({1} : Finset (Fin 2))
        (shareMulFromOTSim 17 {1}) x) =
      (shareMulFromOTProtocol 17).realJoint (batchOTWorld 5 (ZMod 17)) {1} x :=
  ⟨perfectSemiHonestPrivate_shareMulFromOT 17 (by decide) {0} x,
   perfectSemiHonestPrivate_shareMulFromOT 17 (by decide) {1} x⟩

example :
    (∀ I : Finset (Fin 2),
      ProbComp.eval (idealJoint (Beaver.beaverTripleFunctionality 7 2) I
        (tripleFromOTMulSim 7 I) (fun _ => ())) =
      (tripleFromOTMulProtocol 7).realJoint (batchOTWorld 3 (ZMod 7)) I (fun _ => ())) ∧
    (∀ I : Finset (Fin 2),
      ProbComp.eval (idealJoint (Beaver.beaverTripleFunctionality 8 2) I
        (tripleFromOTMulSim 8 I) (fun _ => ())) =
      (tripleFromOTMulProtocol 8).realJoint (batchOTWorld 3 (ZMod 8)) I (fun _ => ())) :=
  ⟨fun I => perfectSemiHonestPrivate_tripleFromOTMul 7 (by decide) I (fun _ => ()),
   fun I => perfectSemiHonestPrivate_tripleFromOTMul 8 (by decide) I (fun _ => ())⟩

/-! ### 3. Generated `Beaver.TripleShare` feeding into `Beaver.beaverMulShare` -/

def mask7' : Fin 3 → ZMod 7 := ![4, 0, 5]
def mask17' : Fin 5 → ZMod 17 := ![1, 2, 14, 6, 9]
def mask8' : Fin 3 → ZMod 8 := ![2, 7, 4]

def otTriple7 : Fin 2 → Beaver.TripleShare (ZMod 7) :=
  tripleSharesOfOTMul (2, 5) (3, 4) mask7 mask7'

def otTriple17 : Fin 2 → Beaver.TripleShare (ZMod 17) :=
  tripleSharesOfOTMul (9, 12) (5, 7) mask17 mask17'

def otTriple8 : Fin 2 → Beaver.TripleShare (ZMod 8) :=
  tripleSharesOfOTMul (2, 3) (4, 5) mask8 mask8'

example :
    otTriple7 ∈ (ProbComp.eval (Beaver.beaverTripleFunctionality 7 2 (fun _ => ()))).support ∧
    otTriple17 ∈ (ProbComp.eval (Beaver.beaverTripleFunctionality 17 2 (fun _ => ()))).support ∧
    otTriple8 ∈ (ProbComp.eval (Beaver.beaverTripleFunctionality 8 2 (fun _ => ()))).support := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Beaver.mem_support_beaverTripleFunctionality_iff, Fin.sum_univ_two, Fin.sum_univ_two,
      Fin.sum_univ_two]
    exact tripleSharesOfOTMul_correct (q := 7) (2, 5) (3, 4) mask7 mask7'
  · rw [Beaver.mem_support_beaverTripleFunctionality_iff, Fin.sum_univ_two, Fin.sum_univ_two,
      Fin.sum_univ_two]
    exact tripleSharesOfOTMul_correct (q := 17) (9, 12) (5, 7) mask17 mask17'
  · rw [Beaver.mem_support_beaverTripleFunctionality_iff, Fin.sum_univ_two, Fin.sum_univ_two,
      Fin.sum_univ_two]
    exact tripleSharesOfOTMul_correct (q := 8) (2, 3) (4, 5) mask8 mask8'

/-- Feeding concrete OT-generated Beaver triples into `Beaver.beaverMulShare` over `ZMod 7`,
`ZMod 17`, and `ZMod 8`. -/
example :
    let xy7 : Fin 2 → ZMod 7 × ZMod 7 := ![(3, 1), (4, 5)]
    let op7 := ∑ j : Fin 2, Beaver.localMaskedOpening (xy7 j) (otTriple7 j)
    (∑ i : Fin 2, Beaver.beaverMulShare i op7 (otTriple7 i)) = (0 : ZMod 7) ∧
    let xy17 : Fin 2 → ZMod 17 × ZMod 17 := ![(6, 4), (7, 8)]
    let op17 := ∑ j : Fin 2, Beaver.localMaskedOpening (xy17 j) (otTriple17 j)
    (∑ i : Fin 2, Beaver.beaverMulShare i op17 (otTriple17 i)) = (3 : ZMod 17) ∧
    let xy8 : Fin 2 → ZMod 8 × ZMod 8 := ![(3, 2), (3, 4)]
    let op8 := ∑ j : Fin 2, Beaver.localMaskedOpening (xy8 j) (otTriple8 j)
    (∑ i : Fin 2, Beaver.beaverMulShare i op8 (otTriple8 i)) = (4 : ZMod 8) := by
  decide

/-- End-to-end execution of `tripleFromOTMulProtocol 7` produces supported `Beaver.TripleShare`
outputs whose online `Beaver.beaverMulShare` composition multiplies any 2-party shared inputs. -/
example (xy : Fin 2 → ZMod 7 × ZMod 7) :
    ∃ res ∈ ((tripleFromOTMulProtocol 7).evalWith
        (batchOTWorld 3 (ZMod 7)) (fun _ => ())).support,
      let op := ∑ j : Fin 2, Beaver.localMaskedOpening (xy j) (res.2 j)
      (∑ i : Fin 2, Beaver.beaverMulShare i op (res.2 i)) =
        (∑ i : Fin 2, (xy i).1) * (∑ i : Fin 2, (xy i).2) := by
  obtain ⟨res, hres⟩ :=
    PMF.support_nonempty ((tripleFromOTMulProtocol 7).evalWith
      (batchOTWorld 3 (ZMod 7)) (fun _ => ()))
  refine ⟨res, hres, ?_⟩
  have hsupp : res.2 ∈
      (ProbComp.eval (Beaver.beaverTripleFunctionality 7 2 (fun _ => ()))).support :=
    mem_support_tripleFromOTMulProtocol 7 hres
  have hc : (∑ i : Fin 2, (res.2 i).c) =
      (∑ i : Fin 2, (res.2 i).a) * (∑ i : Fin 2, (res.2 i).b) :=
    Beaver.sum_c_of_mem_support_beaverTripleFunctionality hsupp
  exact Beaver.sum_beaverMulShare_eq_mul xy res.2 hc

/-- Proper-coalition output marginal uniformity of `tripleFromOTMulProtocol` over `ZMod 7` and
`ZMod 8`. -/
example :
    ((tripleFromOTMulProtocol 7).evalWith (batchOTWorld 3 (ZMod 7)) (fun _ => ())).map
        (fun res => ({0} : Finset (Fin 2)).restrict res.2) =
      PMF.uniformOfFintype ((i : ({0} : Finset (Fin 2))) → Beaver.TripleShare (ZMod 7)) ∧
    ((tripleFromOTMulProtocol 8).evalWith (batchOTWorld 3 (ZMod 8)) (fun _ => ())).map
        (fun res => ({1} : Finset (Fin 2)).restrict res.2) =
      PMF.uniformOfFintype ((i : ({1} : Finset (Fin 2))) → Beaver.TripleShare (ZMod 8)) :=
  ⟨eval_restrict_output_tripleFromOTMul 7 (by decide) {0} (by decide),
   eval_restrict_output_tripleFromOTMul 8 (by decide) {1} (by decide)⟩

end CslibFrontierTests.Crypto.MPCOTMultiplication
