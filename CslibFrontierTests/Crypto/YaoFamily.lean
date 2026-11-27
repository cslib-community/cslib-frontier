/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Protocols.MPC.Yao.Family
import CslibFrontier.Crypto.Protocols.MPC.Yao.Instances
import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Efficient
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for Yao's protocol families (`Yao.oneSidedFamily` and `Yao.family`)

A client of `CslibFrontier.Crypto.Protocols.MPC.Yao.Family` and
`CslibFrontier.Crypto.Protocols.MPC.Yao.Instances` under module encapsulation.

Both the one-sided protocol family (`Yao.oneSidedFamily`, where party `0` outputs `[]` and party `1`
outputs the decoded gate output) and the two-output protocol family (`Yao.family`, where both
parties output the decoded gate output) are instantiated on one AND gate whose first input the
garbler holds and whose second the evaluator holds. In every run at `n ≥ 1` the parties compute the
expected outputs, both families satisfy unconditional semi-honest security against a corrupted
garbler for every setup law, and concrete PPT parameter samplers witness nonvacuity of the setup
hypotheses of `PseudorandomFunction.yaoOneSidedHybridSemiHonestSecure_pointPermute` and
`CircularCorrelationRobust.yaoOneSidedHybridSemiHonestSecure_halfGates` across all static coalitions
`I : Finset (Fin 2)`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.YaoFamily

open Cslib Cslib.Crypto Cslib.Crypto.Garbling Cslib.Crypto.Protocols.MPC Cslib.Probability
  Turing.MultiTapeTM

/-- One AND gate on two inputs: `n = 2`, `m = 1`, `q = 1`, reading wires `1` and `2`. -/
def andGate : ValidCircuit := ⟨⟨2, 1, 1, fun _ => 1, fun _ => 2, fun _ => (· && ·)⟩, by decide⟩

/-- A keyed family on words: the tweak XORed with copies of the key. -/
def xorFamily (key t : List Bool) : List Bool := List.zipWith xor (key ++ key) (t ++ t ++ t)

/-- The family `xorFamily` is computed in polynomial time. -/
theorem xorFamily_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => xorFamily p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hp := ComputableInPolyTime.id' (encIn := encPair encBits encBits)
  exact ComputableInPolyTime.bitsZipWithInput xor
    (hp.fst'.bitsAppend hp.fst')
    ((hp.snd'.bitsAppend hp.snd').bitsAppend hp.snd')

/-- The public parameters: the AND gate, with the garbler holding its first input. -/
def andParams : Yao.Params (PointPermute.scheme xorFamily) := ⟨andGate, 1, by decide⟩

/-- The inputs: the garbler's bit `a` and the evaluator's bit `b`. -/
def inputs (a b : Bool) : (i : Fin 2) → Yao.Input andParams i :=
  fun i => Fin.cases (motive := fun i => Yao.Input andParams i) (fun _ => a) (fun _ _ => b) i

/-- **Correctness on the AND gate.** In every run at a parameter `n ≥ 1`, both parties output the
AND of the garbler's bit and the evaluator's bit. -/
example {n : ℕ} (hn : 0 < n) (a b : Bool)
    {r : ((i : Fin 2) → PartyView (Yao.Input andParams) Yao.Coins (Yao.schedule andParams) i) ×
      (Fin 2 → List Bool)}
    (hr : r ∈ ((Yao.protocol _ n andParams).evalWith (batchOTWorld 1 (List Bool))
      (inputs a b)).support) :
    r.2 = fun _ => [a && b] := by
  rw [Yao.output_of_mem_support rfl (PointPermute.scheme_isValid xorFamily).correct hn andParams
    _ hr]
  cases a <;> cases b <;> decide

/-- **Correctness of `Yao.oneSidedProtocol` on the AND gate.** In every run at a parameter
`n ≥ 1`, the garbler outputs `[]` and the evaluator outputs `[a && b]`. -/
example {n : ℕ} (hn : 0 < n) (a b : Bool)
    {r : ((i : Fin 2) →
        PartyView (Yao.Input andParams) Yao.Coins (Yao.oneSidedSchedule andParams) i) ×
      (Fin 2 → List Bool)}
    (hr : r ∈ ((Yao.oneSidedProtocol _ n andParams).evalWith (batchOTWorld 1 (List Bool))
      (inputs a b)).support) :
    r.2 0 = [] ∧ r.2 1 = [a && b] := by
  rw [Yao.oneSided_output_of_mem_support rfl (PointPermute.scheme_isValid xorFamily).correct hn
    andParams _ hr]
  cases a <;> cases b <;> decide

/-- **The hypotheses of `Yao.hybridSemiHonestSecure_oneSided_garbler` hold for point-and-permute
garbling**, giving unconditional semi-honest security against a corrupted garbler in the ideal
`batchOTWorld` hybrid for every setup law. -/
example (setup : ℕ → PMF (Yao.Params (PointPermute.scheme xorFamily))) :
    (Yao.oneSidedFamily (PointPermute.scheme xorFamily)).SemiHonestSecure setup {0}
      (Yao.oneSidedEncoding _ encValidCircuit) :=
  Yao.hybridSemiHonestSecure_oneSided_garbler
    (PointPermute.scheme_isEfficient xorFamily_polyTime).coins rfl
    (PointPermute.scheme_isValid xorFamily).correct setup

/-- Deterministic PPT public-parameter sampler fixing the two-input AND gate at every security
parameter for `PointPermute.scheme`. -/
noncomputable def andParamSampler (family : List Bool → List Bool → List Bool) :
    ℕ → ProbComp (Yao.Params (PointPermute.scheme family)) :=
  fun _ => pure ⟨andGate, 1, show 1 ≤ 2 by decide⟩

theorem isPPTOn_andParamSampler (family : List Bool → List Bool → List Bool) :
    IsPPTOn encUnary (Yao.encParams (G := PointPermute.scheme family) encValidCircuit)
      (andParamSampler family) :=
  (ComputableInPolyTime.const
    (⟨andGate, 1, show 1 ≤ 2 by decide⟩ : Yao.Params (PointPermute.scheme family))).isPPTOn

/-- **Nonvacuous client of `PseudorandomFunction.yaoOneSidedHybridSemiHonestSecure_pointPermute`**
across all static coalitions `I : Finset (Fin 2)` with the certified PPT sampler
`andParamSampler`. -/
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    (I : Finset (Fin 2)) :
    (Yao.oneSidedFamily (PointPermute.scheme family)).SemiHonestSecure
      (fun n => ProbComp.eval (andParamSampler family n)) I
      (Yao.oneSidedEncoding _ encValidCircuit) :=
  hprf.yaoOneSidedHybridSemiHonestSecure_pointPermute (isPPTOn_andParamSampler family) I

/-- The two-input AND gate as an XOR–AND conventional circuit for `HalfGates.scheme`. -/
def andXorAndGate : XorAndCircuit := ⟨andGate, fun _ => Or.inr rfl⟩

/-- Deterministic PPT public-parameter sampler fixing `andXorAndGate` at every security parameter
for `HalfGates.scheme`. -/
noncomputable def andHalfGatesSampler (hash : List Bool → List Bool → List Bool) :
    ℕ → ProbComp (Yao.Params (HalfGates.scheme hash)) :=
  fun _ => pure ⟨andXorAndGate, 1, show 1 ≤ 2 by decide⟩

theorem isPPTOn_andHalfGatesSampler (hash : List Bool → List Bool → List Bool) :
    IsPPTOn encUnary (Yao.encParams (G := HalfGates.scheme hash) encXorAndCircuit)
      (andHalfGatesSampler hash) :=
  (ComputableInPolyTime.const
    (⟨andXorAndGate, 1, show 1 ≤ 2 by decide⟩ : Yao.Params (HalfGates.scheme hash))).isPPTOn

/-- **Nonvacuous client of `CircularCorrelationRobust.yaoOneSidedHybridSemiHonestSecure_halfGates`**
across all static coalitions `I : Finset (Fin 2)` with the certified PPT sampler
`andHalfGatesSampler`. -/
example {hash : List Bool → List Bool → List Bool} (hccr : CircularCorrelationRobust hash)
    (I : Finset (Fin 2)) :
    (Yao.oneSidedFamily (HalfGates.scheme hash)).SemiHonestSecure
      (fun n => ProbComp.eval (andHalfGatesSampler hash n)) I
      (Yao.oneSidedEncoding _ encXorAndCircuit) :=
  hccr.yaoOneSidedHybridSemiHonestSecure_halfGates (isPPTOn_andHalfGatesSampler hash) I

/-- **The hypotheses of `Yao.hybridSemiHonestSecure_garbler` hold for point-and-permute garbling**,
so Yao's protocol over it in the ideal `batchOTWorld` hybrid is semi-honest secure against a
corrupted garbler, for every setup law. -/
example (setup : ℕ → PMF (Yao.Params (PointPermute.scheme xorFamily))) :
    (Yao.family (PointPermute.scheme xorFamily)).SemiHonestSecure setup {0}
      (Yao.encoding _ encValidCircuit) :=
  Yao.hybridSemiHonestSecure_garbler (PointPermute.scheme_isEfficient xorFamily_polyTime).coins rfl
    (PointPermute.scheme_isValid xorFamily).correct setup

end CslibFrontierTests.Crypto.YaoFamily
