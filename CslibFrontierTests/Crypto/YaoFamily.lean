/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Protocols.MPC.Yao.Family
import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Efficient
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for Yao's protocol as a protocol family

A client of `CslibFrontier.Crypto.Protocols.MPC.Yao.Family` under module encapsulation.

Yao's protocol runs over point-and-permute garbling (`PointPermute.scheme`) with a keyed family
`xorFamily` computed in polynomial time, on one AND gate whose first input the garbler holds and
whose second the evaluator holds. In every run at a parameter `n ≥ 1` both parties output the AND
of the two bits. The scheme meets the hypotheses of `Yao.hybridSemiHonestSecure_garbler`: it
computes its coin count in polynomial time, it is correct, and its encoding is `projectiveEncode`;
so the family is semi-honest secure in the ideal `batchOTWorld` hybrid against a corrupted garbler
for every setup law.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.YaoFamily

open Cslib Cslib.Crypto Cslib.Crypto.Garbling Cslib.Crypto.Protocols.MPC Turing.MultiTapeTM

/-- One AND gate on two inputs: `n = 2`, `m = 1`, `q = 1`, reading wires `1` and `2`. -/
def andGate : ValidCircuit := ⟨⟨2, 1, 1, fun _ => 1, fun _ => 2, fun _ => (· && ·)⟩, by decide⟩

/-- A keyed family on words: the tweak XORed with copies of the key. -/
def xorFamily (key t : List Bool) : List Bool := List.zipWith xor (key ++ key) (t ++ t ++ t)

/-- The family `xorFamily` is computed in polynomial time. -/
theorem xorFamily_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => xorFamily p.1 p.2)
      (encPair encBits encBits) encBits := by
  polytime [xorFamily]

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

/-- **The hypotheses of `Yao.hybridSemiHonestSecure_garbler` hold for point-and-permute garbling**,
so Yao's protocol over it in the ideal `batchOTWorld` hybrid is semi-honest secure against a
corrupted garbler, for every setup law. -/
example (setup : ℕ → PMF (Yao.Params (PointPermute.scheme xorFamily))) :
    (Yao.family (PointPermute.scheme xorFamily)).SemiHonestSecure setup {0}
      (Yao.encoding _ encValidCircuit) :=
  Yao.hybridSemiHonestSecure_garbler (PointPermute.scheme_isEfficient xorFamily_polyTime).coins rfl
    (PointPermute.scheme_isValid xorFamily).correct setup

end CslibFrontierTests.Crypto.YaoFamily
