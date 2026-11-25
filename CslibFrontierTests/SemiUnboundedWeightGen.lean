/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Boolean.SemiUnbounded.WeightGenerator

/-!
# Tests for the native AND-level-scaled weight generator

Checked witnesses exercising:
1. Direct AND-level scaling (`scaleByLevel`), including level zero, positive levels, and zero
   accumulator, together with `scaleByLevel_inSpace`.
2. Retained-rank evaluation (`gateWeightRank`) with trailing-zero seed widths
   (`[true, false, false]` versus `[true]`), empty seeds, and OR/leaf gates at positive
   AND-levels returning `0`.
3. A concrete two-AND-level normal-form circuit on `Fin 5` instantiating
   `gateWeightRank_justesen_eq`, `evalInput_canonicalInput`, `generatedGateWeightBound_inSpace`,
   `generatedGateWeightBound_le_poly`, `gateWeightRank_inLogSpace`, and
   `generatedGateWeight_certified`.
4. Negative boundary witness (`x₁ ∨ x₂` without an AND first layer): `evalInput` agrees with
   `generatedGateWeight` and evaluates to `0` at the OR gate under every seed.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.SemiUnboundedWeightGen

open Cslib.Circuits.Boolean
open Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit
open Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.WeightGenerator
open Cslib.Code.JustesenFamily Cslib.Reachability.Hoza
open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

/-! ## 1. Direct AND-level scaling and retained-rank edge cases -/

example : scaleByLevel 0 7 = 7 ∧ scaleByLevel 2 5 = 180 ∧ scaleByLevel 3 0 = 0 := by
  decide

example :
    ComputableInSpace (fun p : ℕ × ℕ => scaleByLevel p.1 p.2)
      (encPair encNat encNat) encNat
      (fun p => (encPair encNat encNat p).length + p.1) :=
  scaleByLevel_inSpace

private def constBit (ctx : Bool) (_ : ℕ) : Bool := ctx

-- Rank 1 at width 3 has two trailing implicit zero bits (accumulating 36), scaled by 6^2 = 36
-- at AND-level 2; rank 1 at width 1 accumulates 1, giving 36 at AND-level 2.
example :
    gateWeightRank constBit ⟨⟨true, 1, 3⟩, 2, true⟩ = 1296 ∧
    gateWeightRank constBit ⟨⟨true, 1, 1⟩, 2, true⟩ = 36 ∧
    gateWeightRank constBit ⟨⟨true, 1, 3⟩, 2, false⟩ = 0 ∧
    gateWeightRank constBit ⟨⟨true, 0, 0⟩, 5, true⟩ = 0 := by
  decide +kernel

-- Standalone `evalInput` preserves width even when the raw seed ends in `false` bits, and zeroes
-- non-AND gates even at positive AND-levels.
example :
    evalInput ⟨⟨4, 2, false, 3⟩, [true, true, true]⟩ = 0 ∧
    evalInput ⟨⟨4, 3, true, 0⟩, []⟩ = 0 := by
  decide

-- Exact streaming agreement between `evalInput` and `gateWeightRank` on a seed with trailing
-- `false` bits.
example :
    let x : Input := ⟨⟨2, 1, true, 0⟩, [true, false, false]⟩
    evalInput x = gateWeightRank justesenCodeBit
      ⟨⟨(fieldContext 2 0, 0), ofBits x.seed, 3⟩, 1, true⟩ :=
  evalInput_eq_gateWeightRank ⟨⟨2, 1, true, 0⟩, [true, false, false]⟩

-- Direct space certificates for `gateWeightRank`, `generatedGateWeightBound`, and `evalInput`.
example :
    ComputableInSpace (gateWeightRank constBit) (encGateRequest encBool) encNat
      (fun q => (encGateRequest encBool q).length + q.seed.width + q.andLevel) :=
  gateWeightRank_inSpace encBool constBit (fst encBool encNat)

example :
    ComputableInSpace (fun p : ℕ × ℕ => generatedGateWeightBound p.1 p.2)
      (encPair encNat encNat) encNat
      (fun p => (encPair encNat encNat p).length + p.2) :=
  generatedGateWeightBound_inSpace

example :
    ComputableInSpace evalInput encInput encNat
      (fun x => (encInput x).length + x.header.andLevel + 1) :=
  evalInput_inSpace

-- Constant logspace request producer composes via `gateWeightRank_inLogSpace`.
example :
    let req : List Bool → GateRequest Bool := fun _ => ⟨⟨true, 1, 3⟩, 2, true⟩
    ComputableInLogSpace (fun w => gateWeightRank constBit (req w)) encBits encNat := by
  intro req
  refine gateWeightRank_inLogSpace encBool constBit (fst encBool encNat)
    (ComputableInLogSpace.const _) ?_
  refine ⟨(encGateRequest encBool ⟨⟨true, 1, 3⟩, 2, true⟩).length + 5, fun w => ?_⟩
  have hpos : 1 ≤ Nat.log2 (encBits w).length + 1 := Nat.le_add_left _ _
  dsimp only [req]
  nlinarith

/-! ## 2. Concrete normal-form circuit with two AND levels and OR gates at positive AND-levels

Gates on `Fin 5`:
* Layer 0 (leaf): `0 = true`
* Layer 1 (AND-level 0): `1 = AND(0)`, `2 = AND(0, 0)`
* Layer 2 (OR-level 0, `andLevel = 1`, `isAndGate = false`): `3 = OR(1, 2)`
* Layer 3 (AND-level 1, `isAndGate = true`): `4 = AND(3)`
-/

private def smallLayer : Fin 5 → ℕ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 3

private def smallKind : Fin 5 → GateKind (Fin 5)
  | ⟨0, _⟩ => .leaf true
  | ⟨1, _⟩ => .and (.unary 0)
  | ⟨2, _⟩ => .and (.binary 0 0)
  | ⟨3, _⟩ => .or
  | ⟨4, _⟩ => .and (.unary 3)

private def smallOrChild : Fin 5 → Fin 5 → Prop
  | ⟨3, _⟩, c => c = 1 ∨ c = 2
  | _, _ => False

private def smallCircuit : LayeredSemiUnboundedCircuit (Fin 5) where
  layer := smallLayer
  kind := smallKind
  orChild := smallOrChild
  layer_andUnary := by
    intro g c h
    fin_cases g <;> cases h <;> decide
  layer_andBinary := by
    intro g l r h
    fin_cases g <;> cases h
    decide
  layer_orChild := by
    intro g c hg hc
    fin_cases g <;> cases hg
    rcases hc with rfl | rfl <;> decide

private theorem smallCircuit_inNormalForm : smallCircuit.InNormalForm where
  leaf_of_layer_zero := by
    intro g h
    fin_cases g <;> first | exact ⟨_, rfl⟩ | (simp [smallCircuit, smallLayer] at h)
  and_of_odd := by
    intro g h
    fin_cases g <;>
      first
      | exact ⟨_, rfl⟩
      | (exfalso; rcases h with ⟨k, hk⟩; simp only [smallCircuit, smallLayer] at hk; omega)
  or_of_pos_even := by
    intro g hpos heven
    fin_cases g <;>
      first
      | rfl
      | (exfalso; rcases heven with ⟨k, hk⟩; simp only [smallCircuit, smallLayer] at hpos hk; omega)

-- OR gate `3` has `andLevel = 1 > 0` yet `isAndGate = false`, so both evaluators return `0`.
example (seed : Fin (codeLength 5 0) → Bool) :
    smallCircuit.andLevel 3 = 1 ∧
    smallCircuit.isAndGate 3 = false ∧
    evalInput (canonicalInput smallCircuit seed 3) = 0 := by
  refine ⟨rfl, rfl, ?_⟩
  rw [evalInput_canonicalInput]
  rfl

-- Retained-rank and standalone evaluators both match `generatedGateWeight` on every gate.
example (rank : Fin (2 ^ codeLength 5 0)) (g : Fin 5) :
    let seed := (Cslib.BitString.equivFin _).symm rank
    gateWeightRank justesenCodeBit
        ⟨⟨(fieldContext 5 0, g.val), rank.val, codeLength 5 0⟩,
          smallCircuit.andLevel g, smallCircuit.isAndGate g⟩ =
      evalInput (canonicalInput smallCircuit seed g) := by
  intro seed
  rw [gateWeightRank_justesen_eq, evalInput_canonicalInput]

-- Instantiate the joint logspace/isolation/magnitude certificate on `smallCircuit`.
example :
    ∃ (seed : Fin (codeLength 5 0) → Bool) (degree spaceFactor time k : ℕ)
      (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      smallCircuit.IsMinIsolating (smallCircuit.generatedGateWeight seed) ∧
      (∀ g : Fin 5,
        smallCircuit.generatedGateWeight seed g < 6 ^ (smallCircuit.andLevel g + codeLength 5 0) ∧
        smallCircuit.generatedGateWeight seed g < (2 * (5 + 1)) ^ degree) ∧
      tm.ComputesInTimeAndSpace (encInput (canonicalInput smallCircuit seed 4))
        (encNat (smallCircuit.generatedGateWeight seed 4))
        time (spaceFactor * 2 * (Nat.log2 5 + 1)) := by
  obtain ⟨_, spaceFactor, weightDegree, time, k, State, hfin, tm, hcert⟩ :=
    generatedGateWeight_certified
  obtain ⟨_, hisolate, heval⟩ := hcert 5
  obtain ⟨seed, hseed⟩ := hisolate smallCircuit smallCircuit_inNormalForm
  have hdepth (g : Fin 5) : smallCircuit.andLevel g ≤ 1 * (Nat.log2 5 + 1) := by
    fin_cases g <;> decide
  refine ⟨seed, weightDegree 1, spaceFactor, time (canonicalInput smallCircuit seed 4),
    k, State, hfin, tm, hseed, fun g => ⟨(heval 1 smallCircuit seed g (hdepth g)).1,
      (heval 1 smallCircuit seed g (hdepth g)).2.1⟩, ?_⟩
  exact (heval 1 smallCircuit seed 4 (hdepth 4)).2.2

-- Seed-independent polynomial ceiling bound checked at `c = 1`.
example :
    ∃ D : ℕ, generatedGateWeightBound 5 1 ≤ (2 * (5 + 1)) ^ D := by
  obtain ⟨D, hD⟩ := generatedGateWeightBound_le_poly 1
  exact ⟨D, hD 5 1 (by decide)⟩

/-! ## 3. Negative boundary witness: `x₁ ∨ x₂` without an AND first layer -/

private def x1OrX2 : LayeredSemiUnboundedCircuit (Fin 3) where
  layer
    | ⟨0, _⟩ | ⟨1, _⟩ => 0
    | ⟨2, _⟩ => 1
  kind
    | ⟨0, _⟩ => .leaf true
    | ⟨1, _⟩ => .leaf true
    | ⟨2, _⟩ => .or
  orChild
    | ⟨2, _⟩, c => c = 0 ∨ c = 1
    | _, _ => False
  layer_andUnary := by intro g c h; fin_cases g <;> cases h
  layer_andBinary := by intro g l r h; fin_cases g <;> cases h
  layer_orChild := by
    intro g c hg hc
    fin_cases g <;> cases hg
    rcases hc with rfl | rfl <;> decide

example (seed : Fin (codeLength 3 0) → Bool) :
    ¬x1OrX2.InNormalForm ∧
    evalInput (canonicalInput x1OrX2 seed 2) = 0 ∧
    evalInput (canonicalInput x1OrX2 seed 2) = x1OrX2.generatedGateWeight seed 2 := by
  refine ⟨fun h => (by
    obtain ⟨_, hinp⟩ := h.and_of_odd (g := 2) (by decide : Odd (x1OrX2.layer 2))
    cases hinp), ?_, evalInput_canonicalInput x1OrX2 seed 2⟩
  rw [evalInput_canonicalInput]
  rfl

end CslibFrontierTests.SemiUnboundedWeightGen
