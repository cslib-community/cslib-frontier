/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Frontier.Compiler.GateSweep
import CslibFrontier.Computability.Circuit.Frontier.Witness
import Lean.Util.CollectAxioms

/-! Checked clients, edge-case circuits, and axiom audit for the hyperedge gate-sweep compiler. -/

open Cslib Cslib.Circuits Cslib.Circuits.Frontier Matrix Filter Set

namespace CslibFrontierTests.FrontierGateSweep

/-! ### Module-wide axiom audit for all `GateSweep` modules -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let prefixName : Name := `CslibFrontier.Computability.Circuit.Frontier.Compiler.GateSweep
  let mut moduleCount : Nat := 0
  let mut declarationCount : Nat := 0
  for moduleName in env.header.moduleNames, data in env.header.moduleData do
    if moduleName == prefixName || prefixName.isPrefixOf moduleName then
      moduleCount := moduleCount + 1
      for name in data.constNames do
        declarationCount := declarationCount + 1
        let axioms ← collectAxioms name
        let disallowed := axioms.filter fun ax => !allowed.contains ax
        unless disallowed.isEmpty do
          throwError "GateSweep axiom audit: {name} from {moduleName} depends on {disallowed}"
  unless moduleCount == 4 && declarationCount > 0 do
    throwError "GateSweep axiom audit: expected 4 modules, found {moduleCount}"

/-! ### Edge-case circuits on `steinerNetwork`, `signalWidth`, and `multiFanoutSize` -/

/-- Minimal test signature with one nullary constant and two binary Boolean operations. -/
private inductive TestOp : Type
  | constTrue
  | andOp
  | orOp
  deriving DecidableEq

private abbrev testSig : Signature where
  Op := TestOp
  Arity
    | .constTrue => 0
    | .andOp => 2
    | .orOp => 2

private def testInterp : Interpretation testSig Bool
  | .constTrue, _ => true
  | .andOp, w => w 0 && w 1
  | .orOp, w => w 0 || w 1

/-- 1. Projection circuit (`0` gates, `c.outputs 0 = .input 0`). -/
private def projCircuit : Circuit testSig 2 1 :=
  Circuit.wiring testSig fun _ => 0

example (lay : Layout (Compiler.Node projCircuit)) :
    (Compiler.steinerNetwork projCircuit testInterp (fun _ => {true}) lay).accepted =
      {x | projCircuit.eval testInterp x 0 = true} := by
  rw [Compiler.accepted_steinerNetwork]
  ext x
  exact ⟨fun h => h 0, fun h o => Subsingleton.elim o 0 ▸ h⟩

example (lay : Layout (Compiler.Node projCircuit)) :
    (Compiler.steinerGraph projCircuit lay).width lay = Compiler.signalWidth projCircuit lay :=
  Compiler.width_steinerGraph_eq

example : Compiler.multiFanoutSize projCircuit = 0 := by
  rw [Compiler.multiFanoutSize, ncard_eq_zero]
  ext g
  exact False.elim (Fin.elim0 g.1)

/-- 2. Constant arity-`0` gate circuit (`innerSize = 0`). -/
private def constCircuit : Circuit testSig 1 1 where
  program := Program.empty.gate ⟨TestOp.constTrue, Fin.elim0⟩
  outputs _ := Wire.gate 0

example : constCircuit.innerSize = 0 := by decide

example (lay : Layout (Compiler.Node constCircuit)) :
    (Compiler.steinerNetwork constCircuit testInterp (fun _ => {true}) lay).accepted =
      {x | constCircuit.eval testInterp x 0 = true} := by
  rw [Compiler.accepted_steinerNetwork]
  ext x
  exact ⟨fun h => h 0, fun h o => Subsingleton.elim o 0 ▸ h⟩

/-- 3. Duplicate-wire gate `g(x₀, x₀)` (`innerSize = 1`, `multiFanoutSize = 0`). -/
private def dupWireCircuit : Circuit testSig 1 1 where
  program := Program.empty.gate ⟨TestOp.andOp, fun _ => Wire.input 0⟩
  outputs _ := Wire.gate 0

example : dupWireCircuit.innerSize = 1 := by decide

example (lay : Layout (Compiler.Node dupWireCircuit)) :
    (Compiler.steinerNetwork dupWireCircuit testInterp (fun _ => {true}) lay).accepted =
      {x | dupWireCircuit.eval testInterp x 0 = true} := by
  rw [Compiler.accepted_steinerNetwork]
  ext x
  exact ⟨fun h => h 0, fun h o => Subsingleton.elim o 0 ▸ h⟩

/-- 4. Formula `(x₀ ∧ x₁) ∨ x₂`: every inner gate has fan-out one (`multiFanoutSize = 0`). -/
private def formulaCircuit : Circuit testSig 3 1 where
  program :=
    (Program.empty.gate ⟨TestOp.andOp, ![Wire.input 0, Wire.input 1]⟩).gate
      ⟨TestOp.orOp, ![Wire.gate 0, Wire.input 2]⟩
  outputs _ := Wire.gate 1

example : formulaCircuit.innerSize = 2 := by decide

/-- 5. Shared-gate circuit `u = x₀ ∧ x₁; (u ∨ x₂) ∧ (u ∨ x₀)` where `u` feeds two gates. -/
private def sharedCircuit : Circuit testSig 3 1 where
  program :=
    (((Program.empty.gate ⟨TestOp.andOp, ![Wire.input 0, Wire.input 1]⟩).gate
      ⟨TestOp.orOp, ![Wire.gate 0, Wire.input 2]⟩).gate
      ⟨TestOp.orOp, ![Wire.gate 0, Wire.input 0]⟩).gate
      ⟨TestOp.andOp, ![Wire.gate 1, Wire.gate 2]⟩
  outputs _ := Wire.gate 3

example : sharedCircuit.innerSize = 4 := by decide

example (lay : Layout (Compiler.Node sharedCircuit)) :
    (Compiler.steinerNetwork sharedCircuit testInterp (fun _ => {true}) lay).accepted =
      {x | sharedCircuit.eval testInterp x 0 = true} := by
  rw [Compiler.accepted_steinerNetwork]
  ext x
  exact ⟨fun h => h 0, fun h o => Subsingleton.elim o 0 ▸ h⟩

/-! ### Exact rational threshold evaluations and comparisons -/

example : 7 * gateSweepCoefficient 8 2 = 28 / 9 := by
  unfold gateSweepCoefficient
  norm_num

example : (29586 / 10000 : ℝ) < 7 * gateSweepCoefficient 8 2 := by
  unfold gateSweepCoefficient
  norm_num

example : 39 * gateSweepCoefficient 40 4 = 78 / 17 := by
  unfold gateSweepCoefficient
  norm_num

/-- At `r = 40` (`k₀ = 4`), `(r - 1) * gateSweepCoefficient 40 4 = 78 / 17` surpasses `4.57597`. -/
example : (457597 / 100000 : ℝ) < 39 * gateSweepCoefficient 40 4 := by
  unfold gateSweepCoefficient
  norm_num

example : 63 * gateSweepCoefficient 64 4 = 126 / 25 := by
  unfold gateSweepCoefficient
  norm_num

example : (5 : ℝ) < 63 * gateSweepCoefficient 64 4 := by
  unfold gateSweepCoefficient
  norm_num

example : 39 * quadFormGateSweepCoefficient 40 4 = 65 / 17 := by
  unfold quadFormGateSweepCoefficient
  norm_num

/-- At `r = 40` (`k₀ = 4`), `(r - 1) * quadFormGateSweepCoefficient 40 4 = 65 / 17 > 2.78798`. -/
example : (278798 / 100000 : ℝ) < 39 * quadFormGateSweepCoefficient 40 4 := by
  unfold quadFormGateSweepCoefficient
  norm_num

/-! ### Non-vacuous instantiations of all five theorem families -/

/-- Family 1 (`Ω(log r)` worst-case + `78 / 17` at `r = 40`) instantiated on `Bool` via
`exists_rectangleFree_family`. -/
example : ∃ S : ∀ n, Set (Fin n → Bool),
    (∀ r : ℕ, 2 ≤ r → ∀ᶠ n in atTop,
      ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
        (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
          (Real.logb 2 r - Real.logb 2 (Real.logb 2 r) - 1 - 1 / 100) * n <
            (r - 1) * c.innerSize) ∧
    (∀ᶠ n in atTop,
      ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
        (c : Circuit σ n 1), c.FanInAtMost 40 → c.Decides I Acc (S n) →
          (78 / 17 - 1 / 100 : ℝ) * n < 39 * c.innerSize) := by
  obtain ⟨S, hfree, hlog, hdef, _⟩ := exists_rectangleFree_family
  have hSK : DenseRectangleFree S (fun n => n + 2) := ⟨hfree, hlog, hdef⟩
  exact ⟨S,
    fun r hr => eventually_log_sub_log_log_lt_mul_innerSize.{0, 0} hr hSK (by norm_num),
    eventually_seventy_eight_div_seventeen_lt_thirty_nine_mul_innerSize.{0, 0} hSK (by norm_num)⟩

/-- Family 2 (`Ω(log r)` average-case) instantiated on `Bool` via `exists_rectangleBias_family`. -/
example (r : ℕ) (hr : 2 ≤ r) :
    ∃ (S : ∀ n, Set (Fin n → Bool)) (γ : ℝ), 0 < γ ∧
      ∀ᶠ n in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
        (c : Circuit σ n 1), c.FanInAtMost r →
          ((r - 1 : ℝ) * c.innerSize) ≤
            (Real.logb 2 r - Real.logb 2 (Real.logb 2 r) - 1 - 1 / 100) * n →
          agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤
            1 / 2 + 1 / ((n : ℝ) + 1) + Real.exp (-(γ * n)) := by
  obtain ⟨S, hbias, hlog, _⟩ := exists_rectangleBias_family
  obtain ⟨γ, hγ, H⟩ := exists_eventually_agreement_le_log.{0, 0} hr (ε := 1 / 100) (by norm_num)
  exact ⟨S, γ, hγ, H Bool S (fun n => (n + 1) ^ 3) (fun n => 1 / ((n : ℝ) + 1)) hbias hlog⟩

/-- Family 3 (low-reuse `s + 12 g_{≥2} > 6 n` worst-case and average-case) on `Bool`. -/
example : ∃ S : ∀ n, Set (Fin n → Bool), ∀ᶠ n in atTop,
    ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (6 - 1 / 100 : ℝ) * n < c.innerSize + 12 * Compiler.multiFanoutSize c := by
  obtain ⟨S, hfree, hlog, hdef, _⟩ := exists_rectangleFree_family
  have hSK : DenseRectangleFree S (fun n => n + 2) := ⟨hfree, hlog, hdef⟩
  exact ⟨S, eventually_six_sub_lt_innerSize_add_twelve_mul_multiFanoutSize.{0, 0} hSK
    (by norm_num)⟩

example : ∃ (S : ∀ n, Set (Fin n → Bool)) (γ : ℝ), 0 < γ ∧
    ∀ᶠ n in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), c.FanInAtMost 2 →
        (c.innerSize : ℝ) + 12 * Compiler.multiFanoutSize c ≤ (6 - 1 / 100 : ℝ) * n →
        agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤
          1 / 2 + 1 / ((n : ℝ) + 1) + Real.exp (-(γ * n)) := by
  obtain ⟨S, hbias, hlog, _⟩ := exists_rectangleBias_family
  obtain ⟨γ, hγ, H⟩ := exists_eventually_agreement_le_multiFanoutSize.{0, 0}
    (k₀ := 4) (by decide) (ε := 1 / 100) (by norm_num)
  refine ⟨S, γ, hγ, ?_⟩
  filter_upwards [H Bool S (fun n => (n + 1) ^ 3) (fun n => 1 / ((n : ℝ) + 1)) hbias hlog] with
    n hn σ I Acc c hfan hsize
  refine hn σ I Acc c hfan ?_
  have h6 : (((4 : ℕ) + 2 : ℝ) - 1 / 100) = 6 - 1 / 100 := by norm_num
  have h12 : ((2 : ℝ) ^ (4 : ℕ) - (4 : ℕ)) = 12 := by norm_num
  rw [h6, h12]
  exact hsize

/-- Family 4 (nondeterministic `4 / (r + 1)` uniformly in witness count `k : ℕ`). -/
example (r : ℕ) (hr : 2 ≤ r) :
    ∃ S : ∀ n, Set (Fin n → Bool), ∀ᶠ n in atTop,
      ∀ (k : ℕ) (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
        (c : Circuit σ (n + k) 1), c.FanInAtMost r → c.NondeterministicDecides I Acc (S n) →
          (4 / (r + 1 : ℝ) - 1 / 100) * n < c.innerSize := by
  obtain ⟨S, hfree, hlog, hdef, _⟩ := exists_rectangleFree_family
  have hSK : DenseRectangleFree S (fun n => n + 2) := ⟨hfree, hlog, hdef⟩
  exact ⟨S, eventually_four_div_lt_innerSize_of_nondeterministicDecides.{0, 0} hr hSK
    (by norm_num)⟩

/-- Family 5 (`BitString.quadForm (Matrix.symmHardForm n)` correlation decay). -/
example : ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
    ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), c.FanInAtMost 40 →
        (c.innerSize : ℝ) ≤ (quadFormGateSweepCoefficient 40 4 - 1 / 1000) * n →
        |correlation {x | BitString.quadForm (Matrix.symmHardForm n) x}
          {x | c.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  exists_eventually_abs_correlation_symmHardForm_le_gateSweep.{0}
    (r := 40) (k₀ := 4) (by decide) (by decide) (by norm_num)

example (r : ℕ) (hr : 2 ≤ r) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
        (c : Circuit σ n 1), c.FanInAtMost r →
          ((r - 1 : ℝ) * c.innerSize) ≤
            (Real.logb 2 r - Real.logb 2 (Real.logb 2 r) - 2 - 1 / 100) * n →
          |correlation {x | BitString.quadForm (Matrix.symmHardForm n) x}
            {x | c.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  exists_eventually_abs_correlation_symmHardForm_le_log.{0} hr (by norm_num)

end CslibFrontierTests.FrontierGateSweep
