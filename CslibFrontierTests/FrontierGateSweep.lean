/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Frontier.Compiler.GateSweep
import CslibFrontier.Computability.Circuit.Frontier.Witness

/-! Checked clients and edge-case circuits for the hyperedge gate-sweep compiler. -/

open Cslib Cslib.Circuits Cslib.Circuits.Frontier Filter Set

namespace CslibFrontierTests.FrontierGateSweep

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
      {x | projCircuit.eval testInterp x 0 = true} :=
  Compiler.accepted_steinerNetwork_single

example (lay : Layout (Compiler.Node projCircuit)) :
    (Compiler.steinerGraph projCircuit lay).width lay = Compiler.signalWidth projCircuit lay :=
  Compiler.width_steinerGraph_eq

example : Compiler.multiFanoutSize projCircuit = 0 :=
  Compiler.multiFanoutSize_eq_zero_of_gateFanout_le_one (by decide)

/-- 2. Constant arity-`0` gate circuit (`innerSize = 0`). -/
private def constCircuit : Circuit testSig 1 1 where
  program := Program.empty.gate ⟨TestOp.constTrue, Fin.elim0⟩
  outputs _ := Wire.gate 0

example : constCircuit.innerSize = 0 := by decide

example (lay : Layout (Compiler.Node constCircuit)) :
    (Compiler.steinerNetwork constCircuit testInterp (fun _ => {true}) lay).accepted =
      {x | constCircuit.eval testInterp x 0 = true} :=
  Compiler.accepted_steinerNetwork_single

/-- 3. Duplicate-wire gate `g(x₀, x₀)` (`innerSize = 1`, `multiFanoutSize = 0`). -/
private def dupWireCircuit : Circuit testSig 1 1 where
  program := Program.empty.gate ⟨TestOp.andOp, fun _ => Wire.input 0⟩
  outputs _ := Wire.gate 0

example : dupWireCircuit.innerSize = 1 := by decide

example : Compiler.multiFanoutSize dupWireCircuit = 0 :=
  Compiler.multiFanoutSize_eq_zero_of_gateFanout_le_one (by decide)

example (lay : Layout (Compiler.Node dupWireCircuit)) :
    (Compiler.steinerNetwork dupWireCircuit testInterp (fun _ => {true}) lay).accepted =
      {x | dupWireCircuit.eval testInterp x 0 = true} :=
  Compiler.accepted_steinerNetwork_single

/-- 4. Formula `(x₀ ∧ x₁) ∨ x₂`: every inner gate has fan-out one (`multiFanoutSize = 0`), as does
`F.toCircuit` for every formula `F`. -/
private def formulaCircuit : Circuit testSig 3 1 where
  program :=
    (Program.empty.gate ⟨TestOp.andOp, ![Wire.input 0, Wire.input 1]⟩).gate
      ⟨TestOp.orOp, ![Wire.gate 0, Wire.input 2]⟩
  outputs _ := Wire.gate 1

example : formulaCircuit.innerSize = 2 := by decide

example : Compiler.multiFanoutSize formulaCircuit = 0 :=
  Compiler.multiFanoutSize_eq_zero_of_gateFanout_le_one (by decide)

example (lay : Layout (Compiler.Node formulaCircuit)) :
    (Compiler.steinerNetwork formulaCircuit testInterp (fun _ => {true}) lay).accepted =
      {x | formulaCircuit.eval testInterp x 0 = true} :=
  Compiler.accepted_steinerNetwork_single

example (n : ℕ) (F : Formula testSig n) : Compiler.multiFanoutSize F.toCircuit = 0 :=
  Compiler.multiFanoutSize_toCircuit F

/-- 5. Shared-gate circuit `u = x₀ ∧ x₁; (u ∨ x₂) ∧ (u ∨ x₀)` where `u` feeds two gates. -/
private def sharedCircuit : Circuit testSig 3 1 where
  program :=
    (((Program.empty.gate ⟨TestOp.andOp, ![Wire.input 0, Wire.input 1]⟩).gate
      ⟨TestOp.orOp, ![Wire.gate 0, Wire.input 2]⟩).gate
      ⟨TestOp.orOp, ![Wire.gate 0, Wire.input 0]⟩).gate
      ⟨TestOp.andOp, ![Wire.gate 1, Wire.gate 2]⟩
  outputs _ := Wire.gate 3

example : sharedCircuit.innerSize = 4 := by decide

example : Compiler.multiFanoutSize sharedCircuit ≤ sharedCircuit.innerSize :=
  Compiler.multiFanoutSize_le_innerSize sharedCircuit

example : Compiler.multiFanoutSize sharedCircuit = 1 := by
  refine le_antisymm ((Compiler.multiFanoutSize_le_card_gateFanout sharedCircuit).trans (by decide))
    ?_
  let idx₀ : Fin sharedCircuit.size := ⟨0, by decide⟩
  let idx₁ : Fin sharedCircuit.size := ⟨1, by decide⟩
  let idx₂ : Fin sharedCircuit.size := ⟨2, by decide⟩
  let idx₃ : Fin sharedCircuit.size := ⟨3, by decide⟩
  let a₃₀ : Fin (testSig.Arity (sharedCircuit.program.lines idx₃).op) := ⟨0, by decide⟩
  let a₃₁ : Fin (testSig.Arity (sharedCircuit.program.lines idx₃).op) := ⟨1, by decide⟩
  let a₁₀ : Fin (testSig.Arity (sharedCircuit.program.lines idx₁).op) := ⟨0, by decide⟩
  let a₂₀ : Fin (testSig.Arity (sharedCircuit.program.lines idx₂).op) := ⟨0, by decide⟩
  have hw30 : (sharedCircuit.program.lines idx₃).wires a₃₀ = .gate idx₁ := by decide
  have hw31 : (sharedCircuit.program.lines idx₃).wires a₃₁ = .gate idx₂ := by decide
  have hw10 : (sharedCircuit.program.lines idx₁).wires a₁₀ = .gate idx₀ := by decide
  have hw20 : (sharedCircuit.program.lines idx₂).wires a₂₀ = .gate idx₀ := by decide
  have h3 : Compiler.Reach sharedCircuit (.gate idx₃) := Compiler.Reach.output 0
  have h1 : Compiler.Reach sharedCircuit (.gate idx₁) := hw30 ▸ Compiler.Reach.arg a₃₀ h3
  have h2 : Compiler.Reach sharedCircuit (.gate idx₂) := hw31 ▸ Compiler.Reach.arg a₃₁ h3
  have h0 : Compiler.Reach sharedCircuit (.gate idx₀) := hw10 ▸ Compiler.Reach.arg a₁₀ h1
  let g₀ : Compiler.InnerGate sharedCircuit := ⟨idx₀, h0, by decide⟩
  have hmem : g₀ ∈ Compiler.multiFanoutGates sharedCircuit := by
    let w₀ := (Compiler.ActiveSignal.gate g₀).toSignal
    let t₁ : {t : Compiler.Consumer sharedCircuit // Compiler.consumed t = w₀} :=
      ⟨.inl ⟨⟨idx₁, a₁₀⟩, h1⟩, Subtype.ext hw10⟩
    let t₂ : {t : Compiler.Consumer sharedCircuit // Compiler.consumed t = w₀} :=
      ⟨.inl ⟨⟨idx₂, a₂₀⟩, h2⟩, Subtype.ext hw20⟩
    have hne : t₁ ≠ t₂ := fun h => by
      have hslot := congrArg Subtype.val (Sum.inl.inj (congrArg Subtype.val h))
      have hval : idx₁.val = idx₂.val := congrArg (fun p => p.1.val) hslot
      exact absurd hval (by decide)
    have hcard : Nat.card Bool ≤ Compiler.fanout sharedCircuit w₀ :=
      Nat.card_le_card_of_injective (fun b : Bool => if b then t₁ else t₂) fun b₁ b₂ hb => by
        cases b₁ <;> cases b₂ <;> first | rfl | exact absurd hb.symm hne | exact absurd hb hne
    change 2 ≤ Compiler.fanout sharedCircuit w₀
    simpa [Nat.card_eq_fintype_card] using hcard
  exact (ncard_pos (toFinite _)).mpr ⟨g₀, hmem⟩

example (lay : Layout (Compiler.Node sharedCircuit)) :
    (Compiler.steinerNetwork sharedCircuit testInterp (fun _ => {true}) lay).accepted =
      {x | sharedCircuit.eval testInterp x 0 = true} :=
  Compiler.accepted_steinerNetwork_single

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

/-- Family 5 (`BitString.quadForm (symmHardForm n)` correlation decay). -/
example : ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
    ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), c.FanInAtMost 40 →
        (c.innerSize : ℝ) ≤ (quadFormGateSweepCoefficient 40 4 - 1 / 1000) * n →
        |correlation {x | BitString.quadForm (symmHardForm n) x}
          {x | c.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  exists_eventually_abs_correlation_symmHardForm_le_gateSweep.{0}
    (r := 40) (k₀ := 4) (by decide) (by decide) (by norm_num)

example (r : ℕ) (hr : 2 ≤ r) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
        (c : Circuit σ n 1), c.FanInAtMost r →
          ((r - 1 : ℝ) * c.innerSize) ≤
            (Real.logb 2 r - Real.logb 2 (Real.logb 2 r) - 2 - 1 / 100) * n →
          |correlation {x | BitString.quadForm (symmHardForm n) x}
            {x | c.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  exists_eventually_abs_correlation_symmHardForm_le_log.{0} hr (by norm_num)

end CslibFrontierTests.FrontierGateSweep
