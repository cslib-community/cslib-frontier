/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Code
public import CslibFrontier.Probability.Uniform
import CslibFrontier.Computability.Circuit.Quantum.GateMatrix
import CslibFrontier.Computability.Circuit.Quantum.Oracle.QueryDisturbance
import CslibFrontierTests.QuantumCircuitFixture
import CslibFrontierTests.QuantumOracleFixture

/-! Original one-query interference client. A coherent query determines the parity of two
oracle values; sampling one complete finite table makes that output a fair bit. -/

public section

namespace CslibFrontierTests.QuantumOracleInterference

open Cslib Cslib.Quantum CslibFrontierTests.QuantumCircuit CslibFrontierTests.QuantumOracle
open scoped ENNReal

private noncomputable def h₁ : PlacedGate 2 := ⟨1, Gate.hadamard, ⟨![1], by decide⟩⟩

private theorem hadamard_zero (q r : Bool) : hq₀.eval (ket ![q, r]) =
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket ![false, r] +
    ((if q then -1 else 1) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) • ket ![true, r] := by
  have h := GateCode.eval_toPlacedGate_hadamard_ket
    (g := hq₀) (t := 0) (by rfl) (by decide) ![q, r]
  have hu (c : Bool) : Function.update ![q, r] (0 : Fin 2) c = ![c, r] := by
    ext i
    fin_cases i <;> simp
  simpa [Fintype.sum_bool, hu, add_comm] using h

private theorem hadamard_one (q r : Bool) : h₁.eval (ket ![q, r]) =
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket ![q, false] +
    ((if r then -1 else 1) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) • ket ![q, true] := by
  have h := GateCode.eval_toPlacedGate_hadamard_ket
    (g := h₁) (t := 1) (by rfl) (by decide) ![q, r]
  have hu (c : Bool) : Function.update ![q, r] (1 : Fin 2) c = ![q, c] := by
    ext i
    fin_cases i <;> simp
  simpa [Fintype.sum_bool, hu, add_comm] using h

/-- Prepare a negative-phase response, query once, and interfere the address amplitudes. -/
@[expose] def parityProgram : OracleCircuit :=
  [.gate (false, true, 0, []), .gate (false, true, 1, []), .query,
    .gate (false, true, 1, []), .gate (false, true, 0, [])]

private theorem parityProgram_toCircuit (H : (Fin 1 → Bool) → Fin 1 → Bool) :
    OracleCircuit.toCircuit 2 H parityProgram =
      [hq₀, h₁, xorQuery H (Function.Embedding.refl _), h₁, hq₀] := by
  simp only [parityProgram, OracleCircuit.toCircuit, List.filterMap_cons,
    OracleGateCode.toPlacedGate?, PhaseGateCode.toPlacedGate?, GateCode.toPlacedGate?,
    show 0 < 2 by decide, show 1 < 2 by decide,
    show 1 + 1 ≤ 2 by decide, ↓reduceDIte, List.filterMap_nil]
  rfl

/-- The first output bit is the parity of the two oracle values. The oracle's first value
contributes only a global sign. -/
theorem run_parityProgram (H : (Fin 1 → Bool) → Fin 1 → Bool) :
    Circuit.run (OracleCircuit.toCircuit 2 H parityProgram) ![false, true] =
      (if H (fun _ => false) 0 then -1 else 1 : ℂ) •
        ket ![H (fun _ => false) 0 ^^ H (fun _ => true) 0, true] := by
  have hk : (xorQuery H (Function.Embedding.refl _)).eval
      (h₁.eval (hq₀.eval (ket ![false, true]))) =
      (if H (fun _ => false) 0 then -1 else 1 : ℂ) •
        h₁.eval (hq₀.eval (ket ![H (fun _ => false) 0 ^^ H (fun _ => true) 0, true])) := by
    simp only [hadamard_zero, hadamard_one, map_add, map_smul, xorQuery_oneBit_ket,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    cases H (fun _ => false) 0 <;> cases H (fun _ => true) 0 <;>
      simp only [Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, smul_add, smul_smul] <;> module
  rw [parityProgram_toCircuit]
  simp only [Circuit.run, Circuit.eval_cons, Circuit.eval_nil, hk, map_smul]
  rw [show h₁.eval (h₁.eval _) = _ from hadamard_twice _ _,
    show hq₀.eval (hq₀.eval _) = _ from hadamard_twice _ _]

example : (OracleCircuit.gateCount parityProgram, OracleCircuit.queryCount parityProgram) =
    (4, 1) := rfl

example : ∀ g ∈ parityProgram, g.WellFormed 1 1 2 := by decide

example (H : (Fin 1 → Bool) → Fin 1 → Bool) :
    (OracleCircuit.toCircuit 2 H parityProgram).length = 5 :=
  OracleCircuit.length_toCircuit H parityProgram (by decide)

/-- Measurement discards the global phase and returns the two-value parity with certainty. -/
theorem measure_parityProgram (H : (Fin 1 → Bool) → Fin 1 → Bool) :
    Circuit.measure (OracleCircuit.toCircuit 2 H parityProgram) ![false, true] =
      PMF.pure ![H (fun _ => false) 0 ^^ H (fun _ => true) 0, true] := by
  ext y
  rw [Circuit.measure_apply, run_parityProgram]
  cases H (fun _ => false) 0 <;> simp [PMF.pure_apply, apply_ite]

/-- Sample the finite function once, execute the coherent one-query circuit, and read bit zero. -/
noncomputable def parityExperiment : PMF Bool := do
  let H ← Probability.PMF.uniformOfFintype ((Fin 1 → Bool) → Fin 1 → Bool)
  let y ← Circuit.measure (OracleCircuit.toCircuit 2 H parityProgram) ![false, true]
  pure (y 0)

/-- The parity of the two independently sampled oracle values is a fair bit. -/
theorem parityExperiment_eq : parityExperiment = Probability.PMF.uniformOfFintype Bool := by
  let parity : ((Fin 1 → Bool) → Fin 1 → Bool) →+ Bool :=
    { toFun := fun H => H (fun _ => false) 0 + H (fun _ => true) 0
      map_zero' := rfl
      map_add' := fun _ _ => add_add_add_comm .. }
  have hsurj : Function.Surjective parity := by
    intro b
    refine ⟨fun q _ => if q 0 then b else false, ?_⟩
    change false + b = b
    exact zero_add b
  simp only [parityExperiment, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, measure_parityProgram, PMF.pure_bind,
    Matrix.cons_val_zero]
  exact Probability.PMF.uniformOfFintype_map_addHom parity hsurj

example : parityExperiment true = 1 / 2 := by
  rw [parityExperiment_eq]
  norm_num [Probability.PMF.uniformOfFintype_apply]

open Matrix in
-- On a basis input with distinct oracle answers the resulting states are orthogonal.
example :
    xorQueryDisturbance (fun (_ : Fin 1 → Bool) (_ : Fin 1) => true) (fun _ _ => false)
      (Function.Embedding.refl _) (pureState (ket (![false, false], ()))) = 2 := by
  let col (r : Bool) := onFirst (κ := Unit)
    (xorQuery (fun (_ : Fin 1 → Bool) (_ : Fin 1) => r) (Function.Embedding.refl _)).matrix
  have act (r : Bool) : (col r).val.toEuclideanLin (ket (![false, false], ())) =
      ket (![false, r], ()) := by
    change (toEuclideanCLM (𝕜 := ℂ) (col r).val) (ket _) = _
    rw [toEuclideanCLM_ket]
    ext y
    obtain ⟨y, ⟨⟩⟩ := y
    change (col r).val (y, ()) (![false, false], ()) = _
    simp only [col, onFirst_apply, ← PlacedGate.eval_ket_apply, xorQuery_oneBit_ket,
      Matrix.cons_val_zero, Matrix.cons_val_one, Bool.false_xor, ket_apply]
    simp
  change (densityConj ((col true).val - (col false).val)
    (pureState (ket (![false, false], ())))).trace.re = 2
  rw [densityConj_pureState, trace_pureState]
  change ‖((col true).val - (col false).val).toEuclideanLin (ket _)‖ ^ 2 = 2
  rw [map_sub, LinearMap.sub_apply, act, act, @norm_sub_sq ℂ, norm_ket, norm_ket]
  norm_num [ket, EuclideanSpace.inner_single_left]

end CslibFrontierTests.QuantumOracleInterference
