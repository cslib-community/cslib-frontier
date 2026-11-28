/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.DepthClasses
import CslibFrontier.Computability.Circuit.Boolean.IntThreshold
import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.SmallWeights
import CslibFrontier.Computability.Circuit.Boolean.FanInTwo
import CslibFrontier.Computability.Circuit.Boolean.Multiplicity
import CslibFrontier.Computability.Circuit.Simulation
import CslibFrontier.Computability.Circuit.SimulationDepth
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log
import Mathlib.Data.Nat.Size

/-!
# `TCⁱ ⊆ NCⁱ⁺¹`

For the nonuniform gate-counted classes, a polynomial-size majority circuit of depth
`O((log n)^i)` has an equivalent polynomial-size De Morgan circuit of depth `O((log n)^(i+1))`.
A majority gate may read a wire arbitrarily many times. `Unbounded.multCircuit` records those
multiplicities and bounds the number of distinct inputs by the input length plus the gate count.
Small integer weights then replace the multiplicities, so the word width in the integer
threshold simulation is polynomial in that number. AND, OR and NOT use their balanced formulas.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.exists_deMorgan_simulation_tc` bounds the size and depth
  of the simulation of each circuit, including circuits on empty input.
* `Cslib.Circuits.Boolean.TC_subset_NC_succ` and `Cslib.Circuits.Boolean.TC0_subset_NC_one`
  give the nonuniform class containments.
-/

public section

namespace Cslib.Circuits.Boolean

namespace Unbounded

open Finset

private def majorityCount (total count : ℕ) : Bool := decide ((total + 1) / 2 ≤ count)

/-- A strict integer gate realizing majority on the normalized multiplicities. -/
private noncomputable def smallMajority {N : ℕ} (mult : Fin N → ℕ) : IntThreshold.Op :=
  let h := SmallWeights.exists_small_threshold mult (((∑ i, mult i) + 1) / 2)
  ⟨N, h.choose, h.choose_spec.choose⟩

private theorem smallMajority_spec {N : ℕ} (mult : Fin N → ℕ) :
    (∀ i, |(smallMajority mult).weight i| ≤ SmallWeights.weightBound N) ∧
    |(smallMajority mult).bias| ≤ SmallWeights.weightBound N ∧
    ∀ x, ((∑ i, mult i) + 1) / 2 ≤ multWeight mult x ↔
      (smallMajority mult).bias < ∑ i, (smallMajority mult).weight i * ((x i).toNat : ℤ) :=
  (SmallWeights.exists_small_threshold mult (((∑ i, mult i) + 1) / 2)).choose_spec.choose_spec

/-- The factorial weight bound gives a quadratic word-width bound. -/
private theorem width_smallMajority_le {N K : ℕ} (mult : Fin N → ℕ) (hK : N ≤ K) :
    (smallMajority mult).width ≤ (K + 2) ^ 2 := by
  obtain ⟨hw, hb, _⟩ := smallMajority_spec mult
  have hB : SmallWeights.weightBound N ≤ SmallWeights.weightBound K :=
    Nat.mul_le_mul (by omega) (Nat.factorial_le (by omega))
  refine ((smallMajority mult).width_le (B := SmallWeights.weightBound K)
    (fun i => (hw i).trans (by exact_mod_cast hB)) (hb.trans (by exact_mod_cast hB))).trans ?_
  rw [Nat.size_le]
  -- `(2 K + 2) ((K + 1) (K + 1)! + 1) < 2 ^ ((K + 2) ^ 2)`
  have hfact : (K + 1).factorial ≤ (K + 1) ^ (K + 1) := Nat.factorial_le_pow _
  have hpow : K + 1 < 2 ^ (K + 1) := Nat.lt_two_pow_self
  have h1 : (K + 1) ^ (K + 1) ≤ 2 ^ ((K + 1) * (K + 1)) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hpow.le _
  have h2 : SmallWeights.weightBound K + 1 ≤ 2 ^ (K + 1 + (K + 1) * (K + 1)) := by
    have : (K + 1) * (K + 1).factorial < 2 ^ (K + 1) * 2 ^ ((K + 1) * (K + 1)) :=
      Nat.mul_lt_mul_of_lt_of_le hpow (hfact.trans h1) (by positivity)
    rw [pow_add]
    simp only [SmallWeights.weightBound]
    omega
  have h4 : 2 * K + 2 ≤ 2 ^ (K + 1) := by
    have : K < 2 ^ K := Nat.lt_two_pow_self
    rw [pow_succ]
    omega
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _
    (show 2 * N + 2 ≤ 2 * K + 2 by omega)) ?_
  calc (2 * K + 2) * (SmallWeights.weightBound K + 1)
      ≤ 2 ^ (K + 1) * 2 ^ (K + 1 + (K + 1) * (K + 1)) := Nat.mul_le_mul h4 h2
    _ = 2 ^ (K + 1 + (K + 1 + (K + 1) * (K + 1))) := by rw [← pow_add]
    _ < 2 ^ ((K + 2) ^ 2) := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)

/-- Simulate an ordinary gate with its balanced formula and a multiplicity gate with a
small-weight threshold circuit. -/
private noncomputable def multDeMorgan : (op : MultOp) →
    Circuit Boolean.signature op.arity 1
  | .ac op => op.deMorganFormula.toCircuit
  | .gate _ mult => (smallMajority mult).deMorganCircuit

private theorem computes_multDeMorgan (op : MultOp) :
    (multDeMorgan op).Computes Boolean.interpretation
      (single (multInterpretation majorityCount op)) := by
  cases op with
  | ac op => exact op.computes_deMorganFormula.toCircuit
  | gate N mult =>
    intro x
    funext o
    rw [Subsingleton.elim o 0]
    change (smallMajority mult).deMorganCircuit.eval Boolean.interpretation x 0 = _
    exact ((smallMajority mult).eval_deMorganCircuit x).trans
      (decide_eq_decide.mpr ((smallMajority_spec mult).2.2 x).symm)

private theorem bounds_multDeMorgan (op : MultOp) {K : ℕ} (h : op.arity ≤ K) :
    (multDeMorgan op).size ≤ 70 * (K + 1) * ((K + 2) ^ 2 + 2) ^ 2 ∧
    (multDeMorgan op).depth ≤
      9 + 2 * Nat.clog 2 ((K + 2) ^ 2 + 2) + 12 * Nat.clog 2 (K + 1) := by
  cases op with
  | ac op =>
    change op.arity ≤ K at h
    have hs := op.size_deMorganFormula_le
    have hd := op.depth_deMorganFormula_le
    have hprod : 70 * (K + 1) ≤ 70 * (K + 1) * ((K + 2) ^ 2 + 2) ^ 2 :=
      Nat.le_mul_of_pos_right _ (by positivity)
    have hlog := Nat.clog_mono_right 2 (show op.arity ≤ K + 1 by omega)
    constructor
    · change op.deMorganFormula.toCircuit.size ≤ _
      rw [Formula.size_toCircuit]
      omega
    · exact op.deMorganFormula.depth_toCircuit_le.trans (by omega)
  | gate N mult =>
    change N ≤ K at h
    have hw := width_smallMajority_le mult h
    have ha : (smallMajority mult).arity ≤ K := h
    constructor
    · refine (IntThreshold.Op.size_deMorganCircuit_le _).trans ?_
      gcongr
    · have := Nat.clog_mono_right 2 (Nat.add_le_add_right hw 2)
      have := Nat.clog_mono_right 2 (Nat.add_le_add_right ha 1)
      exact (IntThreshold.Op.depth_deMorganCircuit_le _).trans (by omega)

/-- **De Morgan circuits simulate `TC` circuits**: a `TC` circuit with `n` inputs, `s` gates and
depth `d` has an equivalent De Morgan circuit with at most
`s · 70 (K + 1) ((K + 2) ^ 2 + 2) ^ 2` gates and depth at most
`(9 + 2 ⌈log₂ ((K + 2) ^ 2 + 2)⌉ + 12 ⌈log₂ (K + 1)⌉) d`, where `K = n + s`. -/
theorem exists_deMorgan_simulation_tc {n m : ℕ} (C : Circuit extSignature n m) :
    ∃ D : Circuit Boolean.signature n m,
      D.eval Boolean.interpretation = C.eval (extInterpretation majority) ∧
      D.size ≤ C.size * (70 * (n + C.size + 1) * ((n + C.size + 2) ^ 2 + 2) ^ 2) ∧
      D.depth ≤ (9 + 2 * Nat.clog 2 ((n + C.size + 2) ^ 2 + 2) +
        12 * Nat.clog 2 (n + C.size + 1)) * C.depth := by
  let M := multCircuit C
  refine ⟨M.simulate multDeMorgan, ?_, ?_, ?_⟩
  · rw [Circuit.eval_simulate _ _ computes_multDeMorgan]
    exact eval_multCircuit (G := majorityCount) (fun _ _ => rfl) C
  · rw [Circuit.size_simulate, Program.cost_eq_sum]
    refine (Finset.sum_le_sum (g := fun _ : Fin M.size => 70 * (n + C.size + 1) *
      ((n + C.size + 2) ^ 2 + 2) ^ 2) fun k _ =>
        (bounds_multDeMorgan _ (arity_lines_multCircuit_le C k)).1).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rfl
  · exact (Circuit.depth_simulate_le _ _).trans
      ((Circuit.depthWith_le_mul_depth M fun k =>
        (bounds_multDeMorgan _ (arity_lines_multCircuit_le C k)).2).trans
        (Nat.mul_le_mul_left _ (depth_multCircuit_le C)))

end Unbounded

/-- For gate-counted nonuniform families, a polynomial-size majority circuit of depth
`O((log n)^i)` on each input length has a polynomial-size De Morgan simulation of depth
`O((log n)^(i+1))`, even when gates read the same wire arbitrarily many times. -/
theorem TC_subset_NC_succ (i : ℕ) : TC i ⊆ NC (i + 1) := by
  rintro L ⟨c, s, hs, hC⟩
  have hK : PolynomiallyBounded fun n => (n + s n + 2) ^ 2 + 2 + (n + s n + 1) := by fun_prop
  obtain ⟨e, he⟩ := PolynomiallyBounded.exists_clog_le_mul_log hK
  refine ⟨c * (14 * e + 9), fun n => s n * (70 * (n + s n + 1) * ((n + s n + 2) ^ 2 + 2) ^ 2),
    by fun_prop, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  obtain ⟨D, hDe, hDs, hDd⟩ := Unbounded.exists_deMorgan_simulation_tc C
  refine ⟨D, fun x => (congrFun hDe x).trans (hCc x), ?_, ?_⟩
  · have h1 : Nat.clog 2 ((n + C.size + 2) ^ 2 + 2) ≤ e * (Nat.log 2 n + 1) :=
      (Nat.clog_mono_right 2 (Nat.add_le_add_right (Nat.pow_le_pow_left (by omega) 2) 2)).trans
        ((Nat.clog_mono_right 2 (Nat.le_add_right _ _)).trans (he n))
    have h2 : Nat.clog 2 (n + C.size + 1) ≤ e * (Nat.log 2 n + 1) :=
      (Nat.clog_mono_right 2 (show n + C.size + 1 ≤ (n + s n + 2) ^ 2 + 2 + (n + s n + 1) by
        omega)).trans (he n)
    calc D.depth ≤ (9 + 2 * Nat.clog 2 ((n + C.size + 2) ^ 2 + 2) +
          12 * Nat.clog 2 (n + C.size + 1)) * C.depth := hDd
      _ ≤ ((14 * e + 9) * (Nat.log 2 n + 1)) * (c * (Nat.log 2 n + 1) ^ i) := by
          refine Nat.mul_le_mul ?_ hCd
          nlinarith
      _ = c * (14 * e + 9) * (Nat.log 2 n + 1) ^ (i + 1) := by ring
  · refine hDs.trans ?_
    beta_reduce
    gcongr

/-- **TC⁰ ⊆ NC¹**. -/
theorem TC0_subset_NC_one : TC0 ⊆ NC 1 :=
  TC_zero.symm.subset.trans (TC_subset_NC_succ 0)

end Cslib.Circuits.Boolean
