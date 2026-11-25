/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.PowerTime
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Satisfiability Hypothesis

The hypothesis rules out a fixed power saving in the exponent of the time needed to decide
unrestricted CNF satisfiability, measured in occurring variables, clauses and literal occurrences.
For fixed width the literal-occurrence term is absorbed into the clause count.

## Main definitions

* `Cslib.Complexity.SH`: the Satisfiability Hypothesis on the native CNF encoding.

## Main results

* `Cslib.Complexity.SH_iff_KSAT`: the fixed-width formulation of the hypothesis.
* `Cslib.Complexity.SH.not_decidableInPowerExpTime_of_reduction`: exponent transfer under SH.
* `Cslib.Complexity.SH.not_decidableInPowerExpTime_of_linear_reduction`: transfer for
  polynomial-time reductions with linear target parameter.

## References

* [MIT Hardness Group, *ETH is Dead, Long Live SH*][MITHardnessGroup2026SH], v2, Lemma 2.1
  and Theorem 3.1.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The Satisfiability Hypothesis [MITHardnessGroup2026SH, §1 and footnote 2] in the native
deterministic multitape model. The exponent is measured in occurring variables, clauses and
literal occurrences. The input uses native binary labels, so the time bound also allows a
polynomial in actual encoded length. -/
@[expose] def SH : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 →
    ¬DecidableInPowerExpTime SAT encCNF (fun φ => φ.numVars + φ.length + φ.vars.length) p

private theorem width_toThreeSAT (φ : CNF ℕ) : ∀ c ∈ toThreeSAT φ, c.length ≤ 3 := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simpa using CNF.length_le_three_of_mem_to3CNF hd

private theorem toThreeSAT_size_le (φ : CNF ℕ) :
    (toThreeSAT φ).numVars + (toThreeSAT φ).length ≤
      4 * (φ.numVars + φ.length + φ.vars.length) := by
  have hclauses : (toThreeSAT φ).length ≤ φ.length + φ.vars.length := by
    rw [toThreeSAT, CNF.relabel, List.length_map, CNF.length_to3CNF, CNF.length_vars]
    induction φ with
    | nil => simp
    | cons c φ ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
  have hn := CNF.numVars_le_mul_length (width_toThreeSAT φ)
  omega

private theorem decidable_KSAT_of_SAT {k : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (h : DecidableInPowerExpTime SAT encCNF (fun φ => φ.numVars + φ.length + φ.vars.length) p) :
    DecidableInPowerExpTime (KSAT k) encCNF (fun φ => φ.numVars + φ.length) p := by
  let reduce (φ : CNF ℕ) : CNF ℕ :=
    if φ.all (fun c => decide (c.length ≤ k)) then φ else [[]]
  have hcomp : ComputableInPolyTime reduce encCNF encCNF :=
    ComputableInPolyTime.ite' (computableInPolyTime_all_length_le k)
      ComputableInPolyTime.id' (ComputableInPolyTime.const [[]])
  have hmem (φ : CNF ℕ) : φ ∈ KSAT k ↔ reduce φ ∈ SAT := by
    dsimp only [reduce]
    split_ifs with hw
    · exact ⟨fun hφ => hφ.2, fun hφ => ⟨by simpa using hw, hφ⟩⟩
    · exact ⟨fun hφ => absurd hφ.1 (by simpa using hw),
        fun ⟨_, hσ⟩ => (Bool.false_ne_true hσ).elim⟩
  have hsize (φ : CNF ℕ) :
      (((reduce φ).numVars + (reduce φ).length + (reduce φ).vars.length : ℕ) + 1 : ℝ) ≤
        (↑(k + 1 : ℕ) + 1 : ℝ) * ((φ.numVars + φ.length : ℕ) + 1 : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    suffices (reduce φ).numVars + (reduce φ).length + (reduce φ).vars.length + 1 ≤
        (k + 1 + 1) * (φ.numVars + φ.length + 1) by exact_mod_cast this
    dsimp only [reduce]
    split_ifs with hw
    · nlinarith [CNF.length_vars_le_mul_length (show ∀ c ∈ φ, c.length ≤ k by simpa using hw)]
    · change 1 + 1 ≤ _
      nlinarith
  simpa only [one_mul] using h.of_polyTime_reduction hcomp hmem (K := k + 1)
    hsize zero_le_one hp

/-- The size formulation of SH [MITHardnessGroup2026SH, Lemma 2.1, decision case].
For any fixed width `k ≥ 3`, SH holds exactly when `k`-SAT admits no fixed power saving in the
exponent measured in the number of occurring variables plus the number of clauses.
The counting formulation for #SH is tracked in #8457. -/
theorem SH_iff_KSAT {k : ℕ} (hk : 3 ≤ k) :
    SH ↔ ∀ p : ℝ, 0 < p → p < 1 →
      ¬DecidableInPowerExpTime (KSAT k) encCNF (fun φ => φ.numVars + φ.length) p := by
  constructor
  · intro h p hp hp1 hsolver
    apply h p hp hp1
    have hmem (φ : CNF ℕ) : φ ∈ SAT ↔ toThreeSAT φ ∈ KSAT k :=
      ⟨fun hφ => ⟨fun c hc => (width_toThreeSAT φ c hc).trans hk,
        ((mem_ThreeSAT_toThreeSAT_iff φ).mpr hφ).2⟩,
       fun hφ => (mem_ThreeSAT_toThreeSAT_iff φ).mp ⟨width_toThreeSAT φ, hφ.2⟩⟩
    have hsize (φ : CNF ℕ) :
        (((toThreeSAT φ).numVars + (toThreeSAT φ).length : ℕ) + 1 : ℝ) ≤
          (3 + 1 : ℝ) * ((φ.numVars + φ.length + φ.vars.length : ℕ) + 1 : ℝ) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
      have := toThreeSAT_size_le φ
      exact_mod_cast (by omega : (toThreeSAT φ).numVars + (toThreeSAT φ).length + 1 ≤
        (3 + 1) * (φ.numVars + φ.length + φ.vars.length + 1))
    simpa only [one_mul] using hsolver.of_polyTime_reduction computableInPolyTime_toThreeSAT
      hmem (K := 3) hsize zero_le_one hp.le
  · intro h p hp hp1 hsolver
    exact h p hp hp1 (decidable_KSAT_of_SAT hp.le hsolver)

/-- Exponent transfer [MITHardnessGroup2026SH, Theorem 3.1]. A many-one reduction from 3SAT
with running time exponential in the `q`th power of the formula size for `q < 1` and blowup
exponent `b > 0` rules out any target exponent power `0 < p < 1 / b` under SH. The blowup bound
allows `O(s ^ (b + η))` for every `η > 0`, and the target time includes a polynomial factor
in its encoded input length. -/
theorem SH.not_decidableInPowerExpTime_of_reduction (hSH : SH)
    {β : Type} {enc : β ↪ List Bool} {B : Set β} {μ : β → ℕ} {f : CNF ℕ → β} {q b p : ℝ}
    (hq : q < 1) (hb : 0 < b) (hp : 0 < p) (hbp : b * p < 1)
    (hf : ∃ C d : ℕ, ComputableInTimeO f encCNF enc
      fun φ => (2 : ℝ) ^ (C * ((φ.numVars + φ.length : ℕ) + 1 : ℝ) ^ q) *
        ((encCNF φ).length + 1) ^ d)
    (hmem : ∀ φ, φ ∈ ThreeSAT ↔ f φ ∈ B)
    (hsize : ∀ η : ℝ, 0 < η → ∃ K : ℕ, ∀ φ,
      (μ (f φ) + 1 : ℝ) ≤ (K + 1 : ℝ) * ((φ.numVars + φ.length : ℕ) + 1 : ℝ) ^ (b + η)) :
    ¬DecidableInPowerExpTime B enc μ p := by
  intro h
  let η := (1 - b * p) / (2 * p)
  have hη : 0 < η := div_pos (sub_pos.mpr hbp) (by positivity)
  have hmul : (b + η) * p = (b * p + 1) / 2 := by
    dsimp only [η]
    field_simp [ne_of_gt hp]
    ring
  obtain ⟨K, hK⟩ := hsize η hη
  apply (SH_iff_KSAT (k := 3) le_rfl).mp hSH (max q ((b + η) * p))
  · exact lt_max_of_lt_right (mul_pos (add_pos hb hη) hp)
  · rw [max_lt_iff, hmul]
    exact ⟨hq, by linarith⟩
  · exact h.of_reduction hf hmem hK hp.le

/-- Linear-size polynomial-time reductions from width-three satisfiability transfer SH with the
same power threshold. On formulas of greater width the reduction can use the image of a fixed
unsatisfiable width-three formula. -/
theorem SH.not_decidableInPowerExpTime_of_linear_reduction (hSH : SH)
    {β : Type} {enc : β ↪ List Bool} {B : Set β} {μ : β → ℕ} {f : CNF ℕ → β} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hf : ComputableInPolyTime f encCNF enc)
    (hmem : ∀ φ, (∀ c ∈ φ, c.length ≤ 3) → (φ ∈ SAT ↔ f φ ∈ B)) {K : ℕ}
    (hsize : ∀ φ, (∀ c ∈ φ, c.length ≤ 3) → μ (f φ) ≤ K * φ.length + K) :
    ¬DecidableInPowerExpTime B enc μ p := by
  let reduce (φ : CNF ℕ) : β :=
    if φ.all (fun c => decide (c.length ≤ 3)) then f φ else f [[]]
  have hcomp : ComputableInPolyTime reduce encCNF enc :=
    ComputableInPolyTime.ite' (computableInPolyTime_all_length_le 3)
      hf (ComputableInPolyTime.const _)
  obtain ⟨d, hd⟩ := ComputableInExpTime.of_computableInPolyTime (μ := fun _ => 0) hcomp
  refine hSH.not_decidableInPowerExpTime_of_reduction (q := 0) (b := 1)
    zero_lt_one zero_lt_one hp (by simpa using hp1) ⟨0, d, by simpa using hd⟩ ?_ ?_
  · intro φ
    dsimp only [reduce]
    split_ifs with hw
    · have hw' : ∀ c ∈ φ, c.length ≤ 3 := by simpa using hw
      exact ⟨fun h => (hmem φ hw').mp h.2, fun h => ⟨hw', (hmem φ hw').mpr h⟩⟩
    · have hnot : ¬ ∀ c ∈ φ, c.length ≤ 3 := by simpa using hw
      exact ⟨fun h => (hnot h.1).elim, fun h => by
        obtain ⟨σ, hσ⟩ := (hmem [[]] (by simp)).mpr h
        exact (Bool.false_ne_true hσ).elim⟩
  · intro η hη
    refine ⟨2 * K, fun φ => ?_⟩
    have hbound : μ (reduce φ) ≤ 2 * K * (φ.numVars + φ.length + 1) := by
      dsimp only [reduce]
      split_ifs with hw
      · have hw' : ∀ c ∈ φ, c.length ≤ 3 := by simpa using hw
        calc
          μ (f φ) ≤ K * φ.length + K := hsize φ hw'
          _ = K * (φ.length + 1) := by ring
          _ ≤ 2 * K * (φ.numVars + φ.length + 1) := Nat.mul_le_mul (by omega) (by omega)
      · have h := hsize [[]] (by simp)
        simp only [List.length_singleton, mul_one] at h
        calc
          μ (f [[]]) ≤ K + K := h
          _ = (2 * K) * 1 := by ring
          _ ≤ 2 * K * (φ.numVars + φ.length + 1) := Nat.mul_le_mul_left _ (by omega)
    have hl : (μ (reduce φ) + 1 : ℝ) ≤
        (↑(2 * K) + 1 : ℝ) * ((φ.numVars + φ.length : ℕ) + 1 : ℝ) := by
      have hbound' : (μ (reduce φ) : ℝ) ≤
          2 * K * ((φ.numVars : ℝ) + φ.length + 1) := by exact_mod_cast hbound
      push_cast
      nlinarith
    refine hl.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    conv_lhs => rw [← Real.rpow_one (((φ.numVars + φ.length : ℕ) : ℝ) + 1)]
    exact Real.rpow_le_rpow_of_exponent_le
      (le_add_of_nonneg_left (Nat.cast_nonneg _)) (by linarith)

end Cslib.Complexity
