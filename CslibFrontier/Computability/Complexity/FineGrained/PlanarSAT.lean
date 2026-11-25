/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.SatisfiabilityHypothesis
public import CslibFrontier.Computability.Complexity.Problems.PlanarPositiveOneInThreeSAT
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# SH lower bounds for planar satisfiability

Quadratic planarization and exponent transfer [MITHardnessGroup2026SH, Theorem 3.1]
rule out fixed powers below one half in the number of occurring variables. The planar
languages use the native binary CNF encoding and require an orthogonal incidence drawing
to exist. The input consists of the formula.

## Main results

* `Cslib.Complexity.SH.not_decidableInPowerExpTime_planarThreeSATThree`: planar 3SAT
  with at most three literal occurrences per variable.
* `Cslib.Complexity.SH.not_decidableInPowerExpTime_planarPositiveOneInExactThreeSATThree`:
  planar positive exact-one SAT with exactly three distinct variables per clause and
  at most three occurrences per variable.
* `Cslib.Complexity.SH.not_decidableInPowerExpTime_planarPositiveOneInThreeSATThree`:
  the positive exact-one variant allowing shorter clauses.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

private theorem not_decidableInPowerExpTime_of_planarization (hSH : SH)
    {B : Set (CNF ℕ)} {f : CNF ℕ → CNF ℕ} {p : ℝ} (hp : 0 < p) (hp₁ : p < 1 / 2)
    (hf : ComputableInPolyTime f encCNF encCNF)
    (hmem : ∀ φ, φ ∈ ThreeSAT ↔ f φ ∈ B) {K : ℕ}
    (hsize : ∀ φ, (f φ).numVars ≤ K * (φ.length + φ.vars.length + 1) ^ 2) :
    ¬DecidableInPowerExpTime B encCNF CNF.numVars p := by
  intro solver
  let source (φ : CNF ℕ) :=
    if φ.all (fun c => decide (c.length ≤ 3)) then φ else [[]]
  have hsource : ComputableInPolyTime source encCNF encCNF :=
    ComputableInPolyTime.ite' (computableInPolyTime_all_length_le 3)
      ComputableInPolyTime.id' (ComputableInPolyTime.const _)
  apply (SH_iff_KSAT (k := 3) le_rfl).mp hSH (2 * p) (by positivity) (by linarith)
  rw [KSAT_three]
  refine solver.of_polyTime_reduction (b := 2) (hf.comp hsource) ?_
    (K := 16 * K) ?_ (by norm_num) hp.le
  · intro φ
    change φ ∈ ThreeSAT ↔ f (source φ) ∈ B
    rw [← hmem]
    dsimp only [source]
    split_ifs with hw
    · rfl
    · exact iff_of_false
        (fun h => hw (by simpa only [List.all_eq_true, decide_eq_true_eq] using h.1))
        (fun ⟨_, _, hσ⟩ => Bool.false_ne_true hσ)
  · intro φ
    have hsourceSize : (source φ).length + (source φ).vars.length + 1 ≤
        4 * (φ.numVars + φ.length + 1) := by
      dsimp only [source]
      split_ifs with hw
      · have hw' : ∀ c ∈ φ, c.length ≤ 3 := by
          simpa only [List.all_eq_true, decide_eq_true_eq] using hw
        have hvars := CNF.length_vars_le_mul_length hw'
        omega
      · change 2 ≤ 4 * (φ.numVars + φ.length + 1)
        omega
    have hbound : (f (source φ)).numVars ≤ 16 * K * (φ.numVars + φ.length + 1) ^ 2 := by
      calc
        _ ≤ K * ((source φ).length + (source φ).vars.length + 1) ^ 2 := hsize (source φ)
        _ ≤ K * (4 * (φ.numVars + φ.length + 1)) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsourceSize 2)
        _ = _ := by ring
    have hout : (f (source φ)).numVars + 1 ≤ (16 * K + 1) * (φ.numVars + φ.length + 1) ^ 2 := by
      have hone : 1 ≤ (φ.numVars + φ.length + 1) ^ 2 := Nat.one_le_pow 2 _ (by omega)
      calc
        _ ≤ 16 * K * (φ.numVars + φ.length + 1) ^ 2 + (φ.numVars + φ.length + 1) ^ 2 :=
          Nat.add_le_add hbound hone
        _ = _ := by ring
    rw [Real.rpow_two]
    exact_mod_cast hout

/-- Under SH, formula-only planar 3SAT with at most three occurrences per variable
admits no fixed exponent power below one half in the number of occurring variables. -/
theorem SH.not_decidableInPowerExpTime_planarThreeSATThree (h : SH) {p : ℝ}
    (hp : 0 < p) (hp₁ : p < 1 / 2) :
    ¬DecidableInPowerExpTime PlanarThreeSATThree encCNF CNF.numVars p :=
  not_decidableInPowerExpTime_of_planarization h hp hp₁ computableInPolyTime_toPlanarThreeSAT
    (fun φ => (mem_PlanarThreeSATThree_toPlanarThreeSAT_iff φ).symm)
    (K := 490000) fun φ =>
      (CNF.numVars_le_length_vars _).trans (toDrawnPlanarThreeSAT_costs φ).2.1

private theorem numVars_toPlanarPositiveOneInExactThreeSATThree_le (φ : CNF ℕ) :
    (toPlanarPositiveOneInExactThreeSATThree φ).numVars ≤
      124215000 * (φ.length + φ.vars.length + 1) ^ 2 :=
  (CNF.numVars_le_length_vars _).trans (size_toPlanarPositiveOneInExactThreeSATThree φ).2

/-- Under SH, formula-only planar positive exact-one SAT with three distinct variables per clause
and at most three occurrences per variable admits no fixed exponent power below one half in the
number of occurring variables. -/
theorem SH.not_decidableInPowerExpTime_planarPositiveOneInExactThreeSATThree (h : SH) {p : ℝ}
    (hp : 0 < p) (hp₁ : p < 1 / 2) :
    ¬DecidableInPowerExpTime PlanarPositiveOneInExactThreeSATThree encCNF CNF.numVars p :=
  not_decidableInPowerExpTime_of_planarization h hp hp₁
    computableInPolyTime_toPlanarPositiveOneInExactThreeSATThree
    (fun φ => (mem_PlanarPositiveOneInExactThreeSATThree_toPlanar_iff φ).symm)
    numVars_toPlanarPositiveOneInExactThreeSATThree_le

/-- Under SH, formula-only planar positive exact-one SAT of width and occurrence at most three
admits no fixed exponent power below one half in the number of occurring variables. -/
theorem SH.not_decidableInPowerExpTime_planarPositiveOneInThreeSATThree (h : SH) {p : ℝ}
    (hp : 0 < p) (hp₁ : p < 1 / 2) :
    ¬DecidableInPowerExpTime PlanarPositiveOneInThreeSATThree encCNF CNF.numVars p :=
  not_decidableInPowerExpTime_of_planarization h hp hp₁
    computableInPolyTime_toPlanarPositiveOneInExactThreeSATThree
    (fun φ => (mem_PlanarPositiveOneInThreeSATThree_toPlanar_iff φ).symm)
    numVars_toPlanarPositiveOneInExactThreeSATThree_le

end Cslib.Complexity
