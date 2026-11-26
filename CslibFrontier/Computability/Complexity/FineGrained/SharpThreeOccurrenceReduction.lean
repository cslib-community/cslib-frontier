/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.SharpSatisfiabilityHypothesis
public import CslibFrontier.Computability.Complexity.FineGrained.ThreeOccurrenceReduction

/-!
# Bounded-occurrence counting lower bounds under #SH

The parsimonious occurrence splitter has linear output size in both the number of occurring
variables and the number of clauses. Precomposing a counter with the splitter transfers the
fixed-width counting lower bound to formulas with at most three occurrences per variable.

## Main results

* `Cslib.Complexity.SharpSH.not_computableInPowerExpTime_sharpThreeSATThree_numVars`:
  the bound measured in occurring variables.
* `Cslib.Complexity.SharpSH.not_computableInPowerExpTime_sharpThreeSATThree_length`:
  the bound measured in clauses.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

private theorem SharpSH.not_computableInPowerExpTime_sharpThreeSATThree (h : SharpSH) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) {μ : CNF ℕ → ℕ} {K : ℕ}
    (hsize : ∀ φ, μ (toThreeSATThree φ) ≤ K * φ.length + K) :
    ¬ComputableInPowerExpTime SharpThreeSATThree encCNF encNat μ p := by
  intro hsolver
  apply (SharpSH_iff_SharpKSAT (k := 3) le_rfl).mp h p hp hp1
  have hcomp : SharpThreeSATThree ∘ toThreeSATThree = SharpKSAT 3 := by
    rw [SharpKSAT_three]
    exact funext sharpThreeSATThree_toThreeSATThree
  have hbound (φ : CNF ℕ) : (μ (toThreeSATThree φ) + 1 : ℝ) ≤
      (K + 1 : ℝ) * ((φ.numVars + φ.length : ℕ) + 1 : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    have hn : μ (toThreeSATThree φ) + 1 ≤ (K + 1) * (φ.numVars + φ.length + 1) := by
      calc
        _ ≤ K * (φ.length + 1) + 1 := by
          simpa only [Nat.mul_add, Nat.mul_one] using Nat.add_le_add_right (hsize φ) 1
        _ ≤ K * (φ.numVars + φ.length + 1) + (φ.numVars + φ.length + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left K (by omega)) (by omega)
        _ = _ := by rw [Nat.add_mul, Nat.one_mul]
    exact_mod_cast hn
  simpa only [hcomp, one_mul] using
    hsolver.comp_polyTime computableInPolyTime_toThreeSATThree (K := K) hbound zero_le_one hp.le

/-- Under #SH, exact model counting in width-three SAT with at most three literal occurrences
per variable admits no fixed power saving in the exponent measured in occurring variables. -/
theorem SharpSH.not_computableInPowerExpTime_sharpThreeSATThree_numVars (h : SharpSH) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    ¬ComputableInPowerExpTime SharpThreeSATThree encCNF encNat CNF.numVars p :=
  h.not_computableInPowerExpTime_sharpThreeSATThree hp hp1 (K := 3) fun φ =>
    (numVars_toThreeSATThree_le_mul_length φ).trans (Nat.le_add_right _ 3)

/-- Under #SH, exact model counting in width-three SAT with at most three literal occurrences
per variable admits no fixed power saving in the exponent measured in clauses. -/
theorem SharpSH.not_computableInPowerExpTime_sharpThreeSATThree_length (h : SharpSH) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    ¬ComputableInPowerExpTime SharpThreeSATThree encCNF encNat List.length p :=
  h.not_computableInPowerExpTime_sharpThreeSATThree hp hp1 (K := 4) fun φ => by
    have hlen := length_toThreeSATThree_le_mul_length φ
    omega

end Cslib.Complexity
