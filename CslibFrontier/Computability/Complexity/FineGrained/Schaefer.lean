/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.SatisfiabilityHypothesis
public import CslibFrontier.Computability.Complexity.Problems.CSP.Basic
import CslibFrontier.Computability.Complexity.FineGrained.WeakExponentialTimeHypothesis
import CslibFrontier.Computability.Complexity.Problems.CSP.Hardness

/-!
# Satisfiability Hypothesis lower bound for hard Boolean constraint languages

For a fixed finite Boolean constraint language on the hard side of Schaefer's dichotomy, SH is
equivalent to a lower bound measured in occurring variables. The forward direction uses the
linear-size reduction from 3SAT. The converse compiles constraints into bounded-width CNF
without introducing variables and applies the fixed-width Weak ETH equivalence.

## Main results

* `Cslib.Complexity.SH_iff_CSPSAT_numVars`: the variable-count formulation of SH for hard
  Boolean constraint languages.

## References

* [MIT Hardness Group, *ETH is Dead, Long Live SH*][MITHardnessGroup2026SH], v2, §4,
  Corollary 4.1.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Schaefer SAT lower bounds [MITHardnessGroup2026SH, v2, §4, Corollary 4.1].
For a fixed finite Boolean constraint language outside the six Schaefer cases, SH is
equivalent to ruling out every fixed power saving in the exponent measured in occurring
variables for exact-arity satisfiability. The deterministic multitape model uses binary
variable labels, allows polynomial overhead in the encoded input length, and rejects malformed
constraint scopes. -/
theorem SH_iff_CSPSAT_numVars {Rel : Type} [Finite Rel]
    (encRel : Rel ↪ List Bool) (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (hHard : ¬ CSP.HasSchaeferPolymorphism arity sem) :
    SH ↔ ∀ p : ℝ, 0 < p → p < 1 →
      ¬DecidableInPowerExpTime (CSPSAT arity sem) (encCSP encRel encNat) CSP.numVars p := by
  constructor
  · intro hSH p hp hp₁
    obtain ⟨f, C, hpoly, hmem, hsize⟩ :=
      CSPSAT.exists_linear_size_reduction_from_threeSAT encRel arity sem hHard
    refine hSH.not_decidableInPowerExpTime_of_linear_reduction hp hp₁ hpoly ?_ (K := C) ?_
    · intro φ hw
      exact (show φ ∈ SAT ↔ φ ∈ ThreeSAT from
        ⟨fun h => ⟨hw, h⟩, fun h => h.2⟩).trans (hmem φ)
    · intro φ _
      have := hsize φ
      omega
  · intro h
    obtain ⟨f, k, hpoly, hmem, hvars, hwidth⟩ :=
      CSPSAT.exists_boundedWidth_reduction_toSAT encRel arity sem
    apply (SH_iff_WeakKETH (le_max_left 3 k)).mpr
    intro p hp hp₁ hsolver
    apply h p hp hp₁
    have hmem' (F : CSP Rel ℕ) : F ∈ CSPSAT arity sem ↔ f F ∈ KSAT (max 3 k) :=
      ⟨fun hF => ⟨fun c hc => (hwidth F c hc).trans (le_max_right 3 k), (hmem F).mp hF⟩,
        fun hF => (hmem F).mpr hF.2⟩
    have hsize (F : CSP Rel ℕ) :
        ((f F).numVars + 1 : ℝ) ≤ (↑(0 : ℕ) + 1 : ℝ) * (F.numVars + 1 : ℝ) ^ (1 : ℝ) := by
      rw [Nat.cast_zero, zero_add, one_mul, Real.rpow_one]
      exact_mod_cast Nat.add_le_add_right (hvars F) 1
    simpa only [one_mul] using hsolver.of_polyTime_reduction hpoly hmem' (K := 0) hsize
      zero_le_one hp.le

end Cslib.Complexity
