/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.SatisfiabilityHypothesis
public import CslibFrontier.Computability.Complexity.Problems.CSP.Basic
import CslibFrontier.Computability.Complexity.Problems.CSP.Hardness

/-!
# Satisfiability Hypothesis lower bound for hard Boolean constraint languages

This module proves the forward implication in
[MITHardnessGroup2026SH, v2, §4, Corollary 4.1] using the certified linear-size Schaefer reduction
from 3SAT. The exponent is measured in occurring variables, with polynomial overhead in the
native binary input length. The converse depends on the variable-count formulation of SH and
remains open in [#8457](https://github.com/cslib-community/cslib-frontier/issues/8457).

## Main results

* `Cslib.Complexity.SH.not_decidableInPowerExpTime_CSPSAT_numVars`: the variable-count bound
  for every fixed finite language without a common Schaefer polymorphism.

## References

* [MIT Hardness Group, *ETH is Dead, Long Live SH*][MITHardnessGroup2026SH], v2, §4,
  Corollary 4.1.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- This step proves the forward implication of
[MITHardnessGroup2026SH, v2, §4, Corollary 4.1]. Under SH, exact-arity satisfiability for a fixed
finite Boolean constraint language outside the six Schaefer cases has no deterministic multitape
algorithm with a fixed power saving in the exponent measured in occurring variables. The encoding
uses binary variable labels, and the running time allows polynomial overhead in the encoded input
length. The converse depends on the variable-count formulation of SH and remains open in
[#8457](https://github.com/cslib-community/cslib-frontier/issues/8457). -/
theorem SH.not_decidableInPowerExpTime_CSPSAT_numVars {Rel : Type} [Finite Rel]
    (hSH : SH) (encRel : Rel ↪ List Bool) (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (hHard : ¬ CSP.HasSchaeferPolymorphism arity sem) {p : ℝ} (hp : 0 < p) (hp₁ : p < 1) :
    ¬DecidableInPowerExpTime (CSPSAT arity sem) (encCSP encRel encNat) CSP.numVars p := by
  obtain ⟨f, C, hpoly, hmem, hsize⟩ :=
    CSPSAT.exists_linear_size_reduction_from_threeSAT encRel arity sem hHard
  refine hSH.not_decidableInPowerExpTime_of_linear_reduction hp hp₁ hpoly ?_ (K := C) ?_
  · intro φ hw
    exact (show φ ∈ SAT ↔ φ ∈ ThreeSAT from
      ⟨fun h => ⟨hw, h⟩, fun h => h.2⟩).trans (hmem φ)
  · intro φ _
    have := hsize φ
    omega

end Cslib.Complexity
