/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.SatisfiabilityHypothesis
import CslibFrontier.Computability.Complexity.FineGrained.CountingPowerSearch

/-!
# Weak ETH and the Satisfiability Hypothesis

Quantitative sparsification makes the fixed-width SAT lower bound under SH equivalent to the
lower bound measured in occurring variables alone.

## Main definitions

* `Cslib.Complexity.WeakKETH`: the variable-count hypothesis for a fixed clause width.
* `Cslib.Complexity.WeakETH`: the hypothesis at width three.

## Main results

* `Cslib.Complexity.SH_iff_WeakKETH`: for every fixed width at least three, SH is equivalent to
  Weak k-ETH.
* `Cslib.Complexity.SH_iff_WeakETH`: SH is equivalent to Weak ETH.

## References

* [MIT Hardness Group, *ETH is Dead, Long Live SH*][MITHardnessGroup2026SH], v2, §1, §2.2
  and §2.3, Theorem 2.4 and Corollary 2.5.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL

/-- Weak k-ETH [MITHardnessGroup2026SH, v2, §2.2] in the native deterministic multitape model.
For formulas of clause width at most `k`, it rules out a fixed power saving in the exponent
measured in occurring variables. The time bound permits a polynomial in the binary CNF
encoding length, and the decision language rejects formulas above width `k`. -/
@[expose] def WeakKETH (k : ℕ) : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 → ¬DecidableInPowerExpTime (KSAT k) encCNF CNF.numVars p

/-- Weak ETH [MITHardnessGroup2026SH, v2, §1] is the variable-count hypothesis for 3SAT. -/
abbrev WeakETH : Prop := WeakKETH 3

/-- The fixed-width equivalence of [MITHardnessGroup2026SH, v2, §2.3, Corollary 2.5].
For any fixed clause width at least three, the size formulation of SH and the variable-count
formulation agree by quantitative sparsification and monotonicity in the size measure. -/
theorem SH_iff_WeakKETH {k : ℕ} (hk : 3 ≤ k) : SH ↔ WeakKETH k := by
  rw [SH_iff_KSAT hk]
  constructor
  · intro h p hp hp1 hsolver
    exact h p hp hp1 (hsolver.mono_measure (fun φ => Nat.le_add_right φ.numVars φ.length) hp.le)
  · intro h p hp hp1 hsolver
    obtain ⟨q, hq, hq1, hsolver'⟩ := hsolver.KSAT_numVars_of_size
      ((by decide : 2 ≤ 3).trans hk) hp hp1
    exact h q hq hq1 hsolver'

/-- The decision equivalence of [MITHardnessGroup2026SH, v2, §2.3, Theorem 2.4]. -/
theorem SH_iff_WeakETH : SH ↔ WeakETH :=
  SH_iff_WeakKETH le_rfl

end Cslib.Complexity
