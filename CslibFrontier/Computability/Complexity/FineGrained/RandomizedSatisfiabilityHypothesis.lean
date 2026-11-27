/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.RandomizedPowerTime
public import CslibFrontier.Computability.Complexity.FineGrained.SatisfiabilityHypothesis
import CslibFrontier.Computability.Complexity.FineGrained.Bounds

/-!
# The randomized Satisfiability Hypothesis

The bounded-error decision hypothesis of [MITHardnessGroup2026SH, v2, §7] implies its deterministic
counterpart. The fixed-width size formulation and exponent transfer preserve the seed error
bound through a single deterministic reduction. The variable-count equivalences, which need
amplification across sparsification branches, remain open in #8457.

## Main definitions

* `Cslib.Complexity.rSH`: the bounded-error decision Satisfiability Hypothesis.

## Main results

* `Cslib.Complexity.rSH.sh`: randomized SH implies deterministic SH.
* `Cslib.Complexity.rSH_iff_KSAT`: the fixed-width formula-size formulation.
* `Cslib.Complexity.rSH.not_solvesWithErrorInPowerExpTime_of_reduction`: exponent transfer
  to bounded-error promise solvers under randomized SH.

## References

* [MIT Hardness Group, *ETH is Dead, Long Live SH*][MITHardnessGroup2026SH], v2, §7.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL PromiseProblem

/-- The randomized Satisfiability Hypothesis [MITHardnessGroup2026SH, v2, §7, p. 10].
It rules out any fixed power saving for unrestricted CNF satisfiability with two-sided error
at most `1 / 3`. The bound holds for every seed and measures occurring variables, clauses
and literal occurrences, with polynomial overhead in the native binary input length. -/
@[expose] def rSH : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 →
    ¬SolvesWithErrorInPowerExpTime (ofSet SAT) encCNF ErrorModel.bounded
      (fun φ => φ.numVars + φ.length + φ.vars.length) p

/-- The randomized Satisfiability Hypothesis implies SH. -/
theorem rSH.sh (h : rSH) : SH :=
  fun p hp hp₁ hdet =>
    h p hp hp₁ (solvesWithErrorInPowerExpTime_deterministic_iff.mpr hdet
      |>.mono_error (ErrorModel.deterministic_le ErrorModel.bounded))

/-- The randomized size formulation of [MITHardnessGroup2026SH, v2, §2.1, Lemma 2.1,
and §7, Theorem 7.1(a) proof]. For each fixed width `k ≥ 3`, randomized SH is equivalent to
the absence of bounded-error solvers with a fixed power saving in the number of occurring
variables plus clauses. Inputs exceeding the width bound are rejected. -/
theorem rSH_iff_KSAT {k : ℕ} (hk : 3 ≤ k) :
    rSH ↔ ∀ p : ℝ, 0 < p → p < 1 →
      ¬SolvesWithErrorInPowerExpTime (ofSet (KSAT k)) encCNF ErrorModel.bounded
        (fun φ => φ.numVars + φ.length) p := by
  obtain ⟨f, K, hf, hmem, hsize⟩ := SAT.exists_linear_size_reduction_toKSAT hk
  obtain ⟨g, L, hg, hmem', hsize'⟩ := KSAT.exists_linear_size_reduction_toSAT k
  constructor
  · intro h p hp hp₁ hsolver
    apply h p hp hp₁
    simpa only [one_mul] using hsolver.of_polyTime_promiseReduction (A := ofSet SAT) hf
      (fun φ hφ => (hmem φ).mp hφ) (fun φ hφ => mt (hmem φ).mpr hφ)
      (K := K) hsize zero_le_one hp.le
  · intro h p hp hp₁ hsolver
    apply h p hp hp₁
    simpa only [one_mul] using hsolver.of_polyTime_promiseReduction (A := ofSet (KSAT k)) hg
      (fun φ hφ => (hmem' φ).mp hφ) (fun φ hφ => mt (hmem' φ).mpr hφ)
      (K := L) hsize' zero_le_one hp.le

/-- The randomized exponent transfer of [MITHardnessGroup2026SH, v2, §7, Theorem 7.1(b)],
with a promise problem as target. Under randomized SH, a deterministic reduction from 3SAT
of power `q < 1` and parameter blowup `O(s ^ (b + η))` for every `η > 0` rules out power
`p > 0` with `b * p < 1`. The source size `s` counts occurring variables plus clauses, and
the bounds include polynomial factors in the encoded input lengths. -/
theorem rSH.not_solvesWithErrorInPowerExpTime_of_reduction (hSH : rSH)
    {β : Type} {enc : β ↪ List Bool} {B : PromiseProblem β} {μ : β → ℕ}
    {f : CNF ℕ → β} {q b p : ℝ} (hq : q < 1) (hb : 0 < b) (hp : 0 < p) (hbp : b * p < 1)
    (hf : ComputableInPowerExpTime f encCNF enc (fun φ => φ.numVars + φ.length) q)
    (hyes : ∀ φ ∈ ThreeSAT, f φ ∈ B.yes) (hno : ∀ φ ∉ ThreeSAT, f φ ∈ B.no)
    (hsize : ∀ η : ℝ, 0 < η → ∃ K : ℕ, ∀ φ,
      (μ (f φ) + 1 : ℝ) ≤ (K + 1 : ℝ) * ((φ.numVars + φ.length : ℕ) + 1 : ℝ) ^ (b + η)) :
    ¬SolvesWithErrorInPowerExpTime B enc ErrorModel.bounded μ p := by
  intro h
  obtain ⟨η, hη, hηp⟩ := exists_pos_add_mul_lt_one hp hbp
  obtain ⟨K, hK⟩ := hsize η hη
  exact (rSH_iff_KSAT (k := 3) le_rfl).mp hSH (max q ((b + η) * p))
    (lt_max_of_lt_right (mul_pos (add_pos hb hη) hp)) (max_lt hq hηp)
    (h.of_promiseReduction (A := ofSet ThreeSAT) hf hyes hno (K := K) hK hp.le)

end Cslib.Complexity
