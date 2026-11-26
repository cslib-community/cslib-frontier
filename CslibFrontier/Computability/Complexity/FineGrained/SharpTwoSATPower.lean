/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.SharpSatisfiabilityHypothesis
public import CslibFrontier.Computability.Complexity.Problems.SharpTwoSATParity
import CslibFrontier.Computability.Complexity.FineGrained.ThreeOccurrenceReduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Counting Satisfiability Hypothesis lower bound for bounded-degree #2SAT

The transfer in [MITHardnessGroup2026SH, v2, §6, Corollary 6.1] uses two count queries and
subtraction. We compose the parsimonious width-three conversion with the parity queries and
the three-occurrence compiler. Each resulting query has width at most two, at most three
occurrences per variable, and linear variable-plus-clause size. The solver reads the ordinary
binary CNF encoding and only needs to give an answer within its bound on promised inputs.

## Main results

* `Cslib.Complexity.SharpSH.not_computableInPowerExpTime_sharpTwoSAT_threeOccurrence`:
  the lower bound on the width-two, three-occurrence promise.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM SharpTwoSATParity

private def splitParityQuery (odd : Bool) (φ : CNF ℕ) : CNF ℕ :=
  toThreeOccurrenceDense (parityQuery (toSharpThreeSAT φ) odd)

private theorem width_splitParityQuery (odd : Bool) (φ : CNF ℕ) :
    ∀ c ∈ splitParityQuery odd φ, c.length ≤ 2 :=
  width_toThreeOccurrenceDense (by decide) (width_parityQuery _ odd)

private theorem sharpTwoSAT_splitParityQuery (odd : Bool) (φ : CNF ℕ) :
    SharpTwoSAT (splitParityQuery odd φ) = SharpTwoSAT (parityQuery (toSharpThreeSAT φ) odd) := by
  change SharpKSAT 2 (splitParityQuery odd φ) = SharpKSAT 2 (parityQuery (toSharpThreeSAT φ) odd)
  rw [SharpKSAT_of_width (width_splitParityQuery odd φ),
    SharpKSAT_of_width (width_parityQuery _ odd)]
  exact modelCount_toThreeOccurrenceDense _

private theorem size_splitParityQuery (odd : Bool) (φ : CNF ℕ) :
    (splitParityQuery odd φ).numVars + (splitParityQuery odd φ).length ≤
      3300 * (φ.numVars + φ.length + φ.vars.length) + 30 := by
  have hw := width_parityQuery (toSharpThreeSAT φ) odd
  have hv := numVars_toThreeOccurrenceDense_le_mul_length hw
  have hm := length_toThreeOccurrenceDense_le_mul_length hw
  have hs := size_parityQuery_le (toSharpThreeSAT φ) odd
    (fun _ hc => length_le_three_of_mem_toSharpThreeSAT hc)
  have ht := toSharpThreeSAT_size_le φ
  unfold splitParityQuery
  omega

/-- The native multitape form of [MITHardnessGroup2026SH, v2, §6, Corollary 6.1].
Under `SharpSH`, even width-two formulas with at most three literal occurrences per variable
admit no fixed power saving in the exponent in occurring variables plus clauses. Both the
time and correctness guarantee apply only to promised formulas. The subtype's encoding is
the ordinary binary CNF encoding of the formula. -/
theorem SharpSH.not_computableInPowerExpTime_sharpTwoSAT_threeOccurrence
    (hSH : SharpSH) {p : ℝ} (hp : 0 < p) (hp₁ : p < 1) :
    let good := fun ψ : CNF ℕ => (∀ c ∈ ψ, c.length ≤ 2) ∧ (∀ v, ψ.vars.count v ≤ 3)
    ¬ComputableInPowerExpTime (fun ψ : Subtype good => SharpTwoSAT ψ.val)
      ((Function.Embedding.subtype good).trans encCNF) encNat
      (fun ψ => ψ.val.numVars + ψ.val.length) p := by
  intro good hsolver
  let query (odd : Bool) (φ : CNF ℕ) : Subtype good :=
    ⟨splitParityQuery odd φ, width_splitParityQuery odd φ,
      count_vars_toThreeOccurrenceDense_le _⟩
  let μ (φ : CNF ℕ) := φ.numVars + φ.length + φ.vars.length
  have hquery (odd : Bool) : ComputableInPolyTime (query odd) encCNF
      ((Function.Embedding.subtype good).trans encCNF) := by
    have h : ComputableInPolyTime (splitParityQuery odd) encCNF encCNF :=
      computableInPolyTime_toThreeOccurrenceDense.comp
        ((computableInPolyTime_parityQuery odd).comp computableInPolyTime_toSharpThreeSAT)
    obtain ⟨t, s, ht, hs, k, State, hfinite, tm, htm⟩ := h
    exact ⟨t, s, ht, hs, k, State, hfinite, tm, fun φ => htm φ⟩
  have hcount (odd : Bool) : ComputableInPowerExpTime
      (fun φ => SharpTwoSAT (splitParityQuery odd φ)) encCNF encNat μ p := by
    have hsize (φ : CNF ℕ) :
        (((query odd φ).val.numVars + (query odd φ).val.length : ℕ) + 1 : ℝ) ≤
          (3300 + 1 : ℝ) * (μ φ + 1 : ℝ) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
      have h := size_splitParityQuery odd φ
      exact_mod_cast (show (splitParityQuery odd φ).numVars +
        (splitParityQuery odd φ).length + 1 ≤ (3300 + 1) * (μ φ + 1) by dsimp [μ]; omega)
    change ComputableInPowerExpTime ((fun ψ : Subtype good => SharpTwoSAT ψ.val) ∘ query odd)
      encCNF encNat μ p
    simpa only [one_mul] using
      hsolver.comp_polyTime (hquery odd) (K := 3300) hsize zero_le_one hp.le
  have hsub : ComputableInPolyTime (fun xy : ℕ × ℕ => xy.1 - xy.2)
      (encPair encNat encNat) encNat :=
    ComputableInPolyTime.binary_sub'
      (ComputableInPolyTime.fst _ _) (ComputableInPolyTime.snd _ _)
  obtain ⟨e, he⟩ := ComputableInExpTime.of_computableInPolyTime (μ := fun _ => 0) hsub
  have hpost : ComputableInPowerExpTime (fun xy : ℕ × ℕ => xy.1 - xy.2)
      (encPair encNat encNat) encNat (fun _ => 0) 0 := ⟨0, e, by simpa using he⟩
  have hsum := hpost.comp ((hcount false).prod (hcount true)) (b := 0) (K := 0)
    (fun _ => by simp) (by norm_num)
  have hcorrect :
      (fun xy : ℕ × ℕ => xy.1 - xy.2) ∘
        (fun φ => (SharpTwoSAT (splitParityQuery false φ), SharpTwoSAT (splitParityQuery true φ))) =
      SharpSAT := by
    funext φ
    simp only [Function.comp_def, sharpTwoSAT_splitParityQuery,
      ← sharpSAT_eq_parityQuery_sub, SharpSAT, modelCount_toSharpThreeSAT]
  apply hSH p hp hp₁
  simpa only [hcorrect, mul_zero, max_eq_left hp.le] using hsum

end Cslib.Complexity
