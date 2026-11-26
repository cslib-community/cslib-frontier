/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.CountingExponents
public import CslibFrontier.Computability.Complexity.FineGrained.PowerTime
public import CslibFrontier.Computability.Complexity.FineGrained.SatisfiabilityHypothesis
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The counting Satisfiability Hypothesis

`SharpSH` measures exact model counting in occurring variables, clauses, and literal
occurrences. The fixed-width formulation absorbs the literal count into the clause count.
The proof follows the counting argument of [MITHardnessGroup2026SH, v2, §2.1, Lemma 2.1].

The native encoding permits repeated clauses and arbitrarily large binary variable labels.
Running time allows polynomial dependence on the encoded input length. The model count is
over occurring variables. For a declared finite superset of those variables,
`CNF.modelCountOn_eq_mul_modelCount` supplies a factor of two per unused variable, and
`CNF.modelCountOn_denseRelabel` relates the occurring count to a compact declaration.

## Main definitions

* `Cslib.Complexity.SharpSH`: the counting hypothesis for unrestricted CNF.

## Main results

* `Cslib.Complexity.SharpSH_iff_SharpKSAT`: the fixed-width size formulation.
* `Cslib.Complexity.SH.sharpSH`: the decision hypothesis implies the counting hypothesis.

## References

* [MIT Hardness Group, *ETH is Dead, Long Live SH*][MITHardnessGroup2026SH], v2, §2 and
  §2.1, Lemma 2.1.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The counting Satisfiability Hypothesis [MITHardnessGroup2026SH, v2, §2, p. 5]
in the native deterministic multitape model.
It rules out any fixed power saving in the exponent for computing `SharpSAT` from binary
CNF to binary counts, with size given by occurring variables, clauses, and literal occurrences. -/
@[expose] def SharpSH : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 →
    ¬ComputableInPowerExpTime SharpSAT encCNF encNat
      (fun φ => φ.numVars + φ.length + φ.vars.length) p

/-- The parsimonious width-three conversion has linear variable-plus-clause size in the
source variable and clause counts and number of literal occurrences. -/
theorem toSharpThreeSAT_size_le (φ : CNF ℕ) :
    (toSharpThreeSAT φ).numVars + (toSharpThreeSAT φ).length ≤
      11 * (φ.numVars + φ.length + φ.vars.length) := by
  have hclauses : (toSharpThreeSAT φ).length ≤ φ.length + 3 * φ.vars.length := by
    rw [toSharpThreeSAT, CNF.relabel, List.length_map, CNF.length_toExact3CNF]
    calc
      _ ≤ (φ.map fun c => 3 * c.length + 1).sum := List.sum_le_sum fun _ _ => by omega
      _ = _ := by
        rw [CNF.length_vars, List.sum_map_add, List.sum_map_mul_left, List.map_const',
          List.sum_replicate_nat]
        omega
  have hvars := (CNF.numVars_le_length_vars (toSharpThreeSAT φ)).trans
    (length_vars_toSharpThreeSAT φ).2
  omega

/-- The native counting size formulation [MITHardnessGroup2026SH, v2, §2.1, Lemma 2.1].
For any fixed width `k ≥ 3`, `SharpSH` is
equivalent to the absence of a fixed power saving for `SharpKSAT k` in the number of
occurring variables plus clauses. On wider inputs `SharpKSAT k` returns zero. -/
theorem SharpSH_iff_SharpKSAT {k : ℕ} (hk : 3 ≤ k) :
    SharpSH ↔ ∀ p : ℝ, 0 < p → p < 1 →
      ¬ComputableInPowerExpTime (SharpKSAT k) encCNF encNat (fun φ => φ.numVars + φ.length) p := by
  constructor
  · intro h p hp hp₁ hsolver
    apply h p hp hp₁
    have hcomp : SharpKSAT k ∘ toSharpThreeSAT = SharpSAT := funext fun φ =>
      (SharpKSAT_of_width fun _ hc =>
        (length_le_three_of_mem_toSharpThreeSAT hc).trans hk).trans
        (modelCount_toSharpThreeSAT φ)
    have hsize (φ : CNF ℕ) :
        (((toSharpThreeSAT φ).numVars + (toSharpThreeSAT φ).length : ℕ) + 1 : ℝ) ≤
          (11 + 1 : ℝ) * ((φ.numVars + φ.length + φ.vars.length : ℕ) + 1 : ℝ) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
      have h := toSharpThreeSAT_size_le φ
      exact_mod_cast (by omega : (toSharpThreeSAT φ).numVars + (toSharpThreeSAT φ).length + 1 ≤
        (11 + 1) * (φ.numVars + φ.length + φ.vars.length + 1))
    simpa only [hcomp, one_mul] using hsolver.comp_polyTime computableInPolyTime_toSharpThreeSAT
      (K := 11) hsize zero_le_one hp.le
  · rintro h p hp hp₁ ⟨C, e, hsolver⟩
    apply h p hp hp₁
    let D : ℕ := ⌈(C : ℝ) * (k + 1 : ℝ) ^ p⌉₊
    have hscale (φ : CNF ℕ) (hφ : (φ.all fun c => decide (c.length ≤ k)) = true) :
        (C : ℝ) * ((φ.numVars + φ.length + φ.vars.length : ℕ) + 1 : ℝ) ^ p ≤
          (D : ℝ) * ((φ.numVars + φ.length : ℕ) + 1 : ℝ) ^ p := by
      have hw : ∀ c ∈ φ, c.length ≤ k := by
        simpa only [List.all_eq_true, decide_eq_true_eq] using hφ
      have hlinear : φ.numVars + φ.length + φ.vars.length + 1 ≤
          (k + 1) * (φ.numVars + φ.length + 1) := calc
        _ ≤ φ.numVars + φ.length + 1 + k * φ.length := by
          have := CNF.length_vars_le_mul_length hw
          omega
        _ ≤ φ.numVars + φ.length + 1 + k * (φ.numVars + φ.length + 1) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
        _ = _ := by ring
      have hreal : ((φ.numVars + φ.length + φ.vars.length : ℕ) + 1 : ℝ) ≤
          (k + 1 : ℝ) * ((φ.numVars + φ.length : ℕ) + 1 : ℝ) := by exact_mod_cast hlinear
      have hpow := Real.rpow_le_rpow (by positivity) hreal hp.le
      rw [Real.mul_rpow (by positivity) (by positivity)] at hpow
      calc
        _ ≤ (C : ℝ) * ((k + 1 : ℝ) ^ p * ((φ.numVars + φ.length : ℕ) + 1 : ℝ) ^ p) :=
          mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg C)
        _ = ((C : ℝ) * (k + 1 : ℝ) ^ p) * ((φ.numVars + φ.length : ℕ) + 1 : ℝ) ^ p := by
          rw [mul_assoc]
        _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
    obtain ⟨e', hguard⟩ := hsolver.ite_polyTime_of_le (computableInPolyTime_all_length_le k)
      (ComputableInPolyTime.const 0) (fun _ => by positivity) hscale
    refine ⟨D, e', ?_⟩
    delta SharpKSAT
    exact hguard

/-- The Satisfiability Hypothesis implies its counting counterpart
[MITHardnessGroup2026SH, v2, §2, p. 5]. Testing the binary model count for positivity preserves
the exponent power because the count has polynomially bounded bit length. -/
theorem SH.sharpSH (h : SH) : SharpSH := by
  rintro p hp hp₁ ⟨C, e, hcount⟩
  obtain ⟨d, hdec⟩ := DecidableInTimeO.of_computableInTimeO_polyBounded
    (fun _ => by positivity) hcount polyBounded_length_encNat_SharpSAT
    ComputableInPolyTime.binary_pos
  rw [(Set.ext fun _ => by simp [SharpSAT.mem_SAT_iff] :
    {φ | decide (0 < SharpSAT φ) = true} = SAT)] at hdec
  exact h p hp hp₁ ⟨C, d, hdec⟩

end Cslib.Complexity
