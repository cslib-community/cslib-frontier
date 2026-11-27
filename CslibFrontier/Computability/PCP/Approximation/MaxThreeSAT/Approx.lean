/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.MaxThreeSAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# No polynomial-time approximation of MAX-3SAT within some ratio below one unless `P = NP`

A **`ρ`-approximation algorithm for MAX-3SAT** [Arora and Barak, Definition 18.5][AroraBarak09]
outputs, on every formula `φ` whose `m` clauses have at most three literals, an assignment
satisfying at least `ρ · val(φ) · m` clauses, where `val(φ) = 1 - CNF.unsatVal φ` is the largest
proportion of the clauses an assignment satisfies. As in
`Cslib.Complexity.exists_polyTime_maxSAT_approx`, the algorithm returns the list of variables it
sets to `true`, and its running time is measured on `encCNF`.

Such an algorithm with `s < ρ` separates the gap problem `GapThreeSAT s`: comparing the number of
clauses it satisfies with `q · m`, for a rational `q` between `s` and `ρ`, accepts every
satisfiable formula and rejects every formula of value at most `s`
(`Cslib.Complexity.GapThreeSAT_mem_PromiseP_of_approx`). With the NP-hardness of
`GapThreeSAT (1 - 1 / (3 * 2 ^ 77))` (`Cslib.Complexity.GapThreeSAT_npHard`) this gives Arora and
Barak's Corollary 18.7 with every `ρ > 1 - 1 / (3 * 2 ^ 77)`
(`Cslib.Complexity.P_eq_NP_of_maxThreeSAT_approx`).

## Main results

* `Cslib.Complexity.GapThreeSAT_mem_PromiseP_of_approx`: a polynomial-time `ρ`-approximation
  algorithm for MAX-3SAT solves `GapThreeSAT s` for every `0 ≤ s < ρ`.
* `Cslib.Complexity.P_eq_NP_of_maxThreeSAT_approx`: **Arora–Barak Corollary 18.7**, a
  polynomial-time `ρ`-approximation algorithm for MAX-3SAT with `ρ > 1 - 1 / (3 * 2 ^ 77)` gives
  `P = NP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 18.2][AroraBarak09]
* [S. Arora, C. Lund, R. Motwani, M. Sudan, M. Szegedy, *Proof verification and the hardness of
  approximation problems*][AroraLundMotwaniSudanSzegedy1998]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-- **A MAX-3SAT approximation algorithm separates the gap problem.** Let `A` be a polynomial-time
algorithm that, on every formula `φ` with at most three literals per clause, sets to `true` a list
of variables satisfying at least `ρ · (1 - unsatVal φ) · |φ|` clauses. Then `A` decides
`GapThreeSAT s` for every soundness `0 ≤ s < ρ`: accept when the number of satisfied clauses is at
least `q · |φ|`, for a rational `q` with `s < q < ρ`. -/
theorem GapThreeSAT_mem_PromiseP_of_approx {A : CNF ℕ → List ℕ} {ρ s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < ρ) (hA : ComputableInPolyTime A encCNF (encList encNat))
    (happrox : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
      ρ * (1 - φ.unsatVal) * φ.length ≤
        φ.length - φ.countUnsat (fun v => decide (v ∈ A φ))) :
    GapThreeSAT s ∈ PromiseP encCNF := by
  obtain ⟨q, hsq, hqρ⟩ := exists_rat_btwn hs
  have hq0 : (0 : ℝ) < q := hs0.trans_lt hsq
  set a := q.num.toNat
  set b := q.den
  have hab : (q : ℝ) = a / b := by
    have hnum : (0 : ℤ) ≤ q.num := Rat.num_nonneg.2 (by exact_mod_cast hq0.le)
    rw [← Rat.num_div_den q]
    push_cast
    rw [show ((q.num : ℤ) : ℝ) = (a : ℝ) by exact_mod_cast (Int.toNat_of_nonneg hnum).symm]
  have hb : (0 : ℝ) < b := by exact_mod_cast q.den_pos
  set u : CNF ℕ → ℕ := fun φ => φ.countUnsat fun v => decide (v ∈ A φ)
  have hu (φ : CNF ℕ) : (u φ : ℝ) ≤ φ.length := by exact_mod_cast CNF.countUnsat_le_length _ φ
  /- The decider compares the satisfied clauses `|φ| - u φ` with `q · |φ| = (a / b) · |φ|`,
  cleared of denominators and subtractions. -/
  have hiff (φ : CNF ℕ) :
      a * φ.length + b * u φ ≤ b * φ.length ↔ (q : ℝ) * φ.length ≤ φ.length - u φ := by
    rw [hab, div_mul_eq_mul_div, div_le_iff₀ hb, ← @Nat.cast_le ℝ]
    push_cast
    constructor <;> intro h <;> nlinarith
  refine mem_PromiseP_iff.2
    ⟨fun φ => decide (a * φ.length + b * u φ ≤ b * φ.length), ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · have hm : ComputableInPolyTime (fun φ : CNF ℕ => φ.length) encCNF encNat :=
      length_list_binary _
    have hu' : ComputableInPolyTime u encCNF encNat :=
      unary_to_binary.comp ((computableInPolyTime_countUnsat_mem encNat).comp (id'.prod hA))
    exact binary_le' (binary_add' (binary_mul' (const a) hm) (binary_mul' (const b) hu'))
      (binary_mul' (const b) hm)
  · rw [yes_GapThreeSAT] at hφ
    have hval : φ.unsatVal = 0 := (CNF.unsatVal_eq_zero_iff φ).2 hφ.2
    have h := happrox φ hφ.1
    rw [hval, sub_zero, mul_one] at h
    refine decide_eq_true ((hiff φ).2 (le_trans ?_ h))
    exact mul_le_mul_of_nonneg_right hqρ.le (Nat.cast_nonneg _)
  · simp only [GapThreeSAT, PromiseProblem.no_restrict, Set.mem_inter_iff,
      PromiseProblem.mem_no_gapMax] at hφ
    obtain ⟨⟨hval, hs1⟩, -⟩ := hφ
    refine decide_eq_false fun h => ?_
    have h := (hiff φ).1 h
    have hle : φ.unsatVal ≤ u φ / φ.length := CNF.unsatVal_le φ _
    rcases Nat.eq_zero_or_pos φ.length with h0 | hpos
    · rw [h0, Nat.cast_zero, div_zero] at hle
      linarith
    · have hm : (0 : ℝ) < φ.length := by exact_mod_cast hpos
      have hle' : φ.length - (u φ : ℝ) ≤ s * φ.length := by
        rw [le_div_iff₀ hm] at hle
        nlinarith
      nlinarith

/-- **Arora–Barak Corollary 18.7: MAX-3SAT has no polynomial-time `ρ`-approximation algorithm
for some constant `ρ < 1` unless `P = NP`** [Arora and Barak, Corollary 18.7][AroraBarak09]. Every
`ρ > 1 - 1 / (3 * 2 ^ 77)` is such a constant: if a polynomial-time algorithm `A` outputs, on every
formula `φ` with at most three literals per clause, an assignment (the variables set to `true`)
satisfying at least `ρ · val(φ) · |φ|` of its clauses, where `val(φ) = 1 - unsatVal φ`, then
`P = NP`.

The source's `ρ`-approximation algorithms (Definition 18.5) are those on 3CNF formulas, whose
clauses have at most three literals (Section 2.3.1). Formulas are encoded by `encCNF`, with binary
variable indices; the conclusion holds for every instance encoding of `P` and `NP`. The constant
comes from `GapThreeSAT_npHard`, through Dinur's gap amplification instead of the source's
PCP-theorem verifier. -/
theorem P_eq_NP_of_maxThreeSAT_approx {A : CNF ℕ → List ℕ} {ρ : ℝ}
    (hρ : 1 - 1 / (3 * 2 ^ 77) < ρ) (hA : ComputableInPolyTime A encCNF (encList encNat))
    (happrox : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
      ρ * (1 - φ.unsatVal) * φ.length ≤
        φ.length - φ.countUnsat (fun v => decide (v ∈ A φ)))
    {β : Type} (enc : β ↪ List Bool) : P enc = NP enc :=
  GapThreeSAT_npHard.P_eq_NP_of_mem_PromiseP
    (GapThreeSAT_mem_PromiseP_of_approx (by norm_num) hρ hA happrox) enc

end Cslib.Complexity
