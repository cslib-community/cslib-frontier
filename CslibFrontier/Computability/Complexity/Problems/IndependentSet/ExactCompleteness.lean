/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.IndependentSet.Exact
public import CslibFrontier.Computability.Complexity.Problems.SATUNSAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# DP-completeness of exact independent set

For a SAT–UNSAT pair, double the clauses of the first formula and give every clause of the second
formula a fresh guard. Add a unit clause requiring the guard to be false. A satisfying assignment
to the first formula can satisfy all but that unit clause by enabling the guard. If the first
formula is unsatisfiable, doubling its clauses causes at least two failures under every
assignment. Satisfying every clause requires both formulas to be satisfiable. Karp's graph converts
this one-clause gap into the exact independence-number threshold.

## Main definitions

* `Cslib.Complexity.SATUNSAT.toExactIndependentSet`: the reduction.

## Main results

* `Cslib.Complexity.SATUNSAT.toExactIndependentSet_mem_iff`: correctness of the reduction.
* `Cslib.Complexity.SATUNSAT_reducible_ExactIndependentSet`: the polynomial-time many-one reduction.
* `Cslib.Complexity.ExactIndependentSet_dpHard`: every DP language reduces to EXACT INDSET.
* `Cslib.Complexity.ExactIndependentSet_dpComplete`: completeness using the existing DP membership.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, January 2007 draft,
  Chapter 5, Exercise §8(b), printed p. 100 / PDF p. 116][AroraBarak07]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

namespace SATUNSAT

private def guardFormula (p : CNF ℕ × CNF ℕ) : CNF ℕ :=
  let first := p.1.relabel (fun v => 2 * v + 2)
  first ++ first ++ ([(0, false)] :: p.2.map fun c =>
    (0, true) :: c.relabel (fun v => 2 * v + 1))

/-- Karp's graph of the doubled and guarded formula, with target one below its clause count. -/
def toExactIndependentSet (p : CNF ℕ × CNF ℕ) : IndependentSetInstance :=
  let φ := guardFormula p
  ⟨(SAT.toIndependentSet φ).graph, φ.length - 1⟩

private theorem guardFormula_length_pos (p : CNF ℕ × CNF ℕ) :
    0 < (guardFormula p).length := by
  simp [guardFormula]

private theorem countUnsat_guardFormula (p : CNF ℕ × CNF ℕ) (σ : ℕ → Bool) :
    (guardFormula p).countUnsat σ =
      2 * p.1.countUnsat (σ ∘ fun v => 2 * v + 2) +
        if σ 0 then 1 else p.2.countUnsat (σ ∘ fun v => 2 * v + 1) := by
  unfold guardFormula CNF.relabel CNF.countUnsat
  cases h : σ 0 <;> simp [List.countP_append, List.countP_map, Literal.eval, h, two_mul,
    Function.comp_def, Nat.add_assoc]

private def mergeAssignment (a b : ℕ → Bool) (guard : Bool) (v : ℕ) : Bool :=
  if v = 0 then guard else if v % 2 = 0 then a (v / 2 - 1) else b (v / 2)

private theorem mergeAssignment_comp_even (a b : ℕ → Bool) (guard : Bool) :
    mergeAssignment a b guard ∘ (fun v => 2 * v + 2) = a := by
  funext v
  simp [mergeAssignment, show (2 * v + 2) % 2 = 0 by omega]

private theorem mergeAssignment_comp_odd (a b : ℕ → Bool) (guard : Bool) :
    mergeAssignment a b guard ∘ (fun v => 2 * v + 1) = b := by
  funext v
  simp [mergeAssignment, show (2 * v + 1) / 2 = v by omega]

private theorem exists_countUnsat_guardFormula_le_one (p : CNF ℕ × CNF ℕ) :
    (∃ σ : ℕ → Bool, (guardFormula p).countUnsat σ ≤ 1) ↔ p.1 ∈ SAT := by
  constructor
  · rintro ⟨σ, hσ⟩
    rw [countUnsat_guardFormula] at hσ
    exact ⟨σ ∘ (fun v => 2 * v + 2), CNF.countUnsat_eq_zero_iff.1 (by omega)⟩
  · rintro ⟨a, ha⟩
    refine ⟨mergeAssignment a (fun _ => false) true, ?_⟩
    rw [countUnsat_guardFormula, mergeAssignment_comp_even, CNF.countUnsat_eq_zero_iff.2 ha]
    simp [mergeAssignment]

private theorem exists_countUnsat_guardFormula_eq_zero (p : CNF ℕ × CNF ℕ) :
    (∃ σ : ℕ → Bool, (guardFormula p).countUnsat σ = 0) ↔ p.1 ∈ SAT ∧ p.2 ∈ SAT := by
  constructor
  · rintro ⟨σ, hσ⟩
    rw [countUnsat_guardFormula] at hσ
    cases hz : σ 0 <;> simp only [hz, Bool.false_eq_true, ↓reduceIte] at hσ
    · exact ⟨⟨σ ∘ (fun v => 2 * v + 2), CNF.countUnsat_eq_zero_iff.1 (by omega)⟩,
        ⟨σ ∘ (fun v => 2 * v + 1), CNF.countUnsat_eq_zero_iff.1 (by omega)⟩⟩
    · omega
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨mergeAssignment a b false, ?_⟩
    rw [countUnsat_guardFormula, mergeAssignment_comp_even, mergeAssignment_comp_odd,
      CNF.countUnsat_eq_zero_iff.2 ha, CNF.countUnsat_eq_zero_iff.2 hb]
    simp [mergeAssignment]

/-- The target in Karp's graph is exactly its independence number for SAT–UNSAT pairs. -/
theorem toExactIndependentSet_mem_iff (p : CNF ℕ × CNF ℕ) :
    toExactIndependentSet p ∈ ExactIndependentSet ↔ p ∈ SATUNSAT := by
  rw [mem_ExactIndependentSet_iff]
  change
    ((⟨(SAT.toIndependentSet (guardFormula p)).graph, (guardFormula p).length - 1⟩ :
        IndependentSetInstance) ∈ IndependentSet ∧
      (⟨(SAT.toIndependentSet (guardFormula p)).graph, (guardFormula p).length - 1 + 1⟩ :
        IndependentSetInstance) ∉ IndependentSet) ↔ _
  rw [← Graph.le_indepNum_iff, ← Graph.le_indepNum_iff,
    SAT.le_indepNum_toIndependentSet_iff, SAT.le_indepNum_toIndependentSet_iff]
  have hpos := guardFormula_length_pos p
  simp only [show ∀ n : ℕ, (guardFormula p).length - 1 + n ≤ (guardFormula p).length ↔ n ≤ 1
    from fun _ => by omega,
    show ∀ n : ℕ, (guardFormula p).length - 1 + 1 + n ≤ (guardFormula p).length ↔ n = 0
    from fun _ => by omega,
    exists_countUnsat_guardFormula_le_one, exists_countUnsat_guardFormula_eq_zero]
  change (p.1 ∈ SAT ∧ ¬(p.1 ∈ SAT ∧ p.2 ∈ SAT)) ↔ p.1 ∈ SAT ∧ p.2 ∉ SAT
  tauto

private theorem computableInPolyTime_guardFormula :
    ComputableInPolyTime guardFormula (encPair encCNF encCNF) encCNF := by
  have hdouble : ComputableInPolyTime (fun v : ℕ => 2 * v) encNat encNat := by
    rw [show (fun v : ℕ => 2 * v) = (fun v => v + v) from funext two_mul]
    exact ComputableInPolyTime.binary_add' ComputableInPolyTime.id' ComputableInPolyTime.id'
  have heven := ComputableInPolyTime.binary_add' hdouble (ComputableInPolyTime.const 2)
  have hodd := ComputableInPolyTime.binary_add' hdouble (ComputableInPolyTime.const 1)
  have hfirst := (CNF.computableInPolyTime_relabel heven).comp
    (ComputableInPolyTime.fst encCNF encCNF)
  have hclause := Clause.computableInPolyTime_relabel hodd
  have hguard : ComputableInPolyTime
      (fun c : Clause ℕ => (0, true) :: c.relabel (fun v => 2 * v + 1))
      (encClause encNat) (encClause encNat) := by
    fun_prop
  have hsecond := (ComputableInPolyTime.map hguard).comp (ComputableInPolyTime.snd encCNF encCNF)
  exact ComputableInPolyTime.listAppend' (ComputableInPolyTime.listAppend' hfirst hfirst)
    (ComputableInPolyTime.cons' (ComputableInPolyTime.const [(0, false)]) hsecond)

/-- The exact independent-set map is polynomial-time under the framed CNF-pair encoding. -/
theorem computableInPolyTime_toExactIndependentSet :
    ComputableInPolyTime toExactIndependentSet (encPair encCNF encCNF) encIndependentSetInstance :=
  have hφ := computableInPolyTime_guardFormula
  have hgraph := encIndependentSetInstance_graph_polyTime
    (SAT.computableInPolyTime_toIndependentSet.comp hφ)
  have hlen := SAT.computableInPolyTime_length hφ
  have ht : ComputableInPolyTime (fun p => (guardFormula p).length - 1)
      (encPair encCNF encCNF) encNat :=
    ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.unary_sub' hlen (ComputableInPolyTime.const 1))
  encIndependentSetInstance_mk_polyTime hgraph ht

end SATUNSAT

/-- SAT–UNSAT reduces to exact independent set in polynomial time. -/
theorem SATUNSAT_reducible_ExactIndependentSet :
    PolyTimeReducible (encPair encCNF encCNF) encIndependentSetInstance SATUNSAT
      ExactIndependentSet :=
  ⟨SATUNSAT.toExactIndependentSet, SATUNSAT.computableInPolyTime_toExactIndependentSet,
    fun p => (SATUNSAT.toExactIndependentSet_mem_iff p).symm⟩

/-- Exact independent set is DP-hard under deterministic polynomial-time many-one reductions. -/
theorem ExactIndependentSet_dpHard : DPHard encIndependentSetInstance ExactIndependentSet :=
  SATUNSAT_dpComplete.2.trans SATUNSAT_reducible_ExactIndependentSet

/-- Exact independent set is complete for the intersection class DP. -/
theorem ExactIndependentSet_dpComplete : DPComplete encIndependentSetInstance ExactIndependentSet :=
  ⟨ExactIndependentSet_mem_DP, ExactIndependentSet_dpHard⟩

end Cslib.Complexity
