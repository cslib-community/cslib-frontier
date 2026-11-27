/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Tableau
public import CslibFrontier.Logics.Propositional.DNF
import CslibFrontier.Logics.Propositional.CNF.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Quantified tableau matrix normal forms

The tableau construction of [Arora and Barak, Exercise 5 §1][AroraBarak07]
retains a conjunctive or disjunctive matrix depending on the final block.
The tableau accepts the complemented verifier when the final block is universal.

## Main definitions

* `Instance` and `encoding`: a quantifier prefix with a signed matrix.
* `prenexAt`: interpret the signed matrix as CNF or DNF.

## Main results

* `eval_tableauDNF` and `polytime_tableauDNF`: semantics and construction of the negative tableau.

## References

* [Arora and Barak, Computational Complexity, Exercise 5 §1][AroraBarak07]
-/

public section

namespace Cslib.Complexity.QuantifiedSAT.WidthThree

open Cslib.Logic.PL Cslib.Complexity
open _root_.Turing.MultiTapeTM ComputableInPolyTime

/-- The tableau in disjunctive normal form, used when the last block is universal. -/
noncomputable def tableauDNF {k : ℕ} {State : Type} [Fintype State]
    (tab : CNF (CookLevin.Var k State)) (w : ℕ) : DNF ℕ :=
  CNF.negate (TQBF.prenexMatrix tab w)

/-- The DNF evaluates to the complement of the tableau matrix. -/
theorem eval_tableauDNF {k : ℕ} {State : Type} [Fintype State]
    (tab : CNF (CookLevin.Var k State)) (w : ℕ) (σ : ℕ → Bool) :
    (tableauDNF tab w).eval σ = ((TQBF.baseMatrix tab w).not).eval σ := by
  simp [tableauDNF, ← QBF.eval_ofCNF, TQBF.eval_prenexMatrix]

attribute [local irreducible] ComputableInPolyTime

/-- The negative tableau matrix is polynomial-time in the tableau and unary width. -/
theorem polytime_tableauDNF {α : Type} {enc : α ↪ List Bool} {k : ℕ}
    {State : Type} [Fintype State] {tab : α → CNF (CookLevin.Var k State)} {w : α → ℕ}
    (htab : ComputableInPolyTime tab enc (encCNFOver CookLevin.encVar))
    (hw : ComputableInPolyTime w enc encUnary) :
    ComputableInPolyTime (fun a => tableauDNF (tab a) (w a)) enc (encCNFOver encNat) :=
  (CNF.computableInPolyTime_negate encNat).comp (TQBF.computableInPolyTime_prenexMatrix htab hw)

/-- Interpret the DNF as the negation of its dual CNF. -/
@[expose] def matrix (dnf : DNF ℕ) : QBF ℕ := (QBF.ofCNF dnf.negate).not

/-- Conversion to quantified Boolean syntax preserves DNF evaluation. -/
theorem eval_matrix (dnf : DNF ℕ) (σ : ℕ → Bool) :
    (matrix dnf).eval σ = dnf.eval σ := by simp [matrix]

/-- The DNF and the original tableau matrix have the same free variables. -/
theorem tableau_freeVars {k : ℕ} {State : Type} [Fintype State]
    (tab : CNF (CookLevin.Var k State)) (w : ℕ) :
    (matrix (tableauDNF tab w)).freeVars = (TQBF.baseMatrix tab w).freeVars := by
  simpa [matrix, tableauDNF] using TQBF.freeVars_prenexMatrix tab w

open Cslib.Complexity.QuantifiedSAT _root_.Turing TQBF

/-- A grouped quantified normal form with the usual signed-literal convention. -/
structure Instance where
  /-- The quantifier blocks, in prefix order. -/
  blocks : List (List ℕ)
  /-- Signed clauses or terms, according to the final block's polarity. -/
  matrix : DNF ℕ

/-- Frame the list of binary variable blocks as a whole, then encode the signed matrix. -/
enc_structure encoding : Instance where
  blocks : (encList (encList encNat)),
  matrix : (encCNFOver encNat)

/-- Interpret a grouped matrix with its native final-block polarity. -/
@[expose] def prenexAt (r : Bool) (p : Instance) : PrenexQBF :=
  ⟨p.blocks, if r then QBF.ofCNF p.matrix else matrix p.matrix⟩

/-- Convert the appropriate matrix interpretation to prenex QBF in polynomial time. -/
theorem polytime_prenexAt (r : Bool) : ComputableInPolyTime (prenexAt r) encoding encPrenexQBF := by
  have hb := encoding_blocks_polyTime (id' (encIn := encoding))
  have hm := encoding_matrix_polyTime (id' (encIn := encoding))
  cases r
  · have d : ComputableInPolyTime (DNF.negate (V := ℕ))
        (encCNFOver encNat) (encCNFOver encNat) :=
      DNF.computableInPolyTime_negate encNat
    exact encPrenexQBF_mk_polyTime hb
      (TQBF.computableInPolyTime_not (TQBF.computableInPolyTime_ofCNF (d.comp hm)))
  · exact encPrenexQBF_mk_polyTime hb (TQBF.computableInPolyTime_ofCNF hm)

/-- Switch between a normal form and the list of signed literals of its Boolean dual. -/
@[expose] def negateMatrix (p : Instance) : Instance := ⟨p.blocks, DNF.negate p.matrix⟩

/-- Change only the signs of the stored literals in polynomial time. -/
theorem polytime_negateMatrix : ComputableInPolyTime negateMatrix encoding encoding := by
  have d : ComputableInPolyTime (DNF.negate (V := ℕ))
      (encCNFOver encNat) (encCNFOver encNat) :=
    DNF.computableInPolyTime_negate encNat
  exact encoding_mk_polyTime (encoding_blocks_polyTime id')
    (d.comp (encoding_matrix_polyTime id'))

/-- Use the dual matrix in the conjunctive case of an internally disjunctive construction. -/
@[expose] def orientMatrix (r : Bool) (p : Instance) : Instance :=
  if r then negateMatrix p else p

/-- Orienting the matrix is polynomial time for either polarity. -/
theorem polytime_orientMatrix (r : Bool) :
    ComputableInPolyTime (orientMatrix r) encoding encoding := by
  cases r
  · exact id'
  · exact polytime_negateMatrix

/-- The two interpretations of the stored matrix have the same free variables. -/
theorem prenexAt_freeVars (r : Bool) (p : Instance) :
    (prenexAt r p).matrix.freeVars = (matrix p.matrix).freeVars := by
  cases r
  · rfl
  · have vars (d : DNF ℕ) : d.negate.vars = CNF.vars d := by
      induction d with
      | nil => rfl
      | cons t ts ih =>
        simp only [DNF.negate, List.map_cons, CNF.vars] at *
        simp only [List.flatten_cons, List.map_append, Term.negate, List.map_map, Function.comp_def]
        exact congrArg (List.append (t.map Prod.fst)) ih
    ext v
    simp only [prenexAt, matrix, QBF.freeVars_not, QBF.mem_freeVars_ofCNF, ↓reduceIte, vars]

/-- Well-formedness depends on the variable names, independently of interpretation. -/
theorem prenexAt_wf_iff (r : Bool) (p : Instance) (i : ℕ) :
    (prenexAt r p).WellFormed i ↔ (prenexAt false p).WellFormed i := by
  have h (p : Instance) : (prenexAt r p).matrix.QuantifierFree := by
    cases r <;> simp [prenexAt, matrix, QBF.quantifierFree_not, QBF.quantifierFree_ofCNF]
  simp only [PrenexQBF.WellFormed, prenexAt_freeVars, h, true_and]
  simp [prenexAt, matrix, QBF.quantifierFree_not, QBF.quantifierFree_ofCNF]

/-- A change of signs preserves the well-formedness condition. -/
theorem orientMatrix_wf (r : Bool) (p : Instance) (i : ℕ) :
    (prenexAt false (orientMatrix r p)).WellFormed i ↔ (prenexAt false p).WellFormed i := by
  cases r
  · rfl
  · have vars : (matrix (DNF.negate p.matrix)).freeVars = (matrix p.matrix).freeVars := by
      rw [show matrix (DNF.negate p.matrix) = (QBF.ofCNF p.matrix).not by
        unfold matrix
        congr 2
        exact CNF.negate_negate p.matrix, QBF.freeVars_not]
      exact prenexAt_freeVars true p
    have test (d : DNF ℕ) : (matrix d).QuantifierFree :=
      QBF.quantifierFree_not.mpr (QBF.quantifierFree_ofCNF _)
    change (p.blocks.length = i ∧ (matrix (DNF.negate p.matrix)).QuantifierFree ∧
        (matrix (DNF.negate p.matrix)).freeVars ⊆ p.blocks.flatten.toFinset) ↔
      (p.blocks.length = i ∧ (matrix p.matrix).QuantifierFree ∧
        (matrix p.matrix).freeVars ⊆ p.blocks.flatten.toFinset)
    simp only [test, true_and, vars]

end Cslib.Complexity.QuantifiedSAT.WidthThree
