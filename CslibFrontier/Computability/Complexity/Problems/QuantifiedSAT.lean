/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Evaluation
public import CslibFrontier.Computability.Complexity.Problems.TQBF.Closed
public import CslibFrontier.Computability.Complexity.Classes.PH.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Prenex quantified SAT instances

A `PrenexQBF` records a list of variable blocks and a matrix in the existing `QBF` syntax.
Its `formula` alternates the blocks, starting existentially or universally. The matrix is not
restricted to CNF: well-formedness requires it to be quantifier-free and the prefixed formula
to be closed. Empty blocks allow a shorter prefix to be padded to a given level.

This is the grouped-prefix representation of [Arora–Barak, draft Example 5.9, display (1),
printed pp. 94–95][AroraBarak07] and [Goldreich, Exercise 3.7,
printed p. 133][Goldreich2007DraftR2].
The record stores syntax, not a verifier or an efficiency hypothesis.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-- A grouped prenex Boolean formula, with the matrix in the existing quantified-formula syntax.
Well-formedness is a language condition, so malformed instances can be rejected. -/
structure PrenexQBF where
  /-- Variable blocks in outermost-first order. Empty blocks are permitted. -/
  blocks : List (List ℕ)
  /-- The Boolean matrix; language membership requires quantifier-freeness. -/
  matrix : QBF ℕ

/-- Binary variable names in framed lists of framed blocks, followed by the prefix-token encoding
of the matrix. The block list is framed as a whole before the matrix. -/
enc_structure encPrenexQBF : PrenexQBF where
  blocks : (encList (encList encNat)),
  matrix : encQBF

attribute [fun_prop] encPrenexQBF_blocks_polyTime encPrenexQBF_matrix_polyTime
  encPrenexQBF_mk_polyTime

namespace PrenexQBF

/-- The QBF represented by the record, starting existentially for `q = true`. -/
@[expose] def formula (q : Bool) (a : PrenexQBF) : QBF ℕ :=
  QBF.blocks q a.blocks a.matrix

/-- A well-formed level-`i` instance has `i` blocks, a quantifier-free matrix, and no free
variables after prefixing. Empty blocks represent fewer than `i` effective alternations. -/
@[expose] def WellFormed (i : ℕ) (a : PrenexQBF) : Prop :=
  a.blocks.length = i ∧ a.matrix.QuantifierFree ∧
    a.matrix.freeVars ⊆ a.blocks.flatten.toFinset

instance (i : ℕ) : DecidablePred (WellFormed i) := fun a => inferInstanceAs (Decidable
  (a.blocks.length = i ∧ a.matrix.QuantifierFree ∧
    a.matrix.freeVars ⊆ a.blocks.flatten.toFinset))

/-- Well-formed instances yield closed formulas for either initial polarity. -/
theorem closed_formula {i : ℕ} {a : PrenexQBF} (h : a.WellFormed i) (q : Bool) :
    (a.formula q).Closed := by
  rw [QBF.Closed, formula, QBF.freeVars_blocks, Finset.sdiff_eq_empty_iff_subset]
  exact h.2.2

/-- The truth condition for a grouped-prefix instance, using alternating word certificates. -/
theorem eval_formula (a : PrenexQBF) (q : Bool) :
    (a.formula q).eval (fun _ => false) = true ↔
      Alternation q (a.blocks.map List.length)
        (fun w => a.matrix.eval (QBF.updates (fun _ => false) a.blocks.flatten w) = true) :=
  QBF.eval_blocks_eq_true_iff ..

end PrenexQBF

/-- Existential-first true closed prenex formulas with `i` blocks (empty blocks are allowed),
[Arora–Barak, Example 5.9 and Exercise 5 §1][AroraBarak07],
[Goldreich, Exercise 3.7][Goldreich2007DraftR2]. Level zero consists of true closed
quantifier-free matrices, and is excluded from the positive-level hardness claim. -/
@[expose] def PrenexQBF.SigmaSAT (i : ℕ) : Set PrenexQBF :=
  {a | a.WellFormed i ∧ (a.formula true).eval (fun _ => false) = true}

/-- Universal-first true closed prenex formulas with `i` blocks, the dual of `SigmaSAT`. -/
@[expose] def PrenexQBF.PiSAT (i : ℕ) : Set PrenexQBF :=
  {a | a.WellFormed i ∧ (a.formula false).eval (fun _ => false) = true}

end Cslib.Complexity
