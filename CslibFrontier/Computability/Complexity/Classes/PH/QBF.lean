/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.QBF.Blocks
public import CslibFrontier.Computability.Complexity.Classes.PH

/-!
# Alternating word quantifiers and Boolean-formula blocks

`QBF.eval_blocks_eq_true_iff` relates syntactic variable blocks to the hierarchy's alternating
word quantifiers. A word supplies the truth values of one block, including repeated names and
empty blocks. Negating the matrix and swapping the prefix negates the value.
-/

public section

namespace Cslib.Logic.PL.QBF

variable {V : Type*} [DecidableEq V]

/-- Alternating quantifier blocks evaluate by alternating over words of the corresponding
lengths and updating the assignment along the concatenated lists of variables. -/
theorem eval_blocks_eq_true_iff (q : Bool) (bs : List (List V)) (φ : QBF V) (σ : V → Bool) :
    (blocks q bs φ).eval σ = true ↔
      Cslib.Complexity.Alternation q (bs.map List.length)
        (fun w => φ.eval (updates σ bs.flatten w) = true) := by
  induction bs generalizing q σ with
  | nil => simp [blocks, updates]
  | cons vs bs ih =>
    have key (w : List Bool) (hw : w.length = vs.length) (r : Bool) :
        (blocks r bs φ).eval (updates σ vs w) = true ↔
          Cslib.Complexity.Alternation r (bs.map List.length)
            (fun u => φ.eval (updates σ (vs ++ bs.flatten) (w ++ u)) = true) := by
      rw [ih]
      simp only [updates_append hw]
    cases q
    · rw [blocks, eval_alls_iff_word]
      simp only [List.map_cons, List.flatten_cons, Cslib.Complexity.alternation_false_cons]
      exact forall_congr' fun w => imp_congr_right fun hw => key w hw true
    · rw [blocks, eval_exs_iff_word]
      simp only [List.map_cons, List.flatten_cons, Cslib.Complexity.alternation_true_cons]
      exact exists_congr fun w => and_congr_right fun hw => key w hw false

/-- Negation swaps every quantifier in the prefix and negates the matrix. -/
theorem eval_blocks_dual (q : Bool) (bs : List (List V)) (φ : QBF V) (σ : V → Bool) :
    (blocks (!q) bs φ.not).eval σ = !(blocks q bs φ).eval σ := by
  rw [Bool.eq_iff_iff, Bool.not_eq_true', ← Bool.not_eq_true,
    eval_blocks_eq_true_iff, eval_blocks_eq_true_iff,
    Cslib.Complexity.not_alternation]
  exact Cslib.Complexity.alternation_congr fun w => by simp

end Cslib.Logic.PL.QBF
