/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

public import CslibFrontier.Foundations.Computability.RecursiveInJoin
public import CslibFrontier.Foundations.Computability.KleenePost

/-! Clients of the Turing join under module encapsulation. The join of the squaring and identity
oracles is evaluated on concrete inputs, and a nowhere-defined left half leaves the right half
defined. The program `oracle` is lifted along `p ≤ᵀ p ⊕ x` and `x ≤ᵀ p ⊕ x`, and the program
`joinLeft` relative to `p ⊕ x` is run relative to the squaring oracle from codes for its two
halves; the outputs depend on the oracles, so the uniform translations are not constant. The
join of two Kleene–Post incomparable degrees lies strictly above both, so the semilattice
structure is not degenerate. -/

public section

namespace CslibFrontierTests.RecursiveInJoin

open Encodable Denumerable Nat.RecursiveIn.Code
open scoped Computability Partrec

/-- The squaring oracle. -/
abbrev sq : ℕ →. ℕ := (fun n => n * n : ℕ → ℕ)

/-- The identity oracle. -/
abbrev idO : ℕ →. ℕ := (fun n => n : ℕ → ℕ)

/-- The nowhere-defined oracle. -/
abbrev noneO : ℕ →. ℕ := fun _ => Part.none

-- `(sq ⊕ idO) (2 * 3) = 2 * 9` and `(sq ⊕ idO) (2 * 3 + 1) = 2 * 3 + 1`.
example : (sq ⊕ idO) (2 * 3) = Part.some 18 := by
  rw [Partrec.Join.even]; rfl

example : (sq ⊕ idO) (2 * 3 + 1) = Part.some 7 := by
  rw [Partrec.Join.odd]; rfl

-- A nowhere-defined left half diverges on even inputs but leaves odd inputs defined.
example : ¬((noneO ⊕ idO) (2 * 3)).Dom := by
  rw [Partrec.Join.even]; simp

example : (noneO ⊕ idO) (2 * 3 + 1) = Part.some 7 := by
  rw [Partrec.Join.odd]; rfl

-- Both halves reduce to the join, and the join is below any common upper bound.
example (p x : ℕ →. ℕ) : p ≤ᵀ (p ⊕ x) ∧ x ≤ᵀ (p ⊕ x) := ⟨left_le_join p x, right_le_join p x⟩

example (p x : ℕ →. ℕ) : (p ⊕ x) ≤ᵀ (x ⊕ p) :=
  join_le p x _ (right_le_join x p) (left_le_join x p)

-- The program `oracle`, lifted along `p ≤ᵀ p ⊕ x`, computes `p`; lifted along `x ≤ᵀ p ⊕ x`, it
-- computes `x`. On the same joined oracle the two lifts give different outputs.
example : eval (sq ⊕ idO) (oracle.subst joinLeft) 5 = Part.some 25 := by
  rw [eval_subst_joinLeft]; rfl

example : eval (sq ⊕ idO) (oracle.subst joinRight) 5 = Part.some 5 := by
  rw [eval_subst_joinRight]; rfl

-- The program `joinLeft` relative to `p ⊕ x` runs relative to `sq` once `p` and `x` are given by
-- codes from `sq`: here `p = sq` (the code `oracle`) and `x` is the zero function (code `zero`).
example : eval sq (joinLeft.subst (join oracle zero)) 5 = Part.some 25 := by
  rw [eval_subst_join, eval_joinLeft]; rfl

-- The same translated code under the identity oracle: its output depends on the oracle.
example : eval idO (joinLeft.subst (join oracle zero)) 5 = Part.some 5 := by
  rw [eval_subst_join, eval_joinLeft]; rfl

-- Joining the codes `oracle` and `zero` computes the join relative to every oracle.
example (g : ℕ →. ℕ) (n : ℕ) : eval g (join oracle zero) (2 * n) = (g n).map (2 * ·) := by
  rw [eval_join, Partrec.Join.even]; rfl

-- The translations are primitive recursive on codes.
example : Primrec fun c : Nat.RecursiveIn.Code => c.subst joinLeft :=
  primrec₂_subst.comp Primrec.id (Primrec.const _)

example : Primrec fun c : Nat.RecursiveIn.Code => join c oracle :=
  primrec₂_join.comp Primrec.id (Primrec.const _)

-- The index-level lift along `p ≤ᵀ p ⊕ x` on the index of `oracle`.
example : ∃ t : ℕ → ℕ, Primrec t ∧ ∀ p x : ℕ →. ℕ,
    eval (p ⊕ x) (ofNat Nat.RecursiveIn.Code (t (encode oracle))) = p := by
  obtain ⟨t, ht, hlift⟩ := exists_primrec_joinLeft
  exact ⟨t, ht, fun p x => by rw [hlift, ofNat_encode]; rfl⟩

-- The degree of the join is the supremum, and it is strictly above two incomparable degrees.
example : ∃ d₁ d₂ : TuringDegree, d₁ < d₁ ⊔ d₂ ∧ d₂ < d₁ ⊔ d₂ := by
  obtain ⟨d₁, d₂, h₁, h₂⟩ := TuringDegree.exists_incomparable
  exact ⟨d₁, d₂, lt_of_le_of_ne le_sup_left fun h => h₂ (le_sup_right.trans_eq h.symm),
    lt_of_le_of_ne le_sup_right fun h => h₁ (le_sup_left.trans_eq h.symm)⟩

example (f g : ℕ →. ℕ) :
    toAntisymmetrization TuringReducible f ⊔ toAntisymmetrization TuringReducible g =
      toAntisymmetrization TuringReducible (f ⊕ g) :=
  TuringDegree.sup_def f g

end CslibFrontierTests.RecursiveInJoin
