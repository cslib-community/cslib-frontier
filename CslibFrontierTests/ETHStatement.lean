/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.FineGrained.CountingNativeEndpoint

/-!
# Statement pin for the refutations of ETH and SETH

`Cslib.Complexity.CountingNativeEndpoint.not_ETH : ¬ETH` and `not_SETH : ¬SETH` are only as
strong as the definitions of `Cslib.Complexity.ETH` and `Cslib.Complexity.SETH`. This file restates
what the two theorems say with those definitions unfolded, and proves each restatement from the
library theorem. The checks are definitional: `ETH` and `SETH` equal their restatements by
`Iff.rfl`. A change to `ETH`, `SETH`, `DecidableInExpTime`, `DecidableInTimeO`, `ThreeSAT`, `KSAT`,
`CNF.numVars`, `CNF.Satisfiable` or `encCNF` therefore makes this file fail to compile unless the
new definition unfolds to the same statement, so the meaning of the two theorems cannot change
unnoticed. The file is a strict `module` with plain imports, so it also fails when one of these
definitions stops being exposed.

The restatement uses two notions from outside this file:

* `Turing.MultiTapeTM.DecidableInTimeAndSpace` of the pinned cslib, the machine model, which is
  taken as given and not unfolded;
* `Cslib.Complexity.encCNF`, the binary encoding of formulas, which is pinned below by its
  definition from the generic encoders and by its value on small formulas.

The rest (`Formula`, `numVars`, `Satisfiable`, `DecidableAtRate`) is defined here from core Lean
and Mathlib only.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.ETHStatement

open Turing.MultiTapeTM
open Cslib.Complexity (encCNF)

/-- Formulas in conjunctive normal form: a list of clauses, each a list of literals `(v, b)`, where
`(v, true)` is the variable `v` and `(v, false)` is its negation. -/
private abbrev Formula : Type := List (List (ℕ × Bool))

/-- The number of distinct variables occurring in a formula. -/
private def numVars (φ : Formula) : ℕ := (φ.flatten.map Prod.fst).toFinset.card

/-- Some assignment makes a literal true in every clause. -/
private def Satisfiable (φ : Formula) : Prop :=
  ∃ σ : ℕ → Bool, (φ.all fun clause => clause.any fun l => σ l.1 == l.2) = true

/-- Satisfiability of formulas with at most `k` literals per clause is decidable within time
`c * (2 ^ (r * n) * (L + 1) ^ e) + c` for some naturals `e` and `c`, on formulas with `n` variables
and encoding of length `L`, by a multi-tape machine reading the encoded formula. -/
private def DecidableAtRate (k : ℕ) (r : ℝ) : Prop :=
  ∃ (e c : ℕ) (t s : Formula → ℕ),
    (∀ φ, (t φ : ℝ) ≤ c * (2 ^ (r * numVars φ) * ((encCNF φ).length + 1) ^ e) + c) ∧
    DecidableInTimeAndSpace {φ : Formula | (∀ clause ∈ φ, clause.length ≤ k) ∧ Satisfiable φ}
      encCNF t s

/-! ### The hypotheses are their restatements, definitionally -/

example : Cslib.Complexity.ETH ↔ ∃ δ : ℝ, 0 < δ ∧ ¬DecidableAtRate 3 δ := Iff.rfl

example : Cslib.Complexity.SETH ↔ ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ¬DecidableAtRate k (1 - ε) := Iff.rfl

/-! ### The two theorems, unfolded -/

/-- `¬ETH`, unfolded: for every `δ > 0`, 3SAT is decidable within time `2 ^ (δ * n)` times a
polynomial in the length of the encoded formula. -/
private theorem decidableAtRate_three (δ : ℝ) (hδ : 0 < δ) : DecidableAtRate 3 δ :=
  of_not_not fun h => Cslib.Complexity.CountingNativeEndpoint.not_ETH ⟨δ, hδ, h⟩

/-- `¬SETH`, unfolded: for some `ε > 0` and every width `k`, `k`-SAT is decidable within time
`2 ^ ((1 - ε) * n)` times a polynomial in the length of the encoded formula. -/
private theorem exists_forall_decidableAtRate :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ, DecidableAtRate k (1 - ε) :=
  of_not_not fun h => Cslib.Complexity.CountingNativeEndpoint.not_SETH fun ε hε =>
    of_not_not fun hk => h ⟨ε, hε, fun k => of_not_not fun hd => hk ⟨k, hd⟩⟩

/-! ### The parameter and the encoding on small formulas -/

-- Variables are counted once each, whatever their labels, signs and repetitions.
example : numVars [] = 0 := by decide
example : numVars [[]] = 0 := by decide
example : numVars [[(100, true), (100, false)], [(7, true)]] = 2 := by decide
example (φ : Formula) : numVars φ = Cslib.Logic.PL.CNF.numVars φ := rfl

-- The empty formula is satisfiable; a formula with an empty clause is not.
example : Satisfiable [] := ⟨fun _ => false, rfl⟩
example : ¬Satisfiable [[]] := fun ⟨_, h⟩ => Bool.false_ne_true h
example : Satisfiable [[(0, true), (1, false)], [(0, false)]] := ⟨fun _ => false, by decide⟩
example : ¬Satisfiable [[(0, true)], [(0, false)]] := by
  rintro ⟨σ, h⟩
  cases hσ : σ 0 <;> simp [hσ] at h

-- The encoding is the generic list encoding of clauses, each the list encoding of its literals
-- `(v, b)`, encoded as the framed binary digits of `v` followed by the bit `b`.
example : encCNF = encList (encList (encPair encNat encBool)) := rfl
example : encCNF [] = [] := by decide
example : encCNF [[]] = [false] := by decide
example : encCNF [[(0, false)]] =
    [true, true, true, false, true, true, true, false, true, false, false] := by decide
example : (encCNF [[(2, true)]]).length = 27 := by decide
example : (encCNF [[(0, false)], []]).length = 12 := by decide

end CslibFrontierTests.ETHStatement
