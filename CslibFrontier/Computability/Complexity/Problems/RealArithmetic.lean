/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.RealArithmetic.FormulaWordValidation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair

/-!
# Existential and existential–universal real truth problems

These are the binary languages in `edemaine/lean-canny`'s formal abstract at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. The input is an integer-polynomial Boolean
formula encoded by a flat constructor stream, with binary integer magnitudes and unary
variable indices. The two-block language prefixes the formula word with a framed unary
existential-block length. Neither problem promises well-formedness: only words in the image
of a true sentence are accepted. The encoding-membership criteria below show that these words
have their intended semantics
even when the same word represents a formula in several dimensions. No complexity bound is
claimed in this module.

## Main definitions

* `Cslib.Complexity.ETR`: satisfiable existential real formulas.
* `Cslib.Complexity.ExistsForallTheory`: true existential–universal real sentences.

## Main results

* `Cslib.Complexity.encFormula_mem_ETR`: encoding preserves existential truth.
* `Cslib.Complexity.encFormula_mem_ExistsForallTheory`: encoding preserves two-block truth.
-/

public section
namespace Cslib.Complexity

open Logic.RealArithmetic Turing.MultiTapeTM

/-- Encodings of satisfiable integer-polynomial formulas, in any finite dimension. -/
@[expose] def ETR : Set (List Bool) :=
  ⋃ n, {p : Formula n | p.solutionSet.Nonempty}.image (encFormula n)

/-- True existential–universal real sentences. The unary existential-block length is framed
before the formula word. Existential variables precede universal variables; either block may
be empty. Noncanonical and malformed words are rejected. -/
@[expose] def ExistsForallTheory : Set (List Bool) :=
  ⋃ r, ⋃ s, {p : Formula (r + s) | p.existsForallSolutionSet.Nonempty}.image (fun p =>
    encPair encUnary encBits (r, encFormula (r + s) p))

/-- An encoded formula belongs to ETR exactly when its real solution set is nonempty.
Omitting the ambient dimension from the word does not change satisfiability. -/
@[simp] theorem encFormula_mem_ETR {n : ℕ} (p : Formula n) :
    encFormula n p ∈ ETR ↔ p.solutionSet.Nonempty := by
  refine ⟨fun hp => ?_, fun hp => Set.mem_iUnion.mpr ⟨n, Set.mem_image_of_mem _ hp⟩⟩
  obtain ⟨m, q, hq, heq⟩ := Set.mem_iUnion.mp hp
  let f := Fin.castLE (Nat.le_max_left n m)
  let g := Fin.castLE (Nat.le_max_right n m)
  have hpq : p.rename f = q.rename g := (encFormula (max n m)).injective <| by
    rw [encFormula_rename f (fun _ => rfl), encFormula_rename g (fun _ => rfl), heq]
  rwa [← Formula.solutionSet_nonempty_rename (Fin.castLE_injective (Nat.le_max_left n m)) p,
    hpq, Formula.solutionSet_nonempty_rename (Fin.castLE_injective (Nat.le_max_right n m)) q]

/-- ETR membership agrees with satisfiability of the total formula view, on every bit word.
In particular the view rejects malformed inputs by assigning them an empty solution set. -/
theorem mem_ETR_iff_ofWord (word : List Bool) :
    word ∈ ETR ↔ (Formula.ofWord word).solutionSet.Nonempty := by
  by_cases h : validFormulaWord word = true
  · have heq : encFormula word.length (Formula.ofWord word) = word := by
      rw [encFormula_ofWord, normalizeFormulaWord, ite_eq_left h]
    simpa only [heq] using encFormula_mem_ETR (Formula.ofWord word)
  · rw [Formula.ofWord_of_not_valid h, Formula.solutionSet]
    simp [show word ∉ ETR from fun hw =>
      let ⟨n, p, _, hp⟩ := Set.mem_iUnion.mp hw
      h (hp ▸ validFormulaWord_encFormula (n := n) p)]

/-- The two-block encoding has exactly the advertised truth condition, including when a
representing formula has extra unused universal coordinates. -/
theorem encFormula_mem_ExistsForallTheory {r s : ℕ} (p : Formula (r + s)) :
    encPair encUnary encBits (r, encFormula (r + s) p) ∈ ExistsForallTheory ↔
      p.existsForallSolutionSet.Nonempty := by
  refine ⟨fun hp => ?_, fun hp => Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr
    ⟨s, Set.mem_image_of_mem (fun q => encPair encUnary encBits (r, encFormula (r + s) q)) hp⟩⟩⟩
  obtain ⟨r', hp⟩ := Set.mem_iUnion.mp hp
  obtain ⟨t, q, hq, heq⟩ := Set.mem_iUnion.mp hp
  obtain ⟨rfl, hword⟩ := Prod.mk.inj ((encPair encUnary encBits).injective heq.symm)
  let f := Fin.castLE (Nat.add_le_add_left (Nat.le_max_left s t) r)
  let g := Fin.castLE (Nat.add_le_add_left (Nat.le_max_right s t) r)
  have hpq : p.rename f = q.rename g := (encFormula (r + max s t)).injective <| by
    rw [encFormula_rename f (fun _ => rfl), encFormula_rename g (fun _ => rfl), hword]
  rwa [← Formula.existsForallSolutionSet_rename_castLE (Nat.le_max_left s t) p, hpq,
    Formula.existsForallSolutionSet_rename_castLE (Nat.le_max_right s t) q]

end Cslib.Complexity
