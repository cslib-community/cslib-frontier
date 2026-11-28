/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.ComputedWithin
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.WordCode
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Naming the letters of a code by other letters

A polynomial on the codes of words over `Γ` has a variable `(p, y)` for every place `p` and every
letter or end mark `y : Option Γ`. Along a map `e : Δ → Γ`, the substitution
`Tape.letterSubst K e N` sends the variables of the letters outside the range of `e` to `0`
(`Tape.letterSubst_of_notMem_range`) and, for an injective `e`, the variable `(p, Option.map e y)`
to `(p, y)` (`Tape.letterSubst_map`). Its values are affine (`Tape.isAffine_letterSubst`). For an
injective `e`, a polynomial after the substitution takes at the code of a word `w` over `Δ` the
value that it takes before at the code of `w.map e` (`Tape.eval_aeval_letterSubst`).

## Main definitions

* `Tape.letterSubst`: the substitution that names the letters of `Γ` by letters of `Δ`.

## Main results

* `Tape.isAffine_letterSubst`: its values are affine.
* `Tape.eval_aeval_letterSubst`: evaluation at the code of a word after the substitution.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Section K.2, p. 56 (the indicator assignment of a word `w`, here
  `fun b => if wordCode N w b then 1 else 0`) and proof of Lemma K.3, p. 57 (the variables of the
  symbols other than the two of the words of instances are set to `0`); modules `Nc.End.Thm`
  (`letS`) and `Nc.End.PermThm`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Tape

open MvPolynomial

variable {K : Type*} [CommSemiring K] {Γ Δ : Type} {e : Δ → Γ} {N : ℕ}

variable (K) in
/-- The substitution that names the letters of `Γ` by letters of `Δ` along `e : Δ → Γ`: the
variable `(p, y)` becomes `(p, y')` for some `y'` with `Option.map e y' = y` (the only one when `e`
is injective; `y' = none` for the end mark `y = none`), and `0` when there is no such `y'`. -/
noncomputable def letterSubst (e : Δ → Γ) (N : ℕ) :
    Fin N × Option Γ → MvPolynomial (Fin N × Option Δ) K
  | (p, y) => (Function.partialInv (Option.map e) y).elim 0 fun y' => X (p, y')

/-- For an injective `e`, the variable `(p, Option.map e y)` becomes `(p, y)`. -/
theorem letterSubst_map (he : Function.Injective e) (p : Fin N) (y : Option Δ) :
    letterSubst K e N (p, y.map e) = X (p, y) := by
  rw [letterSubst, Function.partialInv_left (Option.map_injective he), Option.elim_some]

/-- The variables of the letters outside the range of `e` become `0`. -/
theorem letterSubst_of_notMem_range {y : Option Γ} (hy : y ∉ Set.range (Option.map e))
    (p : Fin N) : letterSubst K e N (p, y) = 0 := by
  have hy : ¬∃ y', Option.map e y' = y := hy
  simp [letterSubst, Function.partialInv, hy]

/-- The values of `letterSubst` are affine: variables or `0`. -/
theorem isAffine_letterSubst (e : Δ → Γ) (N : ℕ) (b : Fin N × Option Γ) :
    IsAffine (letterSubst K e N b) := by
  rcases h : Function.partialInv (Option.map e) b.2 with _ | y'
  · exact .inl ⟨0, by simp [letterSubst, h]⟩
  · exact .inr ⟨(b.1, y'), 1, 0, by simp [letterSubst, h]⟩

variable [DecidableEq Γ] [DecidableEq Δ]

/-- The code of `w.map e` sets `(p, y)` when the code of `w` sets `(p, y')` with
`Option.map e y' = y`. -/
private theorem wordCode_map_iff (w : List Δ) (p : Fin N) (y : Option Γ) :
    wordCode N (w.map e) (p, y) = true ↔
      ∃ y', wordCode N w (p, y') = true ∧ Option.map e y' = y := by
  have hl : (w.map e).map some ++ [none] = (w.map some ++ [none]).map (Option.map e) := by simp
  simp only [wordCode, decide_eq_true_eq]
  rw [hl, List.getElem?_map, Option.map_eq_some_iff]

/-- Evaluating one value of `letterSubst` at the code of `w`. -/
private theorem eval_letterSubst (he : Function.Injective e) (w : List Δ) (b : Fin N × Option Γ) :
    eval (fun b => if wordCode N w b then (1 : K) else 0) (letterSubst K e N b) =
      if wordCode N (w.map e) b then 1 else 0 := by
  obtain ⟨p, y⟩ := b
  by_cases hy : y ∈ Set.range (Option.map e)
  · obtain ⟨y, rfl⟩ := hy
    rw [letterSubst_map he, eval_X]
    congr 1
    rw [Bool.eq_iff_iff, wordCode_map_iff]
    simp [(Option.map_injective he).eq_iff]
  · rw [letterSubst_of_notMem_range hy, map_zero, ite_eq_right]
    simpa only [wordCode_map_iff, not_exists, not_and] using fun y' _ h => hy ⟨y', h⟩

/-- **Evaluation at a code after naming the letters.** For an injective `e : Δ → Γ`, a polynomial
after the substitution `letterSubst K e N` takes at the code of a word `w` over `Δ` the value
that it takes at the code of the word `w.map e` over `Γ`. -/
theorem eval_aeval_letterSubst (he : Function.Injective e) (w : List Δ)
    (P : MvPolynomial (Fin N × Option Γ) K) :
    eval (fun b => if wordCode N w b then 1 else 0) (aeval (letterSubst K e N) P) =
      eval (fun b => if wordCode N (w.map e) b then 1 else 0) P := by
  rw [map_aeval]
  exact eval₂Hom_congr (by ext; simp) (funext (eval_letterSubst he w)) rfl

end Cslib.Circuits.Arithmetic.Separation.Tape
