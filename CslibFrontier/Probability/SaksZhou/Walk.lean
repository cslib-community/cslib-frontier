/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Floor.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Matrix.Mul
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Walks realizing substochastic matrices

A substochastic matrix `A` over states `ι` whose entries are multiples of `1 / |X|`, for a finite
alphabet `X`, is the transition matrix of a deterministic walk driven by uniformly random letters
of `X`. The walk lives on `Option ι`, where `none` is an absorbing sink collecting the missing
mass of each row. From state `some i`, the letters are split into disjoint parts, `A i j |X|`
letters moving to `some j` for each `j`, and the remaining letters move to `none`.

Reading `m` uniform letters then moves `some i` to `some j` with probability `(A ^ m) i j`
(`dens_foldl_walkStep_eq`). This is how a matrix produced by rounding, such as the dyadic
substochastic matrices of the Saks–Zhou rounding operator, is turned back into a read-once
branching program over random letters.

## Main definitions

* `Cslib.Probability.SaksZhou.walkStep`: one step of the walk of a matrix on a letter.

## Main results

* `Cslib.Probability.SaksZhou.dens_walkStep_eq`: one uniform letter moves `some i` to `some j`
  with probability `A i j`.
* `Cslib.Probability.SaksZhou.dens_foldl_walkStep_eq`: `m` uniform letters move `some i` to
  `some j` with probability `(A ^ m) i j`.
-/

public section

namespace Cslib.Probability.SaksZhou

open Finset

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]

/-- The letters of an alphabet of size `n ≥ ∑ j, c j`, split into disjoint parts of `c j` letters,
one per `j`, and the remaining letters. -/
private noncomputable def walkEquiv (c : ι → ℕ) (h : ∑ j, c j ≤ Fintype.card X) :
    X ≃ (Σ j, Fin (c j)) ⊕ Fin (Fintype.card X - ∑ j, c j) :=
  Fintype.equivOfCardEq <| by
    rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
    simp only [Fintype.card_fin]
    omega

/-- The walk of `A` on letters of `X`: `none` is an absorbing sink; from `some i`, the letters are
split into disjoint parts of `⌊A i j |X|⌋₊` letters, one per `j`, moving to `some j`, and the
remaining letters move to `none` (when the parts do not fit, i.e.
`∑ j ⌊A i j |X|⌋₊ > |X|`, every letter moves to `none`). -/
noncomputable def walkStep (A : Matrix ι ι ℝ) : Option ι → X → Option ι
  | none, _ => none
  | some i, x =>
    if h : ∑ j, ⌊A i j * Fintype.card X⌋₊ ≤ Fintype.card X then
      Sum.elim (fun p => some p.1) (fun _ => none) (walkEquiv _ h x)
    else none

omit [DecidableEq ι] in
@[simp] theorem walkStep_none (A : Matrix ι ι ℝ) (x : X) : walkStep A none x = none := by
  rw [walkStep]

omit [DecidableEq ι] in
private theorem foldl_walkStep_none (A : Matrix ι ι ℝ) (l : List X) :
    l.foldl (walkStep A) none = none := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.foldl_cons, walkStep_none, ih]

/-- The number of letters moving `some i` to `some j` is `A i j |X|`. -/
private theorem card_walkStep_eq {A : Matrix ι ι ℝ} (h0 : ∀ i j, 0 ≤ A i j)
    (h1 : ∀ i, ∑ j, A i j ≤ 1) (hA : ∀ i j, ∃ c : ℕ, A i j * Fintype.card X = c) (i j : ι) :
    (#{x : X | walkStep A (some i) x = some j} : ℝ) = A i j * Fintype.card X := by
  have hfit : ∑ j, ⌊A i j * Fintype.card X⌋₊ ≤ Fintype.card X := by
    have hle : ((∑ j, ⌊A i j * Fintype.card X⌋₊ : ℕ) : ℝ) ≤ Fintype.card X :=
      calc ((∑ j, ⌊A i j * Fintype.card X⌋₊ : ℕ) : ℝ)
          ≤ ∑ j, A i j * Fintype.card X := by
            push_cast
            exact Finset.sum_le_sum fun j _ =>
              Nat.floor_le (mul_nonneg (h0 i j) (Nat.cast_nonneg _))
        _ = (∑ j, A i j) * Fintype.card X := by rw [Finset.sum_mul]
        _ ≤ 1 * Fintype.card X := by gcongr; exact h1 i
        _ = Fintype.card X := one_mul _
    exact_mod_cast hle
  obtain ⟨c, hc⟩ := hA i j
  have hcount : #{x : X | walkStep A (some i) x = some j} = ⌊A i j * Fintype.card X⌋₊ := by
    rw [Finset.card_filter, ← (walkEquiv _ hfit).symm.sum_comp]
    simp only [walkStep, hfit, ↓reduceDIte, Equiv.apply_symm_apply]
    rw [Fintype.sum_sum_type, Fintype.sum_sigma,
      Finset.sum_eq_single_of_mem j (Finset.mem_univ j) fun l _ hl => by simp [hl]]
    simp
  rw [hcount, hc, Nat.floor_natCast]

/-- One uniform letter moves `some i` to `some j` with probability `A i j`. -/
theorem dens_walkStep_eq [Nonempty X] {A : Matrix ι ι ℝ} (h0 : ∀ i j, 0 ≤ A i j)
    (h1 : ∀ i, ∑ j, A i j ≤ 1) (hA : ∀ i j, ∃ c : ℕ, A i j * Fintype.card X = c) (i j : ι) :
    (dens {x : X | walkStep A (some i) x = some j} : ℝ) = A i j := by
  have hX : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [Finset.dens, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast,
    card_walkStep_eq h0 h1 hA, mul_div_cancel_right₀ _ hX]

/-- Splitting off the first letter: the number of words of length `m + 1` moving `s` to `t` sums,
over the state `s'` reached by the first letter, the letters reaching `s'` times the words of
length `m` moving `s'` to `t`. -/
private theorem card_foldl_walkStep_succ (A : Matrix ι ι ℝ) (s t : Option ι) (m : ℕ) :
    #{u : Fin (m + 1) → X | (List.ofFn u).foldl (walkStep A) s = t} =
      ∑ s' : Option ι, #{x : X | walkStep A s x = s'} *
        #{u : Fin m → X | (List.ofFn u).foldl (walkStep A) s' = t} := by
  have key (x : X) (u : Fin m → X) :
      (List.ofFn (Fin.consEquiv (fun _ => X) (x, u))).foldl (walkStep A) s =
        (List.ofFn u).foldl (walkStep A) (walkStep A s x) := by
    rw [Fin.consEquiv_apply, List.ofFn_succ, List.foldl_cons, Fin.cons_zero]
    simp only [Fin.cons_succ]
  rw [Finset.card_filter, ← (Fin.consEquiv fun _ => X).sum_comp, Fintype.sum_prod_type]
  simp only [key, ← Finset.card_filter]
  refine (Finset.sum_fiberwise' Finset.univ (walkStep A s) fun s' =>
    #{u : Fin m → X | (List.ofFn u).foldl (walkStep A) s' = t}).symm.trans ?_
  simp only [Finset.sum_const, smul_eq_mul]

/-- The number of words of length `m` moving `some i` to `some j` is `(A ^ m) i j |X| ^ m`. -/
private theorem card_foldl_walkStep_eq {A : Matrix ι ι ℝ} (h0 : ∀ i j, 0 ≤ A i j)
    (h1 : ∀ i, ∑ j, A i j ≤ 1) (hA : ∀ i j, ∃ c : ℕ, A i j * Fintype.card X = c) (m : ℕ)
    (i j : ι) :
    (#{u : Fin m → X | (List.ofFn u).foldl (walkStep A) (some i) = some j} : ℝ) =
      (A ^ m) i j * (Fintype.card X : ℝ) ^ m := by
  induction m generalizing i with
  | zero =>
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Matrix.one_apply_ne hij]
  | succ m ih =>
    have hnone : #{u : Fin m → X | (List.ofFn u).foldl (walkStep A) none = some j} = 0 := by
      simp [foldl_walkStep_none]
    rw [card_foldl_walkStep_succ, Nat.cast_sum, Fintype.sum_option, hnone, mul_zero,
      Nat.cast_zero, zero_add, pow_succ' A m, Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Nat.cast_mul, card_walkStep_eq h0 h1 hA, ih]
    ring

/-- **The walk realizes the matrix powers**: `m` uniform letters move `some i` to `some j` with
probability `(A ^ m) i j`. -/
theorem dens_foldl_walkStep_eq [Nonempty X] {A : Matrix ι ι ℝ} (h0 : ∀ i j, 0 ≤ A i j)
    (h1 : ∀ i, ∑ j, A i j ≤ 1) (hA : ∀ i j, ∃ c : ℕ, A i j * Fintype.card X = c) (m : ℕ)
    (i j : ι) :
    (dens {u : Fin m → X | (List.ofFn u).foldl (walkStep A) (some i) = some j} : ℝ) =
      (A ^ m) i j := by
  have hX : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [Finset.dens, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast,
    card_foldl_walkStep_eq h0 h1 hA, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    mul_div_cancel_right₀ _ (pow_ne_zero m hX)]

end Cslib.Probability.SaksZhou
