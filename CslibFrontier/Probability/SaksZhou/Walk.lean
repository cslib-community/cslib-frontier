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
letters moving to `some j` for each `j`, and the remaining letters move to `none`. The supplied
order of the columns and numbering of the alphabet assign consecutive intervals of letters to the
columns (`walkStep_eq_some_iff`).

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

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X] {n b : ℕ}
  (order : Fin n ≃ ι) (letter : X ≃ Fin b)

/-- The letters of an alphabet of size `n ≥ ∑ j, c j`, split into disjoint parts of `c j` letters,
one per `j`, and the remaining letters. -/
private def walkEquiv (order : Fin n ≃ ι) (letter : X ≃ Fin b) (c : ι → ℕ)
    (h : ∑ j, c j ≤ Fintype.card X) :
    X ≃ (Σ j, Fin (c j)) ⊕ Fin (Fintype.card X - ∑ j, c j) :=
  let total := ∑ j, c (order j)
  have hsize : b = total + (Fintype.card X - ∑ j, c j) := by
    have hb := Fintype.card_congr letter
    rw [Fintype.card_fin] at hb
    rw [← hb, show total = ∑ j, c j from order.sum_comp c]
    omega
  letter.trans <| (finCongr hsize).trans <| finSumFinEquiv.symm.trans <|
    (finSigmaFinEquiv.symm.trans (Equiv.sigmaCongrLeft (β := fun j => Fin (c j)) order)).sumCongr
      (Equiv.refl _)

/-- The walk of `A` on letters of `X`: `none` is an absorbing sink; from `some i`, the letters are
numbered by `letter` and allocated to successive columns in `order`. The `⌊A i j |X|⌋₊` letters
assigned to column `j` move to `some j`, and the
remaining letters move to `none` (when the parts do not fit, i.e.
`∑ j ⌊A i j |X|⌋₊ > |X|`, every letter moves to `none`). -/
noncomputable def walkStep (order : Fin n ≃ ι) (letter : X ≃ Fin b) (A : Matrix ι ι ℝ) :
    Option ι → X → Option ι
  | none, _ => none
  | some i, x =>
    if h : ∑ j, ⌊A i j * Fintype.card X⌋₊ ≤ Fintype.card X then
      Sum.elim (fun p => some p.1) (fun _ => none) (walkEquiv order letter _ h x)
    else none

omit [DecidableEq ι] in
/-- In a row whose weights fit, a letter moves to column `order j` exactly when its index lies
between the sum of the preceding column weights and that sum plus the current weight. This lets
an evaluator find the destination by scanning the columns in order. -/
theorem walkStep_eq_some_iff (A : Matrix ι ι ℝ) (i : ι) (j : Fin n) (x : X)
    (hfit : ∑ t, ⌊A i t * Fintype.card X⌋₊ ≤ Fintype.card X) :
    walkStep order letter A (some i) x = some (order j) ↔
      let start := ∑ t : Fin j, ⌊A i (order (Fin.castLE j.isLt.le t)) * Fintype.card X⌋₊
      start ≤ (letter x).val ∧ (letter x).val < start + ⌊A i (order j) * Fintype.card X⌋₊ := by
  let c := fun t => ⌊A i t * Fintype.card X⌋₊
  let e := walkEquiv order letter c hfit
  let start := ∑ t : Fin j, c (order (Fin.castLE j.isLt.le t))
  have index (u : Fin (c (order j))) :
      (letter (e.symm (.inl ⟨order j, u⟩))).val = start + u.val := by
    let relabel := Equiv.sigmaCongrLeft (β := fun t => Fin (c t)) order
    change (letter (e.symm (.inl (relabel ⟨j, u⟩)))).val = _
    have hrel : (Equiv.sigmaCongrLeft (β := fun t => Fin (c t)) order).symm ⟨order j, u⟩ =
        ⟨j, u⟩ := relabel.symm_apply_apply ⟨j, u⟩
    simp [e, walkEquiv, relabel, hrel, finSigmaFinEquiv_apply, start]
  change (walkStep order letter A (some i) x = some (order j)) ↔
    start ≤ (letter x).val ∧ (letter x).val < start + c (order j)
  rw [walkStep, dite_eq_left hfit]
  change Sum.elim (fun p => some p.1) (fun _ => none) (e x) = some (order j) ↔ _
  constructor
  · intro hx
    rcases he : e x with ⟨t, u⟩ | v
    · rw [he] at hx
      obtain rfl : t = order j := Option.some.inj hx
      have := index u
      rw [← he, e.symm_apply_apply] at this
      have := u.isLt
      omega
    · simp [he] at hx
  · rintro ⟨hstart, hend⟩
    let u : Fin (c (order j)) := ⟨(letter x).val - start, by omega⟩
    have hidx := index u
    have hx : e.symm (.inl ⟨order j, u⟩) = x :=
      letter.injective (Fin.ext <| hidx.trans (Nat.add_sub_of_le hstart))
    rw [← hx, e.apply_symm_apply]
    rfl

omit [DecidableEq ι] in
@[simp] theorem walkStep_none (A : Matrix ι ι ℝ) (x : X) :
    walkStep order letter A none x = none := by
  rw [walkStep]

omit [DecidableEq ι] in
private theorem foldl_walkStep_none (A : Matrix ι ι ℝ) (l : List X) :
    l.foldl (walkStep order letter A) none = none := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.foldl_cons, walkStep_none order letter, ih]

/-- The number of letters moving `some i` to `some j` is `A i j |X|`. -/
private theorem card_walkStep_eq {A : Matrix ι ι ℝ} (h0 : ∀ i j, 0 ≤ A i j)
    (h1 : ∀ i, ∑ j, A i j ≤ 1) (hA : ∀ i j, ∃ c : ℕ, A i j * Fintype.card X = c) (i j : ι) :
    (#{x : X | walkStep order letter A (some i) x = some j} : ℝ) = A i j * Fintype.card X := by
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
  have hcount : #{x : X | walkStep order letter A (some i) x = some j} =
      ⌊A i j * Fintype.card X⌋₊ := by
    rw [Finset.card_filter, ← (walkEquiv order letter _ hfit).symm.sum_comp]
    simp only [walkStep, hfit, ↓reduceDIte, Equiv.apply_symm_apply]
    rw [Fintype.sum_sum_type, Fintype.sum_sigma,
      Finset.sum_eq_single_of_mem j (Finset.mem_univ j) fun l _ hl => by simp [hl]]
    simp
  rw [hcount, hc, Nat.floor_natCast]

/-- One uniform letter moves `some i` to `some j` with probability `A i j`. -/
theorem dens_walkStep_eq [Nonempty X] {A : Matrix ι ι ℝ} (h0 : ∀ i j, 0 ≤ A i j)
    (h1 : ∀ i, ∑ j, A i j ≤ 1) (hA : ∀ i j, ∃ c : ℕ, A i j * Fintype.card X = c) (i j : ι) :
    (dens {x : X | walkStep order letter A (some i) x = some j} : ℝ) = A i j := by
  have hX : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [Finset.dens, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast,
    card_walkStep_eq order letter h0 h1 hA, mul_div_cancel_right₀ _ hX]

/-- Splitting off the first letter: the number of words of length `m + 1` moving `s` to `t` sums,
over the state `s'` reached by the first letter, the letters reaching `s'` times the words of
length `m` moving `s'` to `t`. -/
private theorem card_foldl_walkStep_succ (A : Matrix ι ι ℝ) (s t : Option ι) (m : ℕ) :
    #{u : Fin (m + 1) → X | (List.ofFn u).foldl (walkStep order letter A) s = t} =
      ∑ s' : Option ι, #{x : X | walkStep order letter A s x = s'} *
        #{u : Fin m → X | (List.ofFn u).foldl (walkStep order letter A) s' = t} := by
  have key (x : X) (u : Fin m → X) :
      (List.ofFn (Fin.consEquiv (fun _ => X) (x, u))).foldl (walkStep order letter A) s =
        (List.ofFn u).foldl (walkStep order letter A) (walkStep order letter A s x) := by
    rw [Fin.consEquiv_apply, List.ofFn_succ, List.foldl_cons, Fin.cons_zero]
    simp only [Fin.cons_succ]
  rw [Finset.card_filter, ← (Fin.consEquiv fun _ => X).sum_comp, Fintype.sum_prod_type]
  simp only [key, ← Finset.card_filter]
  refine (Finset.sum_fiberwise' Finset.univ (walkStep order letter A s) fun s' =>
    #{u : Fin m → X | (List.ofFn u).foldl (walkStep order letter A) s' = t}).symm.trans ?_
  simp only [Finset.sum_const, smul_eq_mul]

/-- The number of words of length `m` moving `some i` to `some j` is `(A ^ m) i j |X| ^ m`. -/
private theorem card_foldl_walkStep_eq {A : Matrix ι ι ℝ} (h0 : ∀ i j, 0 ≤ A i j)
    (h1 : ∀ i, ∑ j, A i j ≤ 1) (hA : ∀ i j, ∃ c : ℕ, A i j * Fintype.card X = c) (m : ℕ)
    (i j : ι) :
    (#{u : Fin m → X | (List.ofFn u).foldl (walkStep order letter A) (some i) = some j} : ℝ) =
      (A ^ m) i j * (Fintype.card X : ℝ) ^ m := by
  induction m generalizing i with
  | zero => simp [Matrix.one_apply, eq_comm, apply_ite]
  | succ m ih =>
    have hnone : #{u : Fin m → X | (List.ofFn u).foldl (walkStep order letter A) none = some j} =
        0 := by
      simp [foldl_walkStep_none order letter]
    rw [card_foldl_walkStep_succ order letter, Nat.cast_sum, Fintype.sum_option, hnone, mul_zero,
      Nat.cast_zero, zero_add, pow_succ' A m, Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Nat.cast_mul, card_walkStep_eq order letter h0 h1 hA, ih]
    ring

/-- **The walk realizes the matrix powers**: `m` uniform letters move `some i` to `some j` with
probability `(A ^ m) i j`. -/
theorem dens_foldl_walkStep_eq [Nonempty X] {A : Matrix ι ι ℝ} (h0 : ∀ i j, 0 ≤ A i j)
    (h1 : ∀ i, ∑ j, A i j ≤ 1) (hA : ∀ i j, ∃ c : ℕ, A i j * Fintype.card X = c) (m : ℕ)
    (i j : ι) :
    (dens {u : Fin m → X | (List.ofFn u).foldl (walkStep order letter A) (some i) = some j} : ℝ) =
      (A ^ m) i j := by
  have hX : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [Finset.dens, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast,
    card_foldl_walkStep_eq order letter h0 h1 hA, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    mul_div_cancel_right₀ _ (pow_ne_zero m hX)]

end Cslib.Probability.SaksZhou
