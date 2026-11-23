/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Minimax.Value
public import Mathlib.Data.Matrix.Block
import CslibFrontier.Foundations.LinearAlgebra.Matrix.BasicSolution
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Linear programs as symmetric zero-sum games

A zero-sum game with skew-symmetric payoff matrix `P` (`Pᵀ = -P`) is *symmetric*, and a
*solution* of it is a mixed strategy `z` with `0 ≤ P *ᵥ z` ([Adler2013], (3)): played against `z`
the opponent's every pure strategy pays at least `0`, the value of the game. By the minimax
theorem every symmetric game has a solution (`exists_isSymmetricGameSolution`, [Adler2013],
Theorem 1). This file formalizes the converse of the reduction of games to linear programs:
the reduction of linear programs to symmetric games of [Dantzig1951], and the repair by
[Adler2013] of the case in which that reduction fails.

## Dantzig's game and its gap

For the linear program `min {c ⬝ᵥ x | b ≤ A *ᵥ x, 0 ≤ x}` and its dual
`max {y ⬝ᵥ b | y ᵥ* A ≤ c, 0 ≤ y}` ([Adler2013], (1)–(2)), the *Dantzig game*
(`dantzigGame A b c`) has the skew-symmetric payoff matrix

```
    ( 0   A  -b)
P = (-Aᵀ  0   c)
    ( bᵀ -cᵀ  0)
```

([Adler2013], (4)). A solution `(y, x, t)` satisfies `t • b ≤ A *ᵥ x`, `y ᵥ* A ≤ t • c` and
`c ⬝ᵥ x ≤ y ⬝ᵥ b` (`isSymmetricGameSolution_dantzigGame_iff`, [Adler2013], (5)), and Dantzig
reads the linear program off it ([Adler2013], Theorem 2):

* `IsSymmetricGameSolution.optimal_of_dantzigGame` (Theorem 2(b)): if `0 < t`, then `x / t` and
  `y / t` are optimal solutions of the primal and the dual;
* `IsSymmetricGameSolution.not_feasible_of_dantzigGame` (Theorem 2(c)): if
  `c ⬝ᵥ x < y ⬝ᵥ b`, then the primal or the dual is infeasible;
* the step `IsSymmetricGameSolution.mul_sub_eq_zero_of_dantzigGame`, after Theorem 2(a):
  `t * (y ⬝ᵥ b - c ⬝ᵥ x) = 0`.

The reduction is incomplete: a solution may have `t = 0` and `c ⬝ᵥ x = y ⬝ᵥ b`, and then it says
nothing about the program ([Adler2013], p. 166, citing [Dantzig1951]). The original example
`exists_dantzigGame_undetermined` exhibits the gap: one strategy with `t = 0` and
`c ⬝ᵥ x = y ⬝ᵥ b` solves the Dantzig games of two programs, one of which has an optimal solution
and the other of which is infeasible. Repairing the reduction for linear programs themselves,
through the feasibility problem below, remains open.

## Adler's repair

[Adler2013] works with the *linear feasibility problem* `F(A, b)`: find `x` with `0 ≤ x` and
`A *ᵥ x = b`, or show that there is none. A pair of dual programs is one feasibility problem
(the primal and dual constraints together with `c ⬝ᵥ x ≤ y ⬝ᵥ b`; [Adler2013], p. 167), a step
not formalized here. Writing
`A *ᵥ x = b` as `b ≤ A *ᵥ x` and `∑ i, (A *ᵥ x) i ≤ ∑ i, b i`, the Dantzig game of the program
`min {u | b ≤ A *ᵥ x + u • 1, ∑ i, (A *ᵥ x) i - u ≤ ∑ i, b i, 0 ≤ x, 0 ≤ u}` is the *Dantzig
game associated with `F(A, b)`* (`feasibilityGame A b`; its solutions are [Adler2013], (6a)–(6g)).
Its solutions `(y, v, x, u, t)` resolve `F(A, b)` unless `t = 0`. Three steps of the reduction
below, after [Adler2013], Proposition 4, say so:

* `IsSymmetricGameSolution.mulVec_eq_of_feasibilityGame`: if `0 < t` and `u = 0`, then
  `x / t` solves `F(A, b)`;
* `IsSymmetricGameSolution.not_exists_of_feasibilityGame`: if `0 < u`, then `F(A, b)` has no
  solution, certified by `y - v • 1`;
* `IsSymmetricGameSolution.mulVec_eq_zero_of_feasibilityGame`: if `t = 0`, then `x` is a nonzero
  solution of `A *ᵥ x = 0`, `0 ≤ x`, which exists whether or not `F(A, b)` is solvable.

Adding the variable `s` and the constraint `∑ j, x j + s = β` makes the solution set bounded, so
the Dantzig game of the bounded problem `F(Â, b̂(β))` has no solution with `t = 0`
(`IsSymmetricGameSolution.pos_of_feasibilityGame_bounded`, [Adler2013], Proposition 6); and for
`β` at least the total weight of some solution of `F(A, b)`, the two problems are solvable
together ([Adler2013], Proposition 7). For integer data with entries of absolute value at most
`B`, the bound `card n * ((card n)! * (card m * B ^ 2 + 1) ^ card n)` from Cramer's rule
(`Matrix.exists_int_nonneg_mulVec_eq`) is such a `β`, and every solution of the bounded game
resolves `F(A, b)` (`resolves_of_feasibilityGame_bounded`). This is the
Karp-type reduction of [Adler2013], Section 3.1, with the Leibniz bound on determinants in place
of Adler's Hadamard bound `m (√m θ) ^ m + 1`.

So every linear feasibility problem with integer data over a linearly ordered field is solved by
solving one symmetric zero-sum game with `card m + card n + 5` pure strategies, built from the
data alone. Here the minimax theorem is itself proved from linear-programming duality
(`exists_isMinimaxValue`), so these results do not give a second proof of duality: their content
is the reduction, that the status of the problem is read off any solution of the game.

## Main definitions

* `Cslib.Probability.IsSymmetricGameSolution`: `z` solves the symmetric game with payoff `P`.
* `Cslib.Probability.dantzigGame`: the Dantzig game of a linear program and its dual.
* `Cslib.Probability.feasibilityGame`: the Dantzig game associated with `F(A, b)`.

## Main results

* `Cslib.Probability.exists_isSymmetricGameSolution`: every symmetric game has a solution
  ([Adler2013], Theorem 1).
* `Cslib.Probability.IsSymmetricGameSolution.optimal_of_dantzigGame`,
  `Cslib.Probability.IsSymmetricGameSolution.not_feasible_of_dantzigGame`: Dantzig's read-off
  ([Adler2013], Theorem 2(b)–(c)).
* `Cslib.Probability.exists_dantzigGame_undetermined`: an original example of the gap in
  Dantzig's reduction.
* `Cslib.Probability.IsSymmetricGameSolution.pos_of_feasibilityGame_bounded`: the bounded game
  has no solution with `t = 0` ([Adler2013], Proposition 6).
* `Cslib.Probability.resolves_of_feasibilityGame_bounded`: Adler's
  reduction of a linear feasibility problem with integer data to one symmetric game
  ([Adler2013], Section 3.1).

The remaining parts of [Adler2013] are open here: the reduction of a pair of dual programs to
one feasibility problem (p. 167), the bound on `β` for algebraic data (Section 3.1), the
Cook-type reduction (Section 3.2) and the derivation of Farkas' lemma from the minimax theorem
(Section 4).

## References

* [Adler2013]
* [Dantzig1951]
-/

public section

namespace Cslib.Probability

open Finset Matrix
open scoped Nat

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Symmetric games -/

section Symmetric

variable {ι : Type*} [Fintype ι]

/-- `z` *solves the symmetric game* with payoff matrix `P` ([Adler2013], (3)): `z` is a mixed
strategy and `0 ≤ P *ᵥ z`. For skew-symmetric `P` the value of the game is `0`, and the
solutions are its optimal strategies. -/
structure IsSymmetricGameSolution (P : Matrix ι ι K) (z : ι → K) : Prop where
  /-- Every weight is nonnegative. -/
  nonneg : 0 ≤ z
  /-- The weights sum to `1`. -/
  sum_eq_one : ∑ i, z i = 1
  /-- Every pure strategy of the opponent pays at least `0` against `z`. -/
  mulVec_nonneg : 0 ≤ P *ᵥ z

/-- **The minimax theorem for symmetric games** ([Adler2013], Theorem 1): every skew-symmetric
matrix `P` has a solution. The value `v` of the game (`exists_isMinimaxValue`) is also the value
`-v` of the game with the players' roles exchanged, so `v = 0`, and an optimal strategy of the
column player solves the game. -/
theorem exists_isSymmetricGameSolution [Nonempty ι] {P : Matrix ι ι K} (hP : Pᵀ = -P) :
    ∃ z, IsSymmetricGameSolution P z := by
  have hskew (i j : ι) : P j i = -P i j := by
    simpa using congr_fun (congr_fun hP i) j
  obtain ⟨v, ⟨p, hp⟩, q, hq⟩ := exists_isMinimaxValue fun i j => P i j
  have hv : IsMinimaxValue (fun i j => P i j) (-v) := by
    refine ⟨⟨q, fun j => ?_⟩, p, fun i => ?_⟩
    · have hsum : ∑ i, q.weights i * P i j = -∑ i, q.weights i * P j i := by
        rw [← sum_neg_distrib]
        exact sum_congr rfl fun i _ => by rw [hskew j i, mul_neg]
      linarith [hq j]
    · have hsum : ∑ j, p.weights j * P j i = -∑ j, p.weights j * P i j := by
        rw [← sum_neg_distrib]
        exact sum_congr rfl fun j _ => by rw [hskew i j, mul_neg]
      linarith [hp i]
  have hv0 : v = 0 := by
    have := hv.unique ⟨⟨p, hp⟩, q, hq⟩
    linarith
  refine ⟨fun i => q.weights i, fun i => q.weights_nonneg i, q.total_of_fintype, fun i => ?_⟩
  have := hq i
  rw [hv0] at this
  simpa only [mulVec, dotProduct, mul_comm, Pi.zero_apply] using this

end Symmetric

/-! ### Dantzig's game of a linear program -/

section Dantzig

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The *Dantzig game* of the linear program `min {c ⬝ᵥ x | b ≤ A *ᵥ x, 0 ≤ x}` and its dual
`max {y ⬝ᵥ b | y ᵥ* A ≤ c, 0 ≤ y}` ([Adler2013], (4); [Dantzig1951]): the skew-symmetric matrix
with block rows `(0, A, -b)`, `(-Aᵀ, 0, c)` and `(bᵀ, -cᵀ, 0)`, indexed by `m ⊕ n ⊕ Unit`. A
strategy `Sum.elim y (Sum.elim x fun _ => t)` puts weight `y` on the dual variables, `x` on the
primal variables and `t` on the right-hand side. -/
@[expose] def dantzigGame (A : Matrix m n K) (b : m → K) (c : n → K) :
    Matrix (m ⊕ n ⊕ Unit) (m ⊕ n ⊕ Unit) K :=
  Matrix.of fun
    | .inl i, .inr (.inl j) => A i j
    | .inl i, .inr (.inr _) => -b i
    | .inr (.inl j), .inl i => -A i j
    | .inr (.inl j), .inr (.inr _) => c j
    | .inr (.inr _), .inl i => b i
    | .inr (.inr _), .inr (.inl j) => -c j
    | _, _ => 0

omit [LinearOrder K] [IsStrictOrderedRing K] [Fintype m] [Fintype n] in
/-- The Dantzig game is symmetric. -/
theorem dantzigGame_transpose (A : Matrix m n K) (b : m → K) (c : n → K) :
    (dantzigGame A b c)ᵀ = -dantzigGame A b c := by
  ext (i | j | _) (i' | j' | _) <;> simp [dantzigGame]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The Dantzig game pays, against the strategy `(y, x, t)`, the slacks of the constraints of the
two programs scaled by `t`, and the duality gap. -/
private theorem dantzigGame_mulVec (A : Matrix m n K) (b : m → K) (c : n → K) (y : m → K)
    (x : n → K) (t : K) :
    dantzigGame A b c *ᵥ Sum.elim y (Sum.elim x fun _ => t) =
      Sum.elim (A *ᵥ x - t • b) (Sum.elim (t • c - y ᵥ* A) fun _ => y ⬝ᵥ b - c ⬝ᵥ x) := by
  ext (i | j | _) <;>
    simp [dantzigGame, mulVec, vecMul, dotProduct, Fintype.sum_sum_type, sub_eq_add_neg,
      mul_comm, add_comm]

/-- A solution `(y, x, t)` of the Dantzig game is a nonnegative strategy with
`t • b ≤ A *ᵥ x`, `y ᵥ* A ≤ t • c` and `c ⬝ᵥ x ≤ y ⬝ᵥ b` ([Adler2013], (5)). -/
theorem isSymmetricGameSolution_dantzigGame_iff {A : Matrix m n K} {b : m → K} {c : n → K}
    {y : m → K} {x : n → K} {t : K} :
    IsSymmetricGameSolution (dantzigGame A b c) (Sum.elim y (Sum.elim x fun _ => t)) ↔
      0 ≤ y ∧ 0 ≤ x ∧ 0 ≤ t ∧ ∑ i, y i + ∑ j, x j + t = 1 ∧
        t • b ≤ A *ᵥ x ∧ y ᵥ* A ≤ t • c ∧ c ⬝ᵥ x ≤ y ⬝ᵥ b := by
  have h0 : (0 : m ⊕ n ⊕ Unit → K) =
      Sum.elim (0 : m → K) (Sum.elim (0 : n → K) fun _ => (0 : K)) := by
    ext (i | j | _) <;> rfl
  constructor
  · rintro ⟨hz, hsum, hP⟩
    rw [h0, Sum.elim_le_elim_iff, Sum.elim_le_elim_iff] at hz
    rw [dantzigGame_mulVec, h0, Sum.elim_le_elim_iff, Sum.elim_le_elim_iff] at hP
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, univ_unique,
      sum_singleton] at hsum
    refine ⟨hz.1, hz.2.1, hz.2.2 (), by rw [← hsum, add_assoc], ?_, ?_, ?_⟩
    · exact fun i => sub_nonneg.1 (hP.1 i)
    · exact fun j => sub_nonneg.1 (hP.2.1 j)
    · exact sub_nonneg.1 (hP.2.2 ())
  · rintro ⟨hy, hx, ht, hsum, hb, hc, hgap⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [h0, Sum.elim_le_elim_iff, Sum.elim_le_elim_iff]
      exact ⟨hy, hx, fun _ => ht⟩
    · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, univ_unique, sum_singleton]
      rw [← hsum, add_assoc]
    · rw [dantzigGame_mulVec, h0, Sum.elim_le_elim_iff, Sum.elim_le_elim_iff]
      exact ⟨fun i => sub_nonneg.2 (hb i), fun j => sub_nonneg.2 (hc j),
        fun _ => sub_nonneg.2 hgap⟩

/-- Weak duality for the pair `min {c ⬝ᵥ x | b ≤ A *ᵥ x, 0 ≤ x}`,
`max {y ⬝ᵥ b | y ᵥ* A ≤ c, 0 ≤ y}`, homogenized by `s` and `t`. -/
private theorem smul_dotProduct_le {A : Matrix m n K} {b : m → K} {c : n → K} {x : n → K}
    {y : m → K} {s t : K} (hx : 0 ≤ x) (hAx : s • b ≤ A *ᵥ x) (hy : 0 ≤ y)
    (hyA : y ᵥ* A ≤ t • c) : s * (y ⬝ᵥ b) ≤ t * (c ⬝ᵥ x) := by
  calc s * (y ⬝ᵥ b) = y ⬝ᵥ (s • b) := by rw [dotProduct_smul, smul_eq_mul]
    _ ≤ y ⬝ᵥ (A *ᵥ x) := dotProduct_le_dotProduct_of_nonneg_left hAx hy
    _ = (y ᵥ* A) ⬝ᵥ x := dotProduct_mulVec y A x
    _ ≤ (t • c) ⬝ᵥ x := dotProduct_le_dotProduct_of_nonneg_right hyA hx
    _ = t * (c ⬝ᵥ x) := by rw [smul_dotProduct, smul_eq_mul]

namespace IsSymmetricGameSolution

variable {A : Matrix m n K} {b : m → K} {c : n → K} {y : m → K} {x : n → K} {t : K}

/-- A step of Dantzig's read-off (`optimal_of_dantzigGame`, `not_feasible_of_dantzigGame`),
after [Adler2013], Theorem 2(a): a solution `(y, x, t)` of the Dantzig game has
`t * (y ⬝ᵥ b - c ⬝ᵥ x) = 0`. -/
theorem mul_sub_eq_zero_of_dantzigGame
    (h : IsSymmetricGameSolution (dantzigGame A b c) (Sum.elim y (Sum.elim x fun _ => t))) :
    t * (y ⬝ᵥ b - c ⬝ᵥ x) = 0 := by
  obtain ⟨hy, hx, ht, -, hb, hc, hgap⟩ := isSymmetricGameSolution_dantzigGame_iff.1 h
  have := smul_dotProduct_le hx hb hy hc
  nlinarith [mul_nonneg ht (sub_nonneg.2 hgap)]

/-- **Dantzig's read-off** ([Adler2013], Theorem 2(b); [Dantzig1951]): if `(y, x, t)` solves
the Dantzig game and `0 < t`, then `x / t` is an optimal solution of
`min {c ⬝ᵥ x | b ≤ A *ᵥ x, 0 ≤ x}` and `y / t` is an optimal solution of its dual
`max {y ⬝ᵥ b | y ᵥ* A ≤ c, 0 ≤ y}`. -/
theorem optimal_of_dantzigGame
    (h : IsSymmetricGameSolution (dantzigGame A b c) (Sum.elim y (Sum.elim x fun _ => t)))
    (ht : 0 < t) :
    (0 ≤ t⁻¹ • x ∧ b ≤ A *ᵥ (t⁻¹ • x)) ∧
      (∀ x', 0 ≤ x' → b ≤ A *ᵥ x' → c ⬝ᵥ (t⁻¹ • x) ≤ c ⬝ᵥ x') ∧
      (0 ≤ t⁻¹ • y ∧ (t⁻¹ • y) ᵥ* A ≤ c) ∧
      ∀ y', 0 ≤ y' → y' ᵥ* A ≤ c → y' ⬝ᵥ b ≤ (t⁻¹ • y) ⬝ᵥ b := by
  have hgap := h.mul_sub_eq_zero_of_dantzigGame
  obtain ⟨hy, hx, -, -, hb, hc, -⟩ := isSymmetricGameSolution_dantzigGame_iff.1 h
  have hti : 0 ≤ t⁻¹ := inv_nonneg.2 ht.le
  have hval : c ⬝ᵥ (t⁻¹ • x) = (t⁻¹ • y) ⬝ᵥ b := by
    rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    have : y ⬝ᵥ b - c ⬝ᵥ x = 0 := (mul_eq_zero.1 hgap).resolve_left ht.ne'
    rw [sub_eq_zero.1 this]
  have hx' : b ≤ A *ᵥ (t⁻¹ • x) := by
    rw [mulVec_smul]
    intro i
    have := hb i
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    rwa [le_inv_mul_iff₀ ht]
  have hy' : (t⁻¹ • y) ᵥ* A ≤ c := by
    rw [smul_vecMul]
    intro j
    have := hc j
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    rwa [inv_mul_le_iff₀ ht]
  refine ⟨⟨smul_nonneg hti hx, hx'⟩, fun x' hx'0 hAx' => ?_, ⟨smul_nonneg hti hy, hy'⟩,
    fun y' hy'0 hy'A => ?_⟩
  · rw [hval]
    simpa using smul_dotProduct_le (s := 1) (t := 1) hx'0 (by simpa using hAx')
      (smul_nonneg hti hy) (by simpa using hy')
  · rw [← hval]
    simpa using smul_dotProduct_le (s := 1) (t := 1) (smul_nonneg hti hx) (by simpa using hx')
      hy'0 (by simpa using hy'A)

/-- If `(y, x, t)` solves the Dantzig game with `c ⬝ᵥ x < y ⬝ᵥ b`, then the program
`min {c ⬝ᵥ x | b ≤ A *ᵥ x, 0 ≤ x}` or its dual is infeasible ([Adler2013], Theorem 2(c);
[Dantzig1951]). -/
theorem not_feasible_of_dantzigGame
    (h : IsSymmetricGameSolution (dantzigGame A b c) (Sum.elim y (Sum.elim x fun _ => t)))
    (hlt : c ⬝ᵥ x < y ⬝ᵥ b) :
    ¬((∃ x', 0 ≤ x' ∧ b ≤ A *ᵥ x') ∧ ∃ y', 0 ≤ y' ∧ y' ᵥ* A ≤ c) := by
  have hgap := h.mul_sub_eq_zero_of_dantzigGame
  obtain ⟨hy, hx, -, -, hb, hc, -⟩ := isSymmetricGameSolution_dantzigGame_iff.1 h
  have ht : t = 0 := (mul_eq_zero.1 hgap).resolve_right (sub_ne_zero.2 hlt.ne')
  subst ht
  rintro ⟨⟨x', hx', hAx'⟩, y', hy', hy'A⟩
  -- `y ⬝ᵥ b ≤ 0` against the primal solution `x'`, and `0 ≤ c ⬝ᵥ x` against the dual one `y'`
  have h₁ := smul_dotProduct_le (s := 1) hx' (by simpa using hAx') hy hc
  have h₂ := smul_dotProduct_le (t := 1) hx hb hy' (by simpa using hy'A)
  simp only [one_mul, zero_mul] at h₁ h₂
  linarith

end IsSymmetricGameSolution

/-- **An example of the gap in Dantzig's reduction** (original; it illustrates the remark of
[Adler2013], p. 166, which cites [Dantzig1951]): a solution `(y, x, 0)` of the Dantzig game with
`c ⬝ᵥ x = y ⬝ᵥ b` does not determine the program. The same such strategy solves the Dantzig
games of `min {0 | 0 ≤ 0, 0 ≤ x}`, which has an optimal solution, and of
`min {0 | 1 ≤ 0, 0 ≤ x}`, which is infeasible. -/
theorem exists_dantzigGame_undetermined :
    ∃ (A : Matrix Unit Unit K) (b₀ b₁ c y x : Unit → K),
      IsSymmetricGameSolution (dantzigGame A b₀ c) (Sum.elim y (Sum.elim x fun _ => 0)) ∧
      IsSymmetricGameSolution (dantzigGame A b₁ c) (Sum.elim y (Sum.elim x fun _ => 0)) ∧
      c ⬝ᵥ x = y ⬝ᵥ b₀ ∧ c ⬝ᵥ x = y ⬝ᵥ b₁ ∧
      (∃ x₀, (0 ≤ x₀ ∧ b₀ ≤ A *ᵥ x₀) ∧ ∀ x', 0 ≤ x' → b₀ ≤ A *ᵥ x' → c ⬝ᵥ x₀ ≤ c ⬝ᵥ x') ∧
      ¬∃ x', 0 ≤ x' ∧ b₁ ≤ A *ᵥ x' := by
  refine ⟨0, 0, 1, 0, 0, 1, ?_, ?_, by simp, by simp, ⟨0, by simp, by simp⟩, ?_⟩
  · refine isSymmetricGameSolution_dantzigGame_iff.2 ⟨le_rfl, zero_le_one, le_rfl, ?_, ?_, ?_, ?_⟩
      <;> simp
  · refine isSymmetricGameSolution_dantzigGame_iff.2 ⟨le_rfl, zero_le_one, le_rfl, ?_, ?_, ?_, ?_⟩
      <;> simp
  · rintro ⟨x', -, h⟩
    linarith [show (1 : K) ≤ 0 by simpa using h ()]

end Dantzig

/-! ### Adler's repair: linear feasibility problems -/

section Feasibility

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The *Dantzig game associated with the linear feasibility problem* `F(A, b)`
(`0 ≤ x`, `A *ᵥ x = b`) ([Adler2013], Section 2): the Dantzig game of the program
`min {u | b ≤ A *ᵥ x + u • 1, ∑ i, (A *ᵥ x) i - u ≤ ∑ i, b i, 0 ≤ x, 0 ≤ u}`, whose constraint
matrix has block rows `(A, 1)` and `(-1ᵀ A, 1)`. A strategy
`Sum.elim (Sum.elim y fun _ => v) (Sum.elim (Sum.elim x fun _ => u) fun _ => t)` is Adler's
`(y, v, x, u, t)`. -/
@[expose] def feasibilityGame (A : Matrix m n K) (b : m → K) :
    Matrix ((m ⊕ Unit) ⊕ (n ⊕ Unit) ⊕ Unit) ((m ⊕ Unit) ⊕ (n ⊕ Unit) ⊕ Unit) K :=
  dantzigGame (fromBlocks A (of fun _ _ => 1) (of fun _ j => -∑ i, A i j) 1)
    (Sum.elim b fun _ => -∑ i, b i) (Sum.elim 0 1)

omit [LinearOrder K] [IsStrictOrderedRing K] [Fintype n] in
/-- The Dantzig game associated with `F(A, b)` is symmetric. -/
theorem feasibilityGame_transpose (A : Matrix m n K) (b : m → K) :
    (feasibilityGame A b)ᵀ = -feasibilityGame A b :=
  dantzigGame_transpose _ _ _

/-- The solutions of the Dantzig game associated with `F(A, b)` are the solutions of
[Adler2013], (6a)–(6g). -/
private theorem feasibilityGame_spec {A : Matrix m n K} {b : m → K} {y : m → K} {v : K}
    {x : n → K} {u t : K}
    (h : IsSymmetricGameSolution (feasibilityGame A b)
      (Sum.elim (Sum.elim y fun _ => v) (Sum.elim (Sum.elim x fun _ => u) fun _ => t))) :
    (∀ i, t * b i ≤ (A *ᵥ x) i + u) ∧ ∑ i, (A *ᵥ x) i - u ≤ t * ∑ i, b i ∧
      (y - v • 1) ᵥ* A ≤ 0 ∧ ∑ i, y i + v ≤ t ∧ u ≤ (y - v • 1) ⬝ᵥ b ∧
      0 ≤ y ∧ 0 ≤ v ∧ 0 ≤ x ∧ 0 ≤ u ∧ 0 ≤ t ∧ ∑ i, y i + v + (∑ j, x j + u) + t = 1 := by
  obtain ⟨hy, hx, ht, hsum, hb, hc, hgap⟩ := isSymmetricGameSolution_dantzigGame_iff.1 h
  rw [← Sum.elim_zero_zero, Sum.elim_le_elim_iff] at hy hx
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, univ_unique, sum_singleton]
    at hsum
  have hb₁ (i : m) := hb (.inl i)
  have hb₂ := hb (.inr ())
  have hc₁ (j : n) := hc (.inl j)
  have hc₂ := hc (.inr ())
  simp only [Pi.smul_apply, Sum.elim_inl, Sum.elim_inr, smul_eq_mul, mul_neg, vecMul,
    dotProduct, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₂₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₂, of_apply, mulVec, univ_unique, sum_singleton, one_apply_eq, mul_one,
    one_mul, Pi.zero_apply, mul_zero, zero_mul, sum_const_zero, Pi.one_apply, zero_add, neg_mul,
    sum_neg_distrib]
    at hb₁ hb₂ hc₁ hc₂ hgap
  -- the column sums of `A` against `x`, and of `A` against `y`, in one normal form
  have hAx : ∑ i, (A *ᵥ x) i = ∑ j, (∑ i, A i j) * x j := by
    simp only [mulVec, dotProduct, sum_mul]
    exact sum_comm
  refine ⟨fun i => ?_, ?_, fun j => ?_, hc₂, ?_, hy.1, hy.2 (), hx.1, hx.2 (), ht, hsum⟩
  · simpa [mulVec, dotProduct] using hb₁ i
  · rw [hAx]
    linarith
  · have hj := hc₁ j
    simp only [vecMul, dotProduct, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
      mul_one, sub_mul, sum_sub_distrib, Pi.zero_apply, ← mul_sum]
    linarith
  · simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
      sub_mul, sum_sub_distrib, ← mul_sum]
    linarith

namespace IsSymmetricGameSolution

variable {A : Matrix m n K} {b : m → K} {y : m → K} {v : K} {x : n → K} {u t : K}

/-- A step of Adler's reduction (`resolves_of_feasibilityGame_bounded`, [Adler2013],
Section 3.1), after [Adler2013], Proposition 4(a)(i): if `(y, v, x, u, t)` solves the Dantzig
game associated with `F(A, b)`, `0 < t` and `u = 0`, then `x / t` solves `F(A, b)`. -/
theorem mulVec_eq_of_feasibilityGame
    (h : IsSymmetricGameSolution (feasibilityGame A b)
      (Sum.elim (Sum.elim y fun _ => v) (Sum.elim (Sum.elim x fun _ => u) fun _ => t)))
    (ht : 0 < t) (hu : u = 0) : 0 ≤ t⁻¹ • x ∧ A *ᵥ (t⁻¹ • x) = b := by
  obtain ⟨h₁, h₂, -, -, -, -, -, hx, -⟩ := feasibilityGame_spec h
  subst hu
  -- the slacks `(A *ᵥ x) i - t * b i` are nonnegative and sum to at most `0`
  have hslack : ∀ i ∈ univ, 0 ≤ (A *ᵥ x) i - t * b i := fun i _ => by linarith [h₁ i]
  have hsum : ∑ i, ((A *ᵥ x) i - t * b i) = 0 := by
    refine le_antisymm ?_ (sum_nonneg hslack)
    rw [sum_sub_distrib, ← mul_sum]
    linarith
  refine ⟨smul_nonneg (inv_nonneg.2 ht.le) hx, funext fun i => ?_⟩
  have := (sum_eq_zero_iff_of_nonneg hslack).1 hsum i (mem_univ i)
  rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ ht.ne']
  linarith

/-- A step of Adler's reduction (`resolves_of_feasibilityGame_bounded`, [Adler2013],
Section 3.1), after [Adler2013], Proposition 4(a)(ii), which also assumes `0 < t`: if
`(y, v, x, u, t)` solves the Dantzig game associated with `F(A, b)` and `0 < u`, then `F(A, b)`
has no solution; `y - v • 1` is a certificate of infeasibility. -/
theorem not_exists_of_feasibilityGame
    (h : IsSymmetricGameSolution (feasibilityGame A b)
      (Sum.elim (Sum.elim y fun _ => v) (Sum.elim (Sum.elim x fun _ => u) fun _ => t)))
    (hu : 0 < u) : ¬∃ x', 0 ≤ x' ∧ A *ᵥ x' = b := by
  obtain ⟨-, -, hc, -, hgap, -⟩ := feasibilityGame_spec h
  rintro ⟨x', hx', rfl⟩
  have : (y - v • 1) ⬝ᵥ (A *ᵥ x') ≤ 0 := by
    rw [dotProduct_mulVec]
    simpa using dotProduct_le_dotProduct_of_nonneg_right hc hx'
  linarith

/-- A step of Adler's reduction (`resolves_of_feasibilityGame_bounded`, [Adler2013],
Section 3.1), after [Adler2013], Proposition 4(b): if `(y, v, x, 0)` solves the Dantzig game
associated with `F(A, b)`, then `x` is a nonzero solution of `0 ≤ x`, `A *ᵥ x = 0`. Such `x`
exist whenever the solutions of `F(A, b)` are unbounded, so they do not resolve `F(A, b)`. -/
theorem mulVec_eq_zero_of_feasibilityGame
    (h : IsSymmetricGameSolution (feasibilityGame A b)
      (Sum.elim (Sum.elim y fun _ => v) (Sum.elim (Sum.elim x fun _ => u) fun _ => 0))) :
    x ≠ 0 ∧ 0 ≤ x ∧ A *ᵥ x = 0 := by
  obtain ⟨h₁, h₂, -, hd, he, hy, hv, hx, hu, -, hsum⟩ := feasibilityGame_spec h
  -- `t = 0` forces `y = 0`, `v = 0` and then `u = 0`
  have hy0 : ∑ i, y i = 0 := le_antisymm (by linarith) (sum_nonneg fun i _ => hy i)
  have hy0' : y = 0 := funext fun i => (sum_eq_zero_iff_of_nonneg fun i _ => hy i).1 hy0 i
    (mem_univ i)
  have hv0 : v = 0 := by linarith
  have hu0 : u = 0 := by
    subst hy0' hv0
    simp only [zero_smul, sub_zero, zero_dotProduct] at he
    linarith
  subst hu0
  have hslack : ∀ i ∈ univ, 0 ≤ (A *ᵥ x) i := fun i _ => by linarith [h₁ i]
  have hAx : ∑ i, (A *ᵥ x) i = 0 := le_antisymm (by linarith) (sum_nonneg hslack)
  refine ⟨fun hx0 => ?_, hx, funext fun i => (sum_eq_zero_iff_of_nonneg hslack).1 hAx i
    (mem_univ i)⟩
  subst hx0
  simp only [Pi.zero_apply, sum_const_zero] at hsum
  linarith

/-- **Bounding removes the gap** ([Adler2013], Proposition 6): the Dantzig game associated with
the bounded problem `F(Â, b̂(β))`, namely `0 ≤ (x, s)`, `A *ᵥ x = b` and `∑ j, x j + s = β`, has
no solution with `t = 0`. Adler assumes `0 < β`; the proof does not need it. -/
theorem pos_of_feasibilityGame_bounded {β : K} {y : m ⊕ Unit → K} {x : n ⊕ Unit → K}
    (h : IsSymmetricGameSolution
      (feasibilityGame (fromBlocks A 0 (of fun _ _ => 1) 1) (Sum.elim b fun _ => β))
      (Sum.elim (Sum.elim y fun _ => v) (Sum.elim (Sum.elim x fun _ => u) fun _ => t))) :
    0 < t := by
  refine (feasibilityGame_spec h).2.2.2.2.2.2.2.2.2.1.lt_of_ne fun ht => ?_
  subst ht
  obtain ⟨hx0, hx, hAx⟩ := h.mulVec_eq_zero_of_feasibilityGame
  -- the last row `∑ j, x j + s = 0` with `0 ≤ x` forces `x = 0`
  have hrow := congr_fun hAx (.inr ())
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    of_apply, one_mul, univ_unique, sum_singleton, one_apply_eq, Pi.zero_apply] at hrow
  have hnn : ∀ j ∈ univ, 0 ≤ x j := fun j _ => hx j
  have : ∑ j, x j = 0 := by
    simpa only [Fintype.sum_sum_type, univ_unique, sum_singleton] using hrow
  exact hx0 (funext fun j => (sum_eq_zero_iff_of_nonneg hnn).1 this j (mem_univ j))

end IsSymmetricGameSolution

/-- A step of Adler's reduction, after [Adler2013], Proposition 7, for integer data: a solvable
integer system `A *ᵥ x = b`, `0 ≤ x`, with entries of absolute value at most `B` has a solution
of total weight at most `card n * ((card n)! * (card m * B ^ 2 + 1) ^ card n)`. -/
private theorem exists_nonneg_mulVec_eq_sum_le {A : Matrix m n ℤ} {b : m → ℤ} {B : ℕ}
    (hA : ∀ i j, |A i j| ≤ B) (hb : ∀ i, |b i| ≤ B) {x : n → K} (hx : 0 ≤ x)
    (hAx : A.map (Int.cast : ℤ → K) *ᵥ x = fun i => (b i : K)) :
    ∃ x' : n → K, 0 ≤ x' ∧ A.map (Int.cast : ℤ → K) *ᵥ x' = (fun i => (b i : K)) ∧
      ∑ j, x' j ≤
        ((Fintype.card n * ((Fintype.card n)! * (Fintype.card m * B ^ 2 + 1) ^ Fintype.card n) :
          ℕ) : K) := by
  obtain ⟨d, p, hd, hp, hAp, -, hpN⟩ := Matrix.exists_int_nonneg_mulVec_eq hA hb hx hAx
  set N : ℕ := (Fintype.card n)! * (Fintype.card m * B ^ 2 + 1) ^ Fintype.card n
  have hdK : (1 : K) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : K) < d := by exact_mod_cast hd
  refine ⟨fun j => (p j : K) / d, fun j => div_nonneg (by exact_mod_cast hp j) hd0.le, ?_, ?_⟩
  · funext i
    have h1 := congr_arg (fun z : ℤ => (z : K)) (congr_fun hAp i)
    simp only [mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Pi.smul_apply, smul_eq_mul,
      Int.cast_mul, map_apply] at h1 ⊢
    simp only [mul_div_assoc', ← sum_div, h1]
    field_simp
  · calc ∑ j, (p j : K) / d ≤ ∑ _j : n, (N : K) := sum_le_sum fun j _ => by
          rw [div_le_iff₀ hd0]
          calc (p j : K) ≤ N := by exact_mod_cast hpN j
            _ = N * 1 := (mul_one _).symm
            _ ≤ N * d := mul_le_mul_of_nonneg_left hdK (Nat.cast_nonneg _)
      _ = _ := by simp [N]

/-- **Adler's reduction of linear feasibility to one symmetric game** ([Adler2013],
Section 3.1, Propositions 4, 6 and 7), for integer data. Let `A *ᵥ x = b`, `0 ≤ x` be an integer
system with entries of absolute value at most `B`, and let
`β ≥ card n * ((card n)! * (card m * B ^ 2 + 1) ^ card n)`. Every solution `(y, v, x, u, t)` of
the Dantzig game associated with the bounded problem `F(Â, b̂(β))` has `0 < t`, and it resolves
`F(A, b)` over `K`: if `u = 0`, the first `card n` coordinates of `x / t` solve it; if `0 < u`,
it has no solution. Since `0 ≤ u`, one of the two holds, and solutions exist by
`exists_isSymmetricGameSolution` and `feasibilityGame_transpose`. Adler's bound
`m (√m θ) ^ m + 1` (Hadamard) is replaced by the Leibniz bound of
`Matrix.exists_int_nonneg_mulVec_eq`; that the reduction is strongly polynomial is not
formalized. -/
theorem resolves_of_feasibilityGame_bounded {A : Matrix m n ℤ} {b : m → ℤ} {B : ℕ}
    (hA : ∀ i j, |A i j| ≤ B) (hb : ∀ i, |b i| ≤ B) {β : K}
    (hβ : ((Fintype.card n * ((Fintype.card n)! * (Fintype.card m * B ^ 2 + 1) ^ Fintype.card n) :
      ℕ) : K) ≤ β)
    {y : m ⊕ Unit → K} {v : K} {x : n ⊕ Unit → K} {u t : K}
    (h : IsSymmetricGameSolution
      (feasibilityGame (fromBlocks (A.map (Int.cast : ℤ → K)) 0 (of fun _ _ => 1) 1)
        (Sum.elim (fun i => (b i : K)) fun _ => β))
      (Sum.elim (Sum.elim y fun _ => v) (Sum.elim (Sum.elim x fun _ => u) fun _ => t))) :
    0 < t ∧
      (u = 0 → 0 ≤ t⁻¹ • (x ∘ Sum.inl) ∧
        A.map (Int.cast : ℤ → K) *ᵥ (t⁻¹ • (x ∘ Sum.inl)) = fun i => (b i : K)) ∧
      (0 < u → ¬∃ x', 0 ≤ x' ∧ A.map (Int.cast : ℤ → K) *ᵥ x' = fun i => (b i : K)) := by
  have ht := h.pos_of_feasibilityGame_bounded
  refine ⟨ht, fun hu => ?_, fun hu ⟨x', hx', hAx'⟩ => ?_⟩
  · obtain ⟨hx, hAx⟩ := h.mulVec_eq_of_feasibilityGame ht hu
    refine ⟨fun j => hx (.inl j), funext fun i => ?_⟩
    have := congr_fun hAx (.inl i)
    simpa [fromBlocks_mulVec, mulVec, dotProduct] using this
  · -- a solution of `F(A, b)` of small total weight extends to one of `F(Â, b̂(β))`
    obtain ⟨x₀, hx₀, hAx₀, hsum⟩ := exists_nonneg_mulVec_eq_sum_le hA hb hx' hAx'
    refine h.not_exists_of_feasibilityGame hu
      ⟨Sum.elim x₀ fun _ => β - ∑ j, x₀ j, ?_, funext fun i => ?_⟩
    · rw [← Sum.elim_zero_zero, Sum.elim_le_elim_iff]
      exact ⟨hx₀, fun _ => sub_nonneg.2 (hsum.trans hβ)⟩
    · rcases i with i | _
      · simpa [mulVec, dotProduct] using congr_fun hAx₀ i
      · simp [mulVec, dotProduct]

end Feasibility

end Cslib.Probability
