/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Universality.Binary
import Mathlib.Algebra.MvPolynomial.CommRing
import CslibFrontier.Foundations.GroupTheory.Perm.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Datta's binary game

The uniform-degree binary construction in the proof of Theorem 6 of [Datta2003]: for polynomials
`F₀, …, F_{m-1}` in `n` variables whose degree in each variable is at most `d`, with `3 ≤ n d`,
there is a game with `n d + max(m, n)` players, each with two pure strategies, whose totally mixed
Nash equilibria are the points `x ∈ (0, 1)ⁿ` with `F_j(x) = 0`, encoded together with the powers
`x_i ^ k` and, when `m > n`, `m - n` free probabilities.

## The construction

The players (`DattaBinary.Player n d m`) are:
* `var i` for `i < n`, whose probability of `true` is `x_i`;
* `chain i k` for `i < n`, `k < d`, whose probability stands for `x_i ^ (k + 1)`;
* `extra e` for `e < m - n`.

The equations are the chain equations `chain i 0 = var i` and `chain i k = var i · chain i (k - 1)`,
and the encoded equations `F̃_j = 0`, where `F̃_j` replaces each `x_i ^ (k + 1)` by `chain i k`.
Every equation is multilinear. Each player is given one equation in which it does not occur
(`binaryGame`, Lemma 4):
* `var i` gets `F̃_i` if `i < m` (chain variables only), and `0` otherwise;
* `extra e` gets `F̃_{n + e}`;
* the chain players, listed in the order `(i, k) ↦ d i + k`, get the chain equation of the
  previous position, cyclically. A chain equation involves its own position and the one before
  it, so with `3 ≤ n d` the player two positions on does not occur in it.

Datta matches equations to chain players by Hall's theorem; the cyclic shift is an explicit
matching. Datta's paper also treats `n d ≤ 2` by special cases, and reduces the player count to
`n d + m` when `n > m`; neither refinement is formalized here. The hypothesis `3 ≤ n d` costs
nothing for universality, since `d` is only an upper bound on the degrees.

## Main definitions

* `Cslib.GameTheory.DattaBinary.game F`: the game.

## Main results

* `Cslib.GameTheory.DattaBinary.isTotallyMixedNash_game_iff`: its totally mixed Nash equilibria.
* `Cslib.GameTheory.DattaBinary.card_player`: it has `n d + max(m, n)` players.

## References

* [Datta2003]
-/

public section

namespace Cslib.GameTheory.DattaBinary

open MvPolynomial Finset Function

/-- The players of Datta's binary game: `n` variable players, `n d` chain players and `m - n`
extra players. -/
abbrev Player (n d m : ℕ) : Type := Fin n ⊕ (Fin n × Fin d) ⊕ Fin (m - n)

variable {n d m : ℕ}

/-- The variable player `i`, whose probability of `true` is `x_i`. -/
abbrev var (i : Fin n) : Player n d m := .inl i

/-- The chain player `(i, k)`, whose probability of `true` stands for `x_i ^ (k + 1)`. -/
abbrev chain (c : Fin n × Fin d) : Player n d m := .inr (.inl c)

/-- The extra player `e`. -/
abbrev extra (e : Fin (m - n)) : Player n d m := .inr (.inr e)

theorem card_player : Fintype.card (Player n d m) = n * d + max m n := by
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
  omega

/-- The factor of the encoded monomial for the power `x_i ^ e`: `1` if `e = 0`, and the chain
variable `chain i (e - 1)` if `1 ≤ e ≤ d`. -/
noncomputable def powerFactor (i : Fin n) (e : ℕ) : MvPolynomial (Player n d m) ℝ :=
  if e = 0 then 1 else if h : e - 1 < d then X (chain (i, ⟨e - 1, h⟩)) else 0

/-- The encoding `F̃` of `F`: each monomial `∏ x_i ^ e_i` becomes `∏ chain i (e_i - 1)`. -/
noncomputable def encode (F : MvPolynomial (Fin n) ℝ) : MvPolynomial (Player n d m) ℝ :=
  ∑ e ∈ F.support, C (F.coeff e) * ∏ i, powerFactor i (e i)

/-- The chain equation of `(i, k)`: `chain i 0 - var i`, or `chain i k - var i · chain i (k - 1)`.
-/
noncomputable def chainEq (c : Fin n × Fin d) : MvPolynomial (Player n d m) ℝ :=
  if h : c.2.val = 0 then X (chain c) - X (var c.1)
  else X (chain c) - X (var c.1) * X (chain (c.1, ⟨c.2.val - 1, by omega⟩))

/-- The chain equation assigned to the chain player `c`: that of the previous position, where
`(i, k)` sits at position `d i + k` (`finProdFinEquiv`). -/
def source (c : Fin n × Fin d) : Fin n × Fin d :=
  finProdFinEquiv.symm ((finRotate (n * d)).symm (finProdFinEquiv c))

/-- The equation assigned to each player. -/
noncomputable def equation (F : Fin m → MvPolynomial (Fin n) ℝ) :
    Player n d m → MvPolynomial (Player n d m) ℝ
  | .inl i => if h : i.val < m then encode (F ⟨i, h⟩) else 0
  | .inr (.inl c) => chainEq (source c)
  | .inr (.inr e) => encode (F ⟨n + e, by omega⟩)

/-- **Datta's binary game** for the system `F`. -/
noncomputable def game (F : Fin m → MvPolynomial (Fin n) ℝ) :
    CostGame (Player n d m) (fun _ => Bool) :=
  CostGame.binaryGame (equation (d := d) F)

/-! ### Multilinearity and the matching -/

theorem vars_powerFactor {i : Fin n} {e : ℕ} {v : Player n d m} (hv : v ∈ (powerFactor i e).vars) :
    ∃ k, v = chain (i, k) := by
  unfold powerFactor at hv
  split_ifs at hv with h0 h
  · simp at hv
  · rw [vars_X, Finset.mem_singleton] at hv
    exact ⟨_, hv⟩
  · simp at hv

theorem isMultilinear_powerFactor (i : Fin n) (e : ℕ) :
    IsMultilinear (powerFactor (d := d) (m := m) i e) := by
  unfold powerFactor
  split_ifs
  · exact IsMultilinear.C 1
  · exact IsMultilinear.X _
  · exact IsMultilinear.zero

theorem vars_encode {F : MvPolynomial (Fin n) ℝ} {v : Player n d m} (hv : v ∈ (encode F).vars) :
    ∃ c, v = chain c := by
  classical
  obtain ⟨e, -, he⟩ := Finset.mem_biUnion.1 (vars_sum_subset _ _ hv)
  have he' := vars_mul _ _ he
  rw [vars_C, Finset.empty_union] at he'
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (vars_prod _ he')
  obtain ⟨k, rfl⟩ := vars_powerFactor hi
  exact ⟨_, rfl⟩

theorem isMultilinear_encode (F : MvPolynomial (Fin n) ℝ) :
    IsMultilinear (encode (d := d) (m := m) F) := by
  classical
  refine IsMultilinear.sum fun e _ => (IsMultilinear.C _).mul
    (IsMultilinear.prod (fun i _ => isMultilinear_powerFactor i (e i)) ?_) (by simp)
  intro i _ j _ hij
  refine Finset.disjoint_left.2 fun v hvi hvj => hij ?_
  obtain ⟨k, rfl⟩ := vars_powerFactor hvi
  obtain ⟨k', hk'⟩ := vars_powerFactor hvj
  simp only [chain, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at hk'
  exact hk'.1

theorem isMultilinear_chainEq (c : Fin n × Fin d) : IsMultilinear (chainEq (m := m) c) := by
  classical
  unfold chainEq
  split_ifs
  · exact (IsMultilinear.X _).sub (IsMultilinear.X _)
  · refine (IsMultilinear.X _).sub ((IsMultilinear.X _).mul (IsMultilinear.X _) ?_)
    simp [vars_X]

theorem vars_chainEq {c : Fin n × Fin d} {v : Player n d m} (hv : v ∈ (chainEq c).vars) :
    v = chain c ∨ v = var c.1 ∨ ∃ _ : c.2.val ≠ 0, v = chain (c.1, ⟨c.2.val - 1, by omega⟩) := by
  classical
  unfold chainEq at hv
  split_ifs at hv with h
  · rcases Finset.mem_union.1 (vars_sub_subset (p := _) (q := _) hv) with hv | hv <;>
      simp only [vars_X, Finset.mem_singleton] at hv <;> simp [hv]
  · rcases Finset.mem_union.1 (vars_sub_subset (p := _) (q := _) hv) with hv | hv
    · simp only [vars_X, Finset.mem_singleton] at hv
      simp [hv]
    · rcases Finset.mem_union.1 (vars_mul _ _ hv) with hv | hv <;>
        simp only [vars_X, Finset.mem_singleton] at hv
      · simp [hv]
      · exact Or.inr (Or.inr ⟨h, hv⟩)

/-- In the cyclic assignment, a chain player does not occur in its own equation. -/
theorem notMem_vars_chainEq_source (hN : 3 ≤ n * d) (c : Fin n × Fin d) :
    chain (m := m) c ∉ (chainEq (source c)).vars := by
  intro hv
  have hrot : finProdFinEquiv c = finRotate (n * d) (finProdFinEquiv (source c)) := by
    simp only [source, Equiv.apply_symm_apply]
  have hval := congrArg Fin.val hrot
  rw [val_finRotate] at hval
  have hlt := (finProdFinEquiv (source c)).2
  rcases vars_chainEq hv with h | h | ⟨h0, h⟩
  · simp only [chain, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [← h] at hval
    split_ifs at hval <;> omega
  · simp at h
  · simp only [chain, Sum.inr.injEq, Sum.inl.injEq] at h
    have hp : (finProdFinEquiv c).val + 1 = (finProdFinEquiv (source c)).val := by
      conv_lhs => rw [h]
      rw [finProdFinEquiv_apply_val, finProdFinEquiv_apply_val]
      simp only
      omega
    split_ifs at hval <;> omega

theorem isMultilinear_equation (F : Fin m → MvPolynomial (Fin n) ℝ) (v : Player n d m) :
    IsMultilinear (equation F v) := by
  rcases v with i | c | e
  · simp only [equation]
    split_ifs
    · exact isMultilinear_encode _
    · exact IsMultilinear.zero
  · exact isMultilinear_chainEq _
  · exact isMultilinear_encode _

theorem notMem_vars_equation (hN : 3 ≤ n * d) (F : Fin m → MvPolynomial (Fin n) ℝ)
    (v : Player n d m) : v ∉ (equation F v).vars := by
  rcases v with i | c | e
  · simp only [equation]
    split_ifs
    · rintro hv
      obtain ⟨_, hc⟩ := vars_encode hv
      cases hc
    · simp
  · exact notMem_vars_chainEq_source hN c
  · rintro hv
    obtain ⟨_, hc⟩ := vars_encode hv
    cases hc

/-! ### The equilibria -/

/-- The value of `encode F` at a point where every chain variable `chain i k` is `x_i ^ (k + 1)`
is `F(x)`, provided `F` has degree at most `d` in each variable. -/
theorem eval_encode {F : MvPolynomial (Fin n) ℝ} (hF : ∀ e ∈ F.support, ∀ i, e i ≤ d)
    {q : Player n d m → ℝ} (hq : ∀ c : Fin n × Fin d, q (chain c) = q (var c.1) ^ (c.2.val + 1)) :
    eval q (encode F) = eval (fun i => q (var i)) F := by
  conv_rhs => rw [F.as_sum]
  simp only [encode, map_sum, map_mul, eval_C, map_prod, eval_monomial,
    Finsupp.prod_fintype _ _ fun _ => pow_zero _]
  refine sum_congr rfl fun e he => congrArg (_ * ·) (prod_congr rfl fun i _ => ?_)
  unfold powerFactor
  split_ifs with h0 h
  · simp [h0]
  · rw [eval_X, hq]
    exact congrArg _ (by dsimp only; omega)
  · exact absurd (hF e he i) (by omega)

/-- If every chain equation holds, each chain variable is the corresponding power. -/
theorem chain_eq_pow {q : Player n d m → ℝ} (hq : ∀ c : Fin n × Fin d, eval q (chainEq c) = 0)
    (c : Fin n × Fin d) : q (chain c) = q (var c.1) ^ (c.2.val + 1) := by
  obtain ⟨i, k, hk⟩ := c
  induction k with
  | zero =>
    have h0 := hq (i, ⟨0, hk⟩)
    simp only [chainEq, ↓reduceDIte, map_sub, eval_X, zero_add, pow_one] at h0 ⊢
    linarith
  | succ k ih =>
    have hs := hq (i, ⟨k + 1, hk⟩)
    simp only [chainEq, Nat.add_one_ne_zero, ↓reduceDIte, map_sub, map_mul, eval_X,
      Nat.add_sub_cancel] at hs
    rw [ih (by omega)] at hs
    dsimp only at hs ⊢
    rw [pow_succ]
    linarith [hs]

/-- The chain equations hold at the powers. -/
theorem eval_chainEq_of_pow {q : Player n d m → ℝ}
    (hq : ∀ c : Fin n × Fin d, q (chain c) = q (var c.1) ^ (c.2.val + 1)) (c : Fin n × Fin d) :
    eval q (chainEq c) = 0 := by
  unfold chainEq
  split_ifs with h
  · simp [hq, h]
  · simp only [map_sub, map_mul, eval_X, hq]
    rw [show c.2.val + 1 = c.2.val - 1 + 1 + 1 by omega, pow_succ _ (c.2.val - 1 + 1)]
    ring

theorem source_bijective : Bijective (source (n := n) (d := d)) := by
  unfold source
  exact (finProdFinEquiv.symm.bijective.comp (finRotate (n * d)).symm.bijective).comp
    finProdFinEquiv.bijective

/-- **The uniform-degree binary construction in the proof of Theorem 6 of [Datta2003].** If each
`F j` has degree at most `d` in every variable and `3 ≤ n d`, the totally mixed Nash equilibria of
Datta's binary game are the profiles `binaryProfile q` such that `q` lies in the open cube,
`x = q ∘ var` solves every `F j = 0`, and each chain player plays the power `x_i ^ (k + 1)`. The
extra players are unconstrained. -/
theorem isTotallyMixedNash_game_iff {F : Fin m → MvPolynomial (Fin n) ℝ}
    (hF : ∀ j, ∀ e ∈ (F j).support, ∀ i, e i ≤ d) (hN : 3 ≤ n * d) (q : Player n d m → ℝ) :
    (game F).IsTotallyMixedNash (binaryProfile q) ↔
      (∀ v, 0 < q v ∧ q v < 1) ∧ (∀ j, eval (fun i => q (var i)) (F j) = 0) ∧
        ∀ c : Fin n × Fin d, q (chain c) = q (var c.1) ^ (c.2.val + 1) := by
  rw [game, CostGame.isTotallyMixedNash_binaryGame_iff (isMultilinear_equation F)
    (notMem_vars_equation hN F)]
  refine and_congr_right fun _ => ⟨fun h => ?_, ?_⟩
  · have hpow := chain_eq_pow fun c => by
      obtain ⟨c', rfl⟩ := source_bijective.2 c
      exact h (chain c')
    refine ⟨fun j => ?_, hpow⟩
    rw [← eval_encode (hF j) hpow]
    by_cases hj : j.val < n
    · simpa [equation, j.2] using h (var ⟨j, hj⟩)
    · have hj' : (⟨n + (j.val - n), by omega⟩ : Fin m) = j :=
        Fin.ext <| by
          dsimp only
          omega
      simpa only [equation, hj'] using h (extra ⟨j - n, by omega⟩)
  · rintro ⟨hF0, hpow⟩ (i | c | e)
    · simp only [equation]
      split_ifs with h
      · rw [eval_encode (hF _) hpow, hF0]
      · simp
    · exact eval_chainEq_of_pow hpow _
    · simp only [equation, eval_encode (hF _) hpow, hF0]

end Cslib.GameTheory.DattaBinary
