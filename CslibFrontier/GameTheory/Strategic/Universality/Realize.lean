/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Semialgebraic
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Tactic.Ring

/-!
# Games with prescribed expected-cost polynomials

Lemma 4 of [Datta2003] (also [McKelveyMcLennan1997]): the expected costs of a finite game can be
any prescribed polynomials, as long as each is affine in every player's block of coordinates and
does not involve the coordinates of the player whose cost it is. Combined with equation (1)
(`CostGame.isTotallyMixedNash_iff`), the totally mixed Nash equilibria of the resulting game are the
positive points of the product of simplices that solve a prescribed polynomial system.

The game is explicit: the cost of player `i` at the pure profile `s` is the prescribed polynomial
for `s i`, evaluated at the vertex of the product of simplices that `s` determines. The proof is
that the expectation, under a product distribution, of a block-affine polynomial evaluated at a
random vertex is the polynomial evaluated at the mean (`sum_productWeight_mul_eval_vertex`).

## Main definitions

* `Cslib.GameTheory.vertex s`: the coordinates of the pure profile `s`, a vertex of the product of
  simplices.
* `Cslib.GameTheory.IsBlockAffine f`: every monomial of `f` has degree at most one in each player's
  block of coordinates.
* `Cslib.GameTheory.CostGame.realize g`: the game whose cost at `s` for player `i` is `g i (s i)` at
  `vertex s`.

## Main results

* `Cslib.GameTheory.sum_productWeight_mul_eval_vertex`: the expectation formula.
* `Cslib.GameTheory.CostGame.deviationCost_realize`: Lemma 4: the expected cost of the pure strategy
  `a` in `realize g` is `g i a`, evaluated at the profile.
* `Cslib.GameTheory.CostGame.isTotallyMixedNash_realize_iff`: the totally mixed Nash equilibria of
  `realize g` when `g i (a₀ i) = 0`: the positive profiles at which every `g i a` vanishes.

## References

* [Datta2003]
* [McKelveyMcLennan1997]
-/

public section

namespace Cslib.GameTheory

open MvPolynomial Finset Function

variable {ι : Type*} {S : ι → Type*}

/-- The coordinates of the pure profile `s`: the vertex of the product of simplices at which every
player `i` puts all its weight on `s i`. -/
@[expose] noncomputable def vertex [∀ i, DecidableEq (S i)] (s : ∀ i, S i) : (Σ i, S i) → ℝ :=
  fun v => if s v.1 = v.2 then 1 else 0

/-- A polynomial in the coordinates of a profile is **block-affine** if each of its monomials has
degree at most one in every player's block of coordinates. -/
@[expose] def IsBlockAffine [∀ i, Fintype (S i)] (f : MvPolynomial (Σ i, S i) ℝ) : Prop :=
  ∀ m ∈ f.support, ∀ i, ∑ b, m ⟨i, b⟩ ≤ 1

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- One block of the expectation formula: for weights summing to `1` and exponents of total degree
at most one, the expectation of `∏ b, [c = b] ^ e b` over `c ∼ q` is `∏ b, q b ^ e b`. -/
private theorem sum_mul_prod_ite_pow {T : Type*} [Fintype T] [DecidableEq T] {q : T → ℝ}
    (hq : ∑ c, q c = 1) {e : T → ℕ} (he : ∑ b, e b ≤ 1) :
    ∑ c, q c * ∏ b, (if c = b then (1 : ℝ) else 0) ^ e b = ∏ b, q b ^ e b := by
  by_cases h0 : ∀ b, e b = 0
  · simp [h0, hq]
  · simp only [not_forall] at h0
    obtain ⟨b₀, hb₀⟩ := h0
    have heb₀ : e b₀ = 1 := by
      have := single_le_sum (fun b _ => Nat.zero_le (e b)) (mem_univ b₀)
      omega
    have hrest : ∀ b, b ≠ b₀ → e b = 0 := by
      intro b hb
      have := add_le_add (single_le_sum (fun b _ => Nat.zero_le (e b)) (mem_univ b))
        (le_refl (e b₀))
      rw [← sum_erase_add _ _ (mem_univ b₀),
        ← add_sum_erase _ _ (mem_erase.2 ⟨hb, mem_univ b⟩)] at he
      have := Nat.zero_le (∑ x ∈ (univ.erase b₀).erase b, e x)
      omega
    have hprod : ∀ x : T → ℝ, ∏ b, x b ^ e b = x b₀ := by
      intro x
      rw [← mul_prod_erase _ _ (mem_univ b₀), heb₀, pow_one,
        prod_eq_one fun b hb => by rw [hrest b (ne_of_mem_erase hb), pow_zero], mul_one]
    simp only [hprod]
    rw [sum_eq_single b₀ (fun c _ hc => by simp [hc]) (by simp)]
    simp

/-- **The expectation formula.** If each player's weights sum to `1` and `f` is block-affine, the
expectation of `f` at the vertex of a random pure profile `s`, drawn from the product distribution,
is `f` at the profile itself. -/
theorem sum_productWeight_mul_eval_vertex {p : ∀ i, S i → ℝ} (hp : ∀ i, ∑ a, p i a = 1)
    {f : MvPolynomial (Σ i, S i) ℝ} (hf : IsBlockAffine f) :
    ∑ s, productWeight p s * eval (vertex s) f = eval (Sigma.uncurry p) f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun m hm => ?_
  simp only [eval_monomial, Finsupp.prod_fintype _ _ fun _ => pow_zero _]
  have key : ∀ x : (Σ i, S i) → ℝ, ∏ v, x v ^ m v = ∏ i, ∏ b, x ⟨i, b⟩ ^ m ⟨i, b⟩ :=
    fun x => Fintype.prod_sigma _
  simp only [key]
  calc ∑ s, productWeight p s * (f.coeff m * ∏ i, ∏ b, vertex s ⟨i, b⟩ ^ m ⟨i, b⟩)
      = f.coeff m * ∑ s, ∏ i, (p i (s i) * ∏ b, vertex s ⟨i, b⟩ ^ m ⟨i, b⟩) := by
        rw [mul_sum]
        refine sum_congr rfl fun s _ => ?_
        rw [productWeight_def, prod_mul_distrib]
        ring
    _ = f.coeff m * ∏ i, ∑ c, p i c * ∏ b, (if c = b then (1 : ℝ) else 0) ^ m ⟨i, b⟩ := by
        rw [Fintype.prod_sum (fun i c => p i c * ∏ b, (if c = b then (1 : ℝ) else 0) ^ m ⟨i, b⟩)]
        rfl
    _ = f.coeff m * ∏ i, ∏ b, Sigma.uncurry p ⟨i, b⟩ ^ m ⟨i, b⟩ := by
        congr 1
        exact prod_congr rfl fun i _ => sum_mul_prod_ite_pow (hp i) (hf m hm i)

namespace CostGame

omit [DecidableEq ι] in
/-- The game that **realizes** the polynomials `g`: the cost of player `i` at the pure profile `s`
is `g i (s i)` evaluated at `vertex s`. -/
noncomputable def realize (g : ∀ i, S i → MvPolynomial (Σ i, S i) ℝ) : CostGame ι S where
  cost i s := eval (vertex s) (g i (s i))

/-- **Lemma 4** of [Datta2003]: if every `g i a` is block-affine and does not involve the
coordinates of player `i`, then in `realize g` the expected cost of player `i`'s pure strategy `a`
is `g i a`, evaluated at the profile. -/
theorem deviationCost_realize {g : ∀ i, S i → MvPolynomial (Σ i, S i) ℝ}
    (hg : ∀ i a, IsBlockAffine (g i a)) (hgi : ∀ i a, ∀ v ∈ (g i a).vars, v.1 ≠ i)
    {p : ∀ i, S i → ℝ} (hp : ∀ i, ∑ a, p i a = 1) (i : ι) (a : S i) :
    (realize g).deviationCost p i a = eval (Sigma.uncurry p) (g i a) := by
  rw [deviationCost_def, ← sum_productWeight_mul_eval_vertex hp (hg i a)]
  refine sum_congr rfl fun s _ => ?_
  simp only [realize, update_self]
  congr 1
  refine eval₂Hom_congr' rfl (fun v hv _ => ?_) rfl
  have hvi : v.1 ≠ i := hgi i a v hv
  simp [vertex, update_of_ne hvi]

/-- The totally mixed Nash equilibria of `realize g`, when `g` satisfies the hypotheses of Lemma 4
and `g i (a₀ i) = 0` for a base strategy `a₀ i` of each player: the positive profiles, with each
player's weights summing to `1`, at which every `g i a` vanishes. -/
theorem isTotallyMixedNash_realize_iff {g : ∀ i, S i → MvPolynomial (Σ i, S i) ℝ}
    (hg : ∀ i a, IsBlockAffine (g i a)) (hgi : ∀ i a, ∀ v ∈ (g i a).vars, v.1 ≠ i)
    (a₀ : ∀ i, S i) (h₀ : ∀ i, g i (a₀ i) = 0) {p : ∀ i, S i → ℝ} :
    (realize g).IsTotallyMixedNash p ↔ (∀ i a, 0 < p i a) ∧ (∀ i, ∑ a, p i a = 1) ∧
      ∀ i a, eval (Sigma.uncurry p) (g i a) = 0 := by
  rw [isTotallyMixedNash_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨hsum, heq⟩
    refine ⟨hsum, fun i a => ?_⟩
    have := heq i a (a₀ i)
    rwa [deviationCost_realize hg hgi hsum, deviationCost_realize hg hgi hsum, h₀, map_zero]
      at this
  · rintro ⟨hsum, hzero⟩
    refine ⟨hsum, fun i a b => ?_⟩
    rw [deviationCost_realize hg hgi hsum, deviationCost_realize hg hgi hsum, hzero, hzero]

end CostGame

end Cslib.GameTheory
