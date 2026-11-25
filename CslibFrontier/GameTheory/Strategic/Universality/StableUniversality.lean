/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.AlgebraicGeometry.StableIsomorphism
public import CslibFrontier.GameTheory.Strategic.Semialgebraic
public import CslibFrontier.GameTheory.Strategic.Universality.DattaBinary
public import CslibFrontier.GameTheory.Strategic.Universality.DattaHorner
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Universality of Nash equilibria

Theorem 1 of [Datta2003] (arXiv:math/0301001, statement p. 1, proof p. 7): every real algebraic set
`V ⊆ ℝⁿ` is stably isomorphic to the set of totally mixed Nash equilibria of a three-player game,
and to that of a game in which every player has two pure strategies.

## The change of variables

Datta's games encode only polynomial systems whose solutions lie in the open box `(0, 1)ⁿ` or in
the open simplex `{x | 0 < xᵢ, ∑ xᵢ < 1}`. Here a point of the box or simplex is read through the
ratios of each player's non-reference probabilities to the reference probability `x₀`:
`tᵢ = ρ(xᵢ / x₀)` with `ρ(y) = y − 1/y` (`ratioCoord xᵢ x₀ = xᵢ / x₀ − x₀ / xᵢ`). The map `ρ` is an
increasing bijection `(0, ∞) → ℝ` with continuous inverse `ratioInv t = (t + √(t² + 4)) / 2`.
* In the binary game, `x₀ = 1 − xᵢ` for each variable, so `tᵢ = ρ(xᵢ / (1 − xᵢ))` is a bijection
  `(0, 1) → ℝ` with inverse `toUnit`.
* In the three-player game, `x₀ = 1 − ∑ᵢ xᵢ` is Alice's reference probability, and
  `x ↦ (ρ(xᵢ / x₀))ᵢ` is a bijection from the open simplex to `ℝⁿ` with inverse `simplexPoint`.

The equations `Fⱼ(t) = 0` become polynomial equations `clear Fⱼ = 0` after multiplying by
`∏ᵢ (xᵢ x₀)^{d_ij}`, with `d_ij` the degree of `tᵢ` in `Fⱼ` (`eval_clear`). The factor does not
vanish on the box or simplex, and the games force their variables into it, so the cleared system
has no zeros there other than the images of `V` (`clear_eq_zero_iff`).

**Source repair.** Datta (p. 7) uses the bijection `s ↦ s / (1 − s²)` from `(−1, 1)` to `ℝ`,
rescales `(−1, 1)` into the box or simplex and clears denominators. The cleared equations also
vanish at points `s` outside `(−1, 1)`, and these can land inside the box or simplex after the
rescaling: for `V = {(−1, 0)} ⊂ ℝ²`, the cleared equation `s₁ + 1 − s₁² = 0` has the extra root
`s₁ = (1 + √5)/2`, and `x = (s + 1)/4` sends `(s₁, 0)` to `(0.654…, 0.25)`, a second point of the
open simplex. So the equilibrium set of the paper's game can be strictly larger than the image of
`V`. The ratio coordinates above are a bijection onto `ℝⁿ` from exactly the region (box or
simplex) that the game imposes, so this cannot happen.

## The isomorphisms

Write `V × ℝ^κ` for `{z | z ∘ Sum.inl ∈ V}`.
* `binaryHomeomorph F`: for `0 < n`, `V × ℝ^{m − n}` is semialgebraically isomorphic to the
  totally mixed equilibria of `binaryGame F`, Datta's binary game (`DattaBinary.game`) for the
  cleared system. The extra players carry the coordinates of `ℝ^{m − n}`.
* `hornerHomeomorph F`: `V × ℝ^{m − n}` (with the coordinates indexed by the equations `j ≥ n`) is
  semialgebraically isomorphic to the totally mixed equilibria of `hornerGame F`, Datta's Horner
  game (`DattaHorner.game`) for the cleared system. Critter's free probabilities, rescaled to the
  budget `freeBudget` that its fixed probabilities leave, carry the coordinates of `ℝ^{m − n}`.

Both maps are explicit: they send a point of `V × ℝ^{m − n}` to the profile `binaryPoint`,
resp. `hornerPoint`, and their inverses send an equilibrium to the ratio coordinates of the
relevant probabilities (`ratioMap`). The case `n = 0` of the binary game is
reduced to `n = 1` by adding a dummy variable (`stablyIsomorphic_rename_castSucc`).

## Main results

* `Cslib.GameTheory.DattaUniversality.stablyIsomorphic_hornerGame`,
  `Cslib.GameTheory.DattaUniversality.stablyIsomorphic_binaryGame`.
* `Cslib.GameTheory.DattaUniversality.universality`: Theorem 1 of [Datta2003].

## References

* [Datta2003]
-/

public section

namespace Cslib.GameTheory.DattaUniversality

open MvPolynomial Finset Function

/-! ### The change of variables -/

/-- The ratio coordinate `ρ(a / b) = a / b − b / a` of a pair of positive probabilities. -/
@[expose] noncomputable def ratioCoord (a b : ℝ) : ℝ := a / b - b / a

/-- The inverse `t ↦ (t + √(t² + 4)) / 2` of `ρ(y) = y − 1/y` on `(0, ∞)`. -/
@[expose] noncomputable def ratioInv (t : ℝ) : ℝ := (t + √(t ^ 2 + 4)) / 2

theorem ratioInv_pos (t : ℝ) : 0 < ratioInv t := by
  unfold ratioInv
  by_contra h
  nlinarith [Real.sqrt_nonneg (t ^ 2 + 4), Real.sq_sqrt (show (0 : ℝ) ≤ t ^ 2 + 4 by positivity)]

theorem ratioInv_sub_inv (t : ℝ) : ratioInv t - (ratioInv t)⁻¹ = t := by
  have hp := ratioInv_pos t
  have hq : ratioInv t ^ 2 - t * ratioInv t - 1 = 0 := by
    unfold ratioInv
    linear_combination Real.sq_sqrt (show (0 : ℝ) ≤ t ^ 2 + 4 by positivity) / 4
  field_simp
  linear_combination hq

theorem continuous_ratioInv : Continuous ratioInv := by
  unfold ratioInv
  fun_prop

theorem ratioCoord_eq (a b : ℝ) : ratioCoord a b = a / b - (a / b)⁻¹ := by
  rw [ratioCoord, inv_div]

theorem ratioCoord_eq_iff {a b t : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ratioCoord a b = t ↔ t * a * b = a ^ 2 - b ^ 2 := by
  rw [ratioCoord, div_sub_div _ _ hb ha, div_eq_iff (mul_ne_zero hb ha)]
  constructor <;> intro h <;> linear_combination -h

private theorem ratioCoord_of_div_eq {a b t : ℝ} (h : a / b = ratioInv t) :
    ratioCoord a b = t := by
  rw [ratioCoord_eq, h, ratioInv_sub_inv]

theorem ratioInv_ratioCoord {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ratioInv (ratioCoord a b) = a / b := by
  have hy : 0 < a / b := div_pos ha hb
  rw [ratioCoord_eq, ratioInv, show (a / b - (a / b)⁻¹) ^ 2 + 4 = (a / b + (a / b)⁻¹) ^ 2 by
    field_simp; ring, Real.sqrt_sq (by positivity)]
  ring

theorem ratioCoord_mul {a b c : ℝ} (hc : c ≠ 0) : ratioCoord (c * a) (c * b) = ratioCoord a b := by
  rw [ratioCoord, ratioCoord, mul_div_mul_left _ _ hc, mul_div_mul_left _ _ hc]

theorem continuousOn_ratioCoord {τ : Type*} (a b : τ) :
    ContinuousOn (fun y : τ → ℝ => ratioCoord (y a) (y b)) {y | y a ≠ 0 ∧ y b ≠ 0} := by
  unfold ratioCoord
  exact ((continuous_apply a).continuousOn.div (continuous_apply b).continuousOn
    fun _ (hy : _ ∈ {y : τ → ℝ | y a ≠ 0 ∧ y b ≠ 0}) => hy.2).sub
      ((continuous_apply b).continuousOn.div (continuous_apply a).continuousOn
        fun _ (hy : _ ∈ {y : τ → ℝ | y a ≠ 0 ∧ y b ≠ 0}) => hy.1)

/-! ### Clearing denominators -/

variable {n m : ℕ} {σ : Type*}

/-- `F(t)` with `tᵢ = ρ(numᵢ / denᵢ)`, with denominators cleared:
`∑ₑ coeffₑ(F) ∏ᵢ (numᵢ² − denᵢ²)^{eᵢ} (numᵢ denᵢ)^{dᵢ − eᵢ}`, where `dᵢ = degreeOf i F`. -/
noncomputable def clear (F : MvPolynomial (Fin n) ℝ) (num den : Fin n → MvPolynomial σ ℝ) :
    MvPolynomial σ ℝ :=
  ∑ e ∈ F.support, C (F.coeff e) *
    ∏ i, (num i ^ 2 - den i ^ 2) ^ e i * (num i * den i) ^ (degreeOf i F - e i)

/-- **Clearing denominators.** Where no `numᵢ` or `denᵢ` vanishes, `clear F num den` is
`F(ρ(num / den))` times `∏ᵢ (numᵢ denᵢ)^{dᵢ}`. -/
theorem eval_clear (F : MvPolynomial (Fin n) ℝ) {num den : Fin n → MvPolynomial σ ℝ}
    {y : σ → ℝ} (h : ∀ i, eval y (num i) ≠ 0 ∧ eval y (den i) ≠ 0) :
    eval y (clear F num den) = (∏ i, (eval y (num i) * eval y (den i)) ^ degreeOf i F) *
      eval (fun i => ratioCoord (eval y (num i)) (eval y (den i))) F := by
  conv_rhs => rw [eval_eq']
  rw [mul_sum, clear, map_sum]
  refine sum_congr rfl fun e he => ?_
  simp only [map_mul, eval_C, map_prod, map_pow, map_sub]
  rw [mul_left_comm, ← prod_mul_distrib]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  have hr : eval y (num i) * eval y (den i) * ratioCoord (eval y (num i)) (eval y (den i)) =
      eval y (num i) ^ 2 - eval y (den i) ^ 2 := by
    have := (h i).1
    have := (h i).2
    unfold ratioCoord
    field_simp
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (monomial_le_degreeOf i he)
  rw [← hr, hk, Nat.add_sub_cancel_left, mul_pow, pow_add]
  ring

theorem clear_eq_zero_iff (F : MvPolynomial (Fin n) ℝ) {num den : Fin n → MvPolynomial σ ℝ}
    {y : σ → ℝ} (h : ∀ i, eval y (num i) ≠ 0 ∧ eval y (den i) ≠ 0) :
    eval y (clear F num den) = 0 ↔
      eval (fun i => ratioCoord (eval y (num i)) (eval y (den i))) F = 0 := by
  rw [eval_clear F h, mul_eq_zero, or_iff_right]
  exact prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (mul_ne_zero (h i).1 (h i).2)

/-! ### Isomorphisms through ratio coordinates -/

section Ratio

variable {κ τ : Type*}

/-- The ratio coordinates `ρ(y (num k) / y (den k))` of a point `y`. -/
@[expose] noncomputable def ratioMap (num den : κ → τ) (y : τ → ℝ) : κ → ℝ :=
  fun k => ratioCoord (y (num k)) (y (den k))

/-- A semialgebraic isomorphism onto a semialgebraic set `B` on which the coordinates `num k` and
`den k` are positive, whose inverse is `ratioMap num den`. -/
noncomputable def ofRatio [Finite κ] {A : Set (κ → ℝ)} {B : Set (τ → ℝ)} (hB : IsSemialgebraic B)
    {num den : κ → τ} (hpos : ∀ y ∈ B, ∀ k, 0 < y (num k) ∧ 0 < y (den k))
    (f : (κ → ℝ) → τ → ℝ) (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ y ∈ B, ratioMap num den y ∈ A)
    (hgf : ∀ x ∈ A, ratioMap num den (f x) = x) (hfg : ∀ y ∈ B, f (ratioMap num den y) = y)
    (hfc : Continuous f) : SemialgebraicHomeomorph A B :=
  SemialgebraicHomeomorph.ofInverse f (ratioMap num den) hf hg hgf hfg hfc.continuousOn
    (continuousOn_pi.2 fun k => (continuousOn_ratioCoord (num k) (den k)).mono fun y hy =>
      ⟨(hpos y hy k).1.ne', (hpos y hy k).2.ne'⟩) <| by
    convert (hB.preimage_comp (σ := κ ⊕ τ) Sum.inr).inter (IsSemialgebraic.iInter fun k =>
      IsSemialgebraic.setOf_eq (X (Sum.inl k) * X (Sum.inr (num k)) * X (Sum.inr (den k)))
        (X (Sum.inr (num k)) ^ 2 - X (Sum.inr (den k)) ^ 2)) using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, map_mul,
      map_sub, map_pow, eval_X]
    refine and_congr_right fun hz => ?_
    rw [funext_iff]
    refine forall_congr' fun k => ?_
    exact ratioCoord_eq_iff (hpos _ hz k).1.ne' (hpos _ hz k).2.ne'

end Ratio


/-! ### The binary game -/

section Binary

open DattaBinary (var chain extra)

/-- The point `ratioInv t / (1 + ratioInv t)` of `(0, 1)`, inverse to `u ↦ ρ(u / (1 − u))`. -/
@[expose] noncomputable def toUnit (t : ℝ) : ℝ := ratioInv t / (1 + ratioInv t)

theorem toUnit_pos (t : ℝ) : 0 < toUnit t :=
  div_pos (ratioInv_pos t) (by linarith [ratioInv_pos t])

theorem toUnit_lt_one (t : ℝ) : toUnit t < 1 :=
  (div_lt_one (by linarith [ratioInv_pos t])).2 (by linarith)

theorem ratioCoord_toUnit (t : ℝ) : ratioCoord (toUnit t) (1 - toUnit t) = t :=
  ratioCoord_of_div_eq <| by
    have := ratioInv_pos t
    unfold toUnit
    field_simp; ring

theorem toUnit_ratioCoord {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    toUnit (ratioCoord u (1 - u)) = u := by
  have : 1 - u ≠ 0 := by linarith
  rw [toUnit, ratioInv_ratioCoord h0 (by linarith)]
  field_simp
  ring

theorem continuous_toUnit : Continuous toUnit :=
  continuous_ratioInv.div (continuous_const.add continuous_ratioInv) fun t =>
    (by linarith [ratioInv_pos t] : 1 + ratioInv t ≠ 0)

/-- The system `F` in the box coordinates: `F_j(ρ(u / (1 − u)))` with denominators cleared. -/
noncomputable def clearBox (F : Fin m → MvPolynomial (Fin n) ℝ) (j : Fin m) :
    MvPolynomial (Fin n) ℝ :=
  clear (F j) X fun i => 1 - X i

/-- On the open box, the cleared system vanishes exactly at the images of the zeros of `F`. -/
theorem eval_clearBox_eq_zero_iff (F : Fin m → MvPolynomial (Fin n) ℝ) (j : Fin m)
    {u : Fin n → ℝ} (hu : ∀ i, 0 < u i ∧ u i < 1) :
    eval u (clearBox F j) = 0 ↔ eval (fun i => ratioCoord (u i) (1 - u i)) (F j) = 0 := by
  rw [clearBox, clear_eq_zero_iff]
  · simp
  · intro i
    simp only [eval_X, map_sub, map_one]
    exact ⟨(hu i).1.ne', by linarith [(hu i).2]⟩

/-- The degree bound of the binary game: `3` plus the total degrees of the cleared system. -/
noncomputable def boxDegree (F : Fin m → MvPolynomial (Fin n) ℝ) : ℕ :=
  3 + ∑ j, (clearBox F j).totalDegree

private theorem le_boxDegree (F : Fin m → MvPolynomial (Fin n) ℝ) (j : Fin m) :
    ∀ e ∈ (clearBox F j).support, ∀ i, e i ≤ boxDegree F := fun _ he i =>
  (monomial_le_degreeOf i he).trans <| (degreeOf_le_totalDegree _ i).trans <|
    (single_le_sum (f := fun j => (clearBox F j).totalDegree) (fun _ _ => Nat.zero_le _)
      (mem_univ j)).trans (Nat.le_add_left _ _)

/-- **Datta's binary game for `V`**: the game of `DattaBinary.game` for the cleared system. -/
noncomputable def binaryGame (F : Fin m → MvPolynomial (Fin n) ℝ) :
    CostGame (DattaBinary.Player n (boxDegree F) m) (fun _ => Bool) :=
  DattaBinary.game (clearBox F)

theorem isTotallyMixedNash_binaryGame_iff {F : Fin m → MvPolynomial (Fin n) ℝ} (hn : 0 < n)
    (q : DattaBinary.Player n (boxDegree F) m → ℝ) :
    (binaryGame F).IsTotallyMixedNash (binaryProfile q) ↔
      (∀ v, 0 < q v ∧ q v < 1) ∧
        (∀ j, eval (fun i => ratioCoord (q (var i)) (1 - q (var i))) (F j) = 0) ∧
        ∀ c : Fin n × Fin (boxDegree F), q (chain c) = q (var c.1) ^ (c.2.val + 1) := by
  rw [binaryGame, DattaBinary.isTotallyMixedNash_game_iff (le_boxDegree F)
    ((show 3 ≤ boxDegree F by unfold boxDegree; omega).trans (Nat.le_mul_of_pos_left _ hn))]
  refine and_congr_right fun hq => and_congr_left fun _ => forall_congr' fun j => ?_
  exact eval_clearBox_eq_zero_iff F j fun i => hq _

/-- The player carrying the coordinate `k`: the variable player `i` for `Sum.inl i`, the extra
player `e` for `Sum.inr e`. -/
abbrev binaryPlayer {d : ℕ} : Fin n ⊕ Fin (m - n) → DattaBinary.Player n d m :=
  Sum.elim var extra

/-- The change of variables, from `V × ℝ^{m − n}` to profiles: the variable and extra players play
`toUnit (z k)`, and the chain players the powers of the variables. -/
@[expose] noncomputable def binaryPoint (F : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin n ⊕ Fin (m - n) → ℝ) : DattaBinary.Player n (boxDegree F) m → ℝ
  | .inl i => toUnit (z (.inl i))
  | .inr (.inl c) => toUnit (z (.inl c.1)) ^ (c.2.val + 1)
  | .inr (.inr e) => toUnit (z (.inr e))

theorem ratioMap_binaryProfile {d : ℕ} (q : DattaBinary.Player n d m → ℝ)
    (k : Fin n ⊕ Fin (m - n)) :
    ratioMap (fun k => (⟨binaryPlayer k, true⟩ : Σ _ : DattaBinary.Player n d m, Bool))
      (fun k => ⟨binaryPlayer k, false⟩) (Sigma.uncurry (binaryProfile q)) k =
      ratioCoord (q (binaryPlayer k)) (1 - q (binaryPlayer k)) := by
  simp [ratioMap, binaryProfile, Sigma.uncurry]

private theorem exists_eq_uncurry_binaryProfile {P : Type*} [Fintype P] [DecidableEq P]
    {G : CostGame P fun _ => Bool} {y : (Σ _ : P, Bool) → ℝ}
    (hy : G.IsTotallyMixedNash (Sigma.curry y)) :
    ∃ q, y = Sigma.uncurry (binaryProfile q) :=
  ⟨_, by simpa using congrArg Sigma.uncurry hy.eq_binaryProfile⟩

/-- **The binary change of variables.** For `0 < n`, `V × ℝ^{m − n}` is semialgebraically
isomorphic to the set of totally mixed Nash equilibria of `binaryGame F`. The map is
`binaryProfile ∘ binaryPoint F`; its inverse sends an equilibrium to the ratio coordinates
`ρ(p / (1 − p))` of the probabilities `p` of `true` of the variable and extra players. -/
noncomputable def binaryHomeomorph (F : Fin m → MvPolynomial (Fin n) ℝ) (hn : 0 < n) :
    SemialgebraicHomeomorph
      {z : Fin n ⊕ Fin (m - n) → ℝ | z ∘ Sum.inl ∈ {x | ∀ j, eval x (F j) = 0}}
      {x : (Σ _ : DattaBinary.Player n (boxDegree F) m, Bool) → ℝ |
        (binaryGame F).IsTotallyMixedNash (Sigma.curry x)} :=
  ofRatio (CostGame.isSemialgebraic_setOf_isTotallyMixedNash _)
    (num := fun k => ⟨binaryPlayer k, true⟩) (den := fun k => ⟨binaryPlayer k, false⟩)
    (fun _ hy _ => ⟨hy.2 _ _, hy.2 _ _⟩)
    (fun z => Sigma.uncurry (binaryProfile (binaryPoint F z)))
    (fun z hz => by
      simp only [Set.mem_ofPred_eq, Sigma.curry_uncurry]
      refine (isTotallyMixedNash_binaryGame_iff hn _).2 ⟨?_, fun j => ?_, fun _ => rfl⟩
      · rintro (i | c | e)
        · exact ⟨toUnit_pos _, toUnit_lt_one _⟩
        · exact ⟨pow_pos (toUnit_pos _) _, pow_lt_one₀ (toUnit_pos _).le (toUnit_lt_one _)
            (Nat.succ_ne_zero _)⟩
        · exact ⟨toUnit_pos _, toUnit_lt_one _⟩
      · simp only [binaryPoint, ratioCoord_toUnit]
        exact hz j)
    (fun y hy => by
      obtain ⟨q, rfl⟩ := exists_eq_uncurry_binaryProfile hy
      simp only [Set.mem_ofPred_eq, Sigma.curry_uncurry] at hy ⊢
      intro j
      convert ((isTotallyMixedNash_binaryGame_iff hn q).1 hy).2.1 j using 3
      exact funext fun i => ratioMap_binaryProfile q (.inl i))
    (fun z _ => funext fun k => by
      rw [ratioMap_binaryProfile]
      rcases k with i | e <;> exact ratioCoord_toUnit _)
    (fun y hy => by
      obtain ⟨q, rfl⟩ := exists_eq_uncurry_binaryProfile hy
      simp only [Set.mem_ofPred_eq, Sigma.curry_uncurry] at hy
      obtain ⟨hq, -, hc⟩ := (isTotallyMixedNash_binaryGame_iff hn q).1 hy
      congr 2
      funext v
      rcases v with i | c | e
      · rw [binaryPoint, ratioMap_binaryProfile q (.inl i)]
        exact toUnit_ratioCoord (hq _).1 (hq _).2
      · rw [binaryPoint, ratioMap_binaryProfile q (.inl c.1), hc c]
        exact congrArg (· ^ _) (toUnit_ratioCoord (hq _).1 (hq _).2)
      · rw [binaryPoint, ratioMap_binaryProfile q (.inr e)]
        exact toUnit_ratioCoord (hq _).1 (hq _).2)
    (continuous_pi fun v => by
      have hq : ∀ v, Continuous fun z => binaryPoint F z v := by
        rintro (i | c | e)
        · exact continuous_toUnit.comp (continuous_apply _)
        · exact (continuous_toUnit.comp (continuous_apply _)).pow _
        · exact continuous_toUnit.comp (continuous_apply _)
      obtain ⟨v, b⟩ := v
      cases b
      · exact continuous_const.sub (hq v)
      · exact hq v)

theorem coe_binaryHomeomorph_apply (F : Fin m → MvPolynomial (Fin n) ℝ) (hn : 0 < n)
    (z : {z : Fin n ⊕ Fin (m - n) → ℝ | z ∘ Sum.inl ∈ {x | ∀ j, eval x (F j) = 0}}) :
    ((binaryHomeomorph F hn).toHomeomorph z : _ → ℝ) =
      Sigma.uncurry (binaryProfile (binaryPoint F z)) := by
  simp [binaryHomeomorph, ofRatio]

end Binary


/-! ### The three-player game -/

section Horner

open DattaThree (Who)
open DattaHorner (Strat Coord aCoord bCoord cCoord bobNodes horner shift scale critterWeight)

variable {ι : Type*} [Fintype ι]

/-- The point of the open simplex with ratio coordinates `t`:
`ratioInv (tᵢ) / (1 + ∑ᵢ' ratioInv (tᵢ'))`. -/
@[expose] noncomputable def simplexPoint (t : ι → ℝ) (i : ι) : ℝ :=
  ratioInv (t i) / (1 + ∑ i', ratioInv (t i'))

theorem one_add_sum_ratioInv_pos (t : ι → ℝ) : 0 < 1 + ∑ i, ratioInv (t i) := by
  have := sum_nonneg fun i (_ : i ∈ univ) => (ratioInv_pos (t i)).le
  linarith

theorem simplexPoint_pos (t : ι → ℝ) (i : ι) : 0 < simplexPoint t i :=
  div_pos (ratioInv_pos _) (one_add_sum_ratioInv_pos t)

theorem one_sub_sum_simplexPoint (t : ι → ℝ) :
    1 - ∑ i, simplexPoint t i = (1 + ∑ i, ratioInv (t i))⁻¹ := by
  have := (one_add_sum_ratioInv_pos t).ne'
  simp only [simplexPoint, ← sum_div]
  field_simp
  ring

theorem sum_simplexPoint_lt_one (t : ι → ℝ) : ∑ i, simplexPoint t i < 1 := by
  linarith [one_sub_sum_simplexPoint t, inv_pos.2 (one_add_sum_ratioInv_pos t)]

/-- The ratio coordinates of `c · simplexPoint t`, against the reference weight
`c (1 − ∑ simplexPoint t)`, are `t`. -/
theorem ratioCoord_simplexPoint {c : ℝ} (hc : c ≠ 0) (t : ι → ℝ) (i : ι) :
    ratioCoord (c * simplexPoint t i) (c * (1 - ∑ i', simplexPoint t i')) = t i := by
  rw [ratioCoord_mul hc]
  refine ratioCoord_of_div_eq ?_
  have := (one_add_sum_ratioInv_pos t).ne'
  rw [one_sub_sum_simplexPoint, simplexPoint]
  field_simp

/-- Conversely, positive weights `x` with `∑ x < c` are `c · simplexPoint` of their ratio
coordinates against `c − ∑ x`. -/
theorem mul_simplexPoint_ratioCoord {c : ℝ} {x : ι → ℝ} (hx : ∀ i, 0 < x i) (hs : ∑ i, x i < c)
    (i : ι) : c * simplexPoint (fun i => ratioCoord (x i) (c - ∑ i', x i')) i = x i := by
  have h0 : 0 < c - ∑ i, x i := sub_pos.2 hs
  have hc : c ≠ 0 := by linarith [sum_nonneg fun i (_ : i ∈ univ) => (hx i).le]
  simp only [simplexPoint, ratioInv_ratioCoord (hx _) h0, ← sum_div]
  field_simp
  rw [sub_add_cancel]
  field_simp

theorem continuous_simplexPoint (i : ι) : Continuous fun t : ι → ℝ => simplexPoint t i :=
  (continuous_ratioInv.comp (continuous_apply i)).div
    (continuous_const.add (continuous_finsetSum _ fun i' _ =>
      continuous_ratioInv.comp (continuous_apply i'))) fun t =>
    (one_add_sum_ratioInv_pos t).ne'

/-- The system `F` in the simplex coordinates: `F_j(ρ(x / x₀))`, `x₀ = 1 − ∑ xᵢ`, with
denominators cleared. -/
noncomputable def clearSimplex (F : Fin m → MvPolynomial (Fin n) ℝ) (j : Fin m) :
    MvPolynomial (Fin n) ℝ :=
  clear (F j) X fun _ => 1 - ∑ i, X i

/-- On the open simplex, the cleared system vanishes exactly at the images of the zeros of `F`. -/
theorem eval_clearSimplex_eq_zero_iff (F : Fin m → MvPolynomial (Fin n) ℝ) (j : Fin m)
    {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) (hs : ∑ i, x i < 1) :
    eval x (clearSimplex F j) = 0 ↔
      eval (fun i => ratioCoord (x i) (1 - ∑ i', x i')) (F j) = 0 := by
  rw [clearSimplex, clear_eq_zero_iff]
  · simp
  · intro i
    simp only [eval_X, map_sub, map_one, map_sum]
    exact ⟨(hx i).ne', by linarith⟩

/-- **Datta's three-player game for `V`**: the Horner game of `DattaHorner.game` for the cleared
system. -/
noncomputable def hornerGame (F : Fin m → MvPolynomial (Fin n) ℝ) :
    CostGame Who (fun w => Option (Strat (clearSimplex F) w)) :=
  DattaHorner.game (clearSimplex F)

/-- The equations `j ≥ n`, whose Critter probabilities are free when `m > n`. -/
abbrev Extra (n m : ℕ) : Type := {j : Fin m // n ≤ j.val}

/-- The weight left to Critter's free probabilities and its reference strategy:
`(|Extra n m| + 1) · critterWeight`, where `critterWeight = 1 / (|bobNodes| + m + 1)` is one over
Critter's number of strategies. (This is `(|Extra n m| + 1) / (D + 1)` with `D = chainLength` only
when every cleared equation involves a variable.) -/
noncomputable def freeBudget (F : Fin m → MvPolynomial (Fin n) ℝ) : ℝ :=
  (Fintype.card (Extra n m) + 1) * critterWeight (clearSimplex F)

theorem freeBudget_pos (F : Fin m → MvPolynomial (Fin n) ℝ) : 0 < freeBudget F := by
  unfold freeBudget critterWeight
  positivity

/-- Critter's reference probability, when its probabilities for Bob's nodes and for the equations
`j < n` are `critterWeight G`, one over its number of strategies. -/
theorem one_sub_sum_critter {G : Fin m → MvPolynomial (Fin n) ℝ} {q : Coord G → ℝ}
    (h1 : ∀ ν, q (cCoord (.inl ν)) = critterWeight G)
    (h2 : ∀ j : Fin m, j.val < n → q (cCoord (.inr j)) = critterWeight G) :
    1 - ∑ s, q (cCoord s) =
      (Fintype.card (Extra n m) + 1) * critterWeight G -
        ∑ j : Extra n m, q (cCoord (.inr j.1)) := by
  rw [Fintype.sum_sum_type, ← Fintype.sum_subtype_add_sum_subtype (fun j : Fin m => n ≤ j.val)
    fun j => q (cCoord (.inr j)), sum_congr rfl fun ν _ => h1 ν,
    sum_congr rfl fun (j : {j : Fin m // ¬n ≤ j.val}) _ => h2 j.1 (not_le.1 j.2)]
  have hcard := Fintype.sum_subtype_add_sum_subtype (fun j : Fin m => n ≤ j.val) fun _ => (1 : ℝ)
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, Fintype.card_fin, Fintype.card_coe]
    at hcard ⊢
  have hw : critterWeight G * (#(bobNodes G) + m + 1) = 1 := by
    unfold critterWeight
    field_simp
  linear_combination -hw - critterWeight G * hcard

/-- The coordinate `ρ(num / den)` of the change of variables: Alice's `xᵢ` against her reference
probability, and Critter's free probabilities against its reference probability. -/
@[expose] def hornerNum (F : Fin m → MvPolynomial (Fin n) ℝ) :
    Fin n ⊕ Extra n m → Σ w, Option (Strat (clearSimplex F) w)
  | .inl i => ⟨.alice, some i⟩
  | .inr j => ⟨.critter, some (.inr j.1)⟩

/-- The reference coordinates against which `hornerNum` is read. -/
@[expose] def hornerDen (F : Fin m → MvPolynomial (Fin n) ℝ) :
    Fin n ⊕ Extra n m → Σ w, Option (Strat (clearSimplex F) w)
  | .inl _ => ⟨.alice, none⟩
  | .inr _ => ⟨.critter, none⟩

/-- The change of variables, from `V × ℝ^{Extra n m}` to profiles: Alice plays `simplexPoint` of
the first coordinates, Bob the rescaled Horner values, and Critter `critterWeight` on its fixed
strategies and `freeBudget F · simplexPoint` of the last coordinates on its free ones. -/
@[expose] noncomputable def hornerPoint (F : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin n ⊕ Extra n m → ℝ) :
    Coord (clearSimplex F) → ℝ
  | ⟨.alice, i⟩ => simplexPoint (z ∘ Sum.inl) i
  | ⟨.bob, ⟨⟨j, p⟩, _⟩⟩ => (horner (clearSimplex F j) (simplexPoint (z ∘ Sum.inl)) p.var p.expo -
      shift (clearSimplex F) j) / scale (clearSimplex F) j
  | ⟨.critter, .inl _⟩ => critterWeight (clearSimplex F)
  | ⟨.critter, .inr j⟩ => if h : n ≤ j.val then freeBudget F * simplexPoint (z ∘ Sum.inr) ⟨j, h⟩
      else critterWeight (clearSimplex F)

theorem ratioMap_simplexProfile_inl {F : Fin m → MvPolynomial (Fin n) ℝ}
    (q : Coord (clearSimplex F) → ℝ) (i : Fin n) :
    ratioMap (hornerNum F) (hornerDen F) (Sigma.uncurry (simplexProfile q)) (.inl i) =
      ratioCoord (q (aCoord i)) (1 - ∑ i', q (aCoord i')) :=
  rfl

theorem ratioMap_simplexProfile_inr {F : Fin m → MvPolynomial (Fin n) ℝ}
    (q : Coord (clearSimplex F) → ℝ) (j : Extra n m) :
    ratioMap (hornerNum F) (hornerDen F) (Sigma.uncurry (simplexProfile q)) (.inr j) =
      ratioCoord (q (cCoord (.inr j.1))) (1 - ∑ s, q (cCoord s)) :=
  rfl

private theorem exists_eq_uncurry_simplexProfile {P : Type*} {T : P → Type*} [Fintype P]
    [DecidableEq P] [∀ p, Fintype (T p)] {G : CostGame P fun p => Option (T p)}
    {y : (Σ p, Option (T p)) → ℝ} (hy : G.IsTotallyMixedNash (Sigma.curry y)) :
    ∃ q, y = Sigma.uncurry (simplexProfile q) :=
  ⟨_, by simpa using congrArg Sigma.uncurry hy.eq_simplexProfile⟩

/-- Critter's reference probability at `hornerPoint F z`. -/
theorem one_sub_sum_hornerPoint (F : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin n ⊕ Extra n m → ℝ) :
    1 - ∑ s, hornerPoint F z (cCoord s) =
      freeBudget F * (1 - ∑ j, simplexPoint (z ∘ Sum.inr) j) := by
  rw [one_sub_sum_critter (fun _ => rfl) fun j hj => dite_eq_right (not_le.2 hj), freeBudget,
    mul_sub, mul_one, mul_sum]
  exact congrArg _ (sum_congr rfl fun j _ => by
    simp only [hornerPoint, dite_eq_left j.2, freeBudget])

/-- **The three-player change of variables.** `V × ℝ^{Extra n m}` is semialgebraically
isomorphic to the set of totally mixed Nash equilibria of `hornerGame F`. The map is
`simplexProfile ∘ hornerPoint F`; its inverse sends an equilibrium to the ratio coordinates of
Alice's probabilities against her reference probability, and of Critter's free probabilities (for
the equations `j ≥ n`) against its reference probability. When `m ≤ n`, `Extra n m` is empty. -/
noncomputable def hornerHomeomorph (F : Fin m → MvPolynomial (Fin n) ℝ) :
    SemialgebraicHomeomorph {z : Fin n ⊕ Extra n m → ℝ | z ∘ Sum.inl ∈ {x | ∀ j, eval x (F j) = 0}}
      {x : (Σ w, Option (Strat (clearSimplex F) w)) → ℝ |
        (hornerGame F).IsTotallyMixedNash (Sigma.curry x)} :=
  ofRatio (CostGame.isSemialgebraic_setOf_isTotallyMixedNash _) (num := hornerNum F)
    (den := hornerDen F)
    (fun _ hy k => ⟨hy.2 _ _, hy.2 _ _⟩)
    (fun z => Sigma.uncurry (simplexProfile (hornerPoint F z)))
    (fun z hz => by
      simp only [Set.mem_ofPred_eq, Sigma.curry_uncurry]
      refine (DattaHorner.isTotallyMixedNash_game_iff _).2 ⟨⟨fun i => simplexPoint_pos _ i,
        sum_simplexPoint_lt_one _, fun j => ?_⟩, fun _ _ _ => rfl, fun _ => rfl,
        fun j hj => dite_eq_right (not_le.2 hj), fun j => ?_, ?_⟩
      · refine (eval_clearSimplex_eq_zero_iff F j (simplexPoint_pos _)
          (sum_simplexPoint_lt_one _)).2 ?_
        have h := fun i => ratioCoord_simplexPoint one_ne_zero (z ∘ Sum.inl) i
        simp only [one_mul] at h
        change eval (fun i => ratioCoord (simplexPoint (z ∘ Sum.inl) i)
          (1 - ∑ i', simplexPoint (z ∘ Sum.inl) i')) (F j) = 0
        simp only [h]
        exact hz j
      · by_cases h : n ≤ j.val
        · simp only [hornerPoint, dite_eq_left h]
          exact mul_pos (freeBudget_pos F) (simplexPoint_pos _ _)
        · simp only [hornerPoint, dite_eq_right h, critterWeight]
          positivity
      · have := one_sub_sum_hornerPoint F z
        have := mul_pos (freeBudget_pos F) (sub_pos.2 (sum_simplexPoint_lt_one (z ∘ Sum.inr)))
        linarith)
    (fun y hy => by
      obtain ⟨q, rfl⟩ := exists_eq_uncurry_simplexProfile hy
      simp only [Set.mem_ofPred_eq, Sigma.curry_uncurry] at hy ⊢
      obtain ⟨⟨ha, has, hF⟩, -⟩ := (DattaHorner.isTotallyMixedNash_game_iff q).1 hy
      intro j
      exact (eval_clearSimplex_eq_zero_iff F j ha has).1 (hF j))
    (fun z _ => funext fun k => by
      rcases k with i | j
      · rw [ratioMap_simplexProfile_inl]
        have := ratioCoord_simplexPoint one_ne_zero (z ∘ Sum.inl) i
        simp only [one_mul] at this
        exact this
      · rw [ratioMap_simplexProfile_inr, one_sub_sum_hornerPoint]
        simp only [hornerPoint, dite_eq_left j.2, freeBudget]
        exact ratioCoord_simplexPoint (freeBudget_pos F).ne' _ _)
    (fun y hy => by
      obtain ⟨q, rfl⟩ := exists_eq_uncurry_simplexProfile hy
      simp only [Set.mem_ofPred_eq, Sigma.curry_uncurry] at hy
      obtain ⟨⟨ha, has, -⟩, hb, hc1, hc2, hcpos, hcs⟩ :=
        (DattaHorner.isTotallyMixedNash_game_iff q).1 hy
      have hA : simplexPoint (ratioMap (hornerNum F) (hornerDen F)
          (Sigma.uncurry (simplexProfile q)) ∘ Sum.inl) = fun i => q (aCoord i) :=
        funext fun i => by
        have := mul_simplexPoint_ratioCoord (c := 1) ha has i
        rw [one_mul] at this
        exact this
      have hC := one_sub_sum_critter hc1 hc2
      congr 2
      funext v
      obtain ⟨_ | _ | _, t⟩ := v
      · exact congrFun hA t
      · obtain ⟨⟨j, p⟩, h⟩ := t
        simp only [hornerPoint, hA]
        exact (hb j p h).symm
      · rcases t with ν | j
        · exact (hc1 ν).symm
        · by_cases h : n ≤ j.val
          · simp only [hornerPoint, dite_eq_left h, freeBudget]
            have hs : ∑ j : Extra n m, q (cCoord (.inr j.1)) <
                (Fintype.card (Extra n m) + 1) * critterWeight (clearSimplex F) := by
              linarith
            convert mul_simplexPoint_ratioCoord (fun j : Extra n m => hcpos j.1) hs ⟨j, h⟩
              using 3
            funext j'
            rw [Function.comp_apply, ratioMap_simplexProfile_inr, hC]
          · simp only [hornerPoint, dite_eq_right h]
            exact (hc2 j (not_le.1 h)).symm)
    (continuous_pi fun v => by
      have hA : Continuous fun z : Fin n ⊕ Extra n m → ℝ => simplexPoint (z ∘ Sum.inl) :=
        continuous_pi fun i => (continuous_simplexPoint i).comp
          (continuous_pi fun i => continuous_apply _)
      have hq : ∀ v, Continuous fun z => hornerPoint F z v := by
        rintro ⟨_ | _ | _, t⟩
        · exact (continuous_apply t).comp hA
        · obtain ⟨⟨j, p⟩, h⟩ := t
          exact (((DattaHorner.continuous_horner _ _ _).comp hA).sub continuous_const).div_const _
        · rcases t with ν | j
          · exact continuous_const
          · by_cases h : n ≤ j.val
            · simp only [hornerPoint, dite_eq_left h]
              exact continuous_const.mul ((continuous_simplexPoint _).comp
                (continuous_pi fun i => continuous_apply _))
            · simp only [hornerPoint, dite_eq_right h]
              exact continuous_const
      obtain ⟨w, _ | t⟩ := v
      · exact continuous_const.sub (continuous_finsetSum _ fun t _ => hq ⟨w, t⟩)
      · exact hq ⟨w, t⟩)

theorem coe_hornerHomeomorph_apply (F : Fin m → MvPolynomial (Fin n) ℝ)
    (z : {z : Fin n ⊕ Extra n m → ℝ | z ∘ Sum.inl ∈ {x | ∀ j, eval x (F j) = 0}}) :
    ((hornerHomeomorph F).toHomeomorph z : _ → ℝ) =
      Sigma.uncurry (simplexProfile (hornerPoint F z)) := by
  simp [hornerHomeomorph, ofRatio]

end Horner


/-! ### Theorem 1 -/

open DattaThree (Who)

/-- A real algebraic set is semialgebraic. -/
theorem isSemialgebraic_setOf_eval_eq_zero (F : Fin m → MvPolynomial (Fin n) ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | ∀ j, eval x (F j) = 0} := by
  rw [Set.ofPred_forall]
  exact IsSemialgebraic.iInter fun j => IsSemialgebraic.setOf_eq_zero (F j)

/-- **Theorem 1 of [Datta2003], three-player form, with an explicit game.** The real algebraic
set `V = {x | ∀ j, F_j(x) = 0}` is stably isomorphic to the set of totally mixed Nash equilibria
of the three-player game `hornerGame F`: `V × ℝ^{Extra n m}` is semialgebraically isomorphic to it
(`hornerHomeomorph`), and `V × ℝ^{Extra n m}` projects to `V`. -/
theorem stablyIsomorphic_hornerGame (F : Fin m → MvPolynomial (Fin n) ℝ) :
    StablyIsomorphic {x : Fin n → ℝ | ∀ j, eval x (F j) = 0}
      {x : (Σ w, Option (DattaHorner.Strat (clearSimplex F) w)) → ℝ |
        (hornerGame F).IsTotallyMixedNash (Sigma.curry x)} :=
  (StablyIsomorphic.prod (isSemialgebraic_setOf_eval_eq_zero F) (Extra n m)).symm.trans
    (.of_homeomorph (hornerHomeomorph F))

/-- **Theorem 1 of [Datta2003], binary form, with an explicit game**, for `0 < n`: `V` is stably
isomorphic to the set of totally mixed Nash equilibria of `binaryGame F`. -/
theorem stablyIsomorphic_binaryGame (F : Fin m → MvPolynomial (Fin n) ℝ) (hn : 0 < n) :
    StablyIsomorphic {x : Fin n → ℝ | ∀ j, eval x (F j) = 0}
      {x : (Σ _ : DattaBinary.Player n (boxDegree F) m, Bool) → ℝ |
        (binaryGame F).IsTotallyMixedNash (Sigma.curry x)} :=
  (StablyIsomorphic.prod_fin _ (m - n)).symm.trans (.of_homeomorph (binaryHomeomorph F hn))

/-- Adding a dummy variable: `V ⊆ ℝⁿ` is stably isomorphic to `V × ℝ ⊆ ℝⁿ⁺¹`, the zero set of the
same polynomials in `n + 1` variables. -/
theorem stablyIsomorphic_rename_castSucc (F : Fin m → MvPolynomial (Fin n) ℝ) :
    StablyIsomorphic {x : Fin n → ℝ | ∀ j, eval x (F j) = 0}
      {x : Fin (n + 1) → ℝ | ∀ j, eval x (rename Fin.castSucc (F j)) = 0} := by
  have hset : {y : Fin (n + 1) → ℝ | y ∘ finSumFinEquiv ∈
      (fun x : Fin n ⊕ Fin 1 → ℝ => x ∘ Sum.inl) ⁻¹' {x | ∀ j, eval x (F j) = 0}} =
      {x : Fin (n + 1) → ℝ | ∀ j, eval x (rename Fin.castSucc (F j)) = 0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, eval_rename]; rfl
  exact (StablyIsomorphic.prod_fin _ 1).symm.trans (.of_homeomorph
    (hset ▸ SemialgebraicHomeomorph.reindex finSumFinEquiv
      ((isSemialgebraic_setOf_eval_eq_zero F).preimage_comp (σ := Fin n ⊕ Fin 1) Sum.inl)))

/-- **Theorem 1 of [Datta2003]** (arXiv:math/0301001, p. 1): every real algebraic set
`V = {x ∈ ℝⁿ | F₀(x) = ⋯ = F_{m-1}(x) = 0}` is stably isomorphic to the set of totally mixed Nash
equilibria of a game with the three players `Who` (Alice, Bob and Critter), and to that of a game
in which every player has two pure strategies. Every player has a pure strategy, and the binary
game has a player, so an empty `V` is not matched by a degenerate game. The isomorphisms are
explicit (`hornerHomeomorph`, `binaryHomeomorph`), with the change of variables repaired as
described in the module documentation. For `n = 0` the binary form first adds a dummy variable
(`stablyIsomorphic_rename_castSucc`). -/
theorem universality (F : Fin m → MvPolynomial (Fin n) ℝ) :
    (∃ (S : Who → Type) (_ : ∀ w, Fintype (S w)) (_ : ∀ w, DecidableEq (S w))
        (_ : ∀ w, Nonempty (S w)) (G : CostGame Who S),
        StablyIsomorphic {x : Fin n → ℝ | ∀ j, eval x (F j) = 0}
          {x : (Σ w, S w) → ℝ | G.IsTotallyMixedNash (Sigma.curry x)}) ∧
      ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (_ : Nonempty P)
        (G : CostGame P fun _ => Bool),
        StablyIsomorphic {x : Fin n → ℝ | ∀ j, eval x (F j) = 0}
          {x : (Σ _ : P, Bool) → ℝ | G.IsTotallyMixedNash (Sigma.curry x)} := by
  refine ⟨⟨_, inferInstance, inferInstance, fun _ => ⟨none⟩, hornerGame F,
    stablyIsomorphic_hornerGame F⟩, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨_, inferInstance, inferInstance, ⟨.inl 0⟩, binaryGame fun j => rename Fin.castSucc (F j),
      (stablyIsomorphic_rename_castSucc F).trans (stablyIsomorphic_binaryGame _ Nat.one_pos)⟩
  · exact ⟨_, inferInstance, inferInstance, ⟨.inl ⟨0, hn⟩⟩, binaryGame F,
      stablyIsomorphic_binaryGame F hn⟩

end Cslib.GameTheory.DattaUniversality
