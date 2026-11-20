/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Universality.SimplexGame
public import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A three-player universality game

An original three-player variant of the construction in the proof of Theorem 5 of [Datta2003]
(statement p. 4, proof pp. 4–6). Let
`F₀, …, F_{m-1}` be polynomials in `n` variables whose degree in each variable is at most `d`. There
is a game with three players, Alice, Bob and Critter, with `n + 1`, `(d + 1)ⁿ + 1` and
`(d + 1)ⁿ + m + 1` pure strategies, whose totally mixed Nash equilibria are the points `x` of the
open simplex `{x | 0 < xᵢ, ∑ xᵢ < 1}` with `F_j(x) = 0`, encoded together with the monomials `xᵉ`
and, when `m > n`, `m - n` free probabilities of Critter.

## The construction

Every player has a reference strategy (`none`, `CostGame.simplexGame`). The non-reference
strategies (`DattaThree.Strat`) are:
* for Alice, `i < n`, whose probability is `xᵢ`;
* for Bob, the exponent vectors `e ∈ {0, …, d}ⁿ`, whose probability stands for `xᵉ / K` with
  `K = (d + 1)ⁿ + 1` (`bobScale`);
* for Critter, the exponent vectors `e` and the equations `j < m`.

Each player's indifference equations involve only the other two players:
* Critter's equation for `e` is the **monomial chain** `K b_e = a_l · K b_{e - 1_l}`, where `l` is a
  variable with `e_l ≥ 1`, and `K b_0 = 1` (`chainEq`). By induction on the total degree they
  force `b_e = xᵉ / K`.
* Critter's equation for `j` is `F_j` with each monomial `xᵉ` replaced by `K b_e` (`encode`),
  which is affine in Bob's block.
* Bob's equation for `e` and, for `j < min(m, n)`, Alice's equation for `j` fix Critter's
  probability of the strategy for `e`, resp. `j`, at `1 / (number of Critter's strategies)`
  (`critterWeight`). Alice's remaining equations are `0`.

**Differences from the source.** The monomial table is this library's, not Datta's. Datta
writes each `F_j` by Horner's rule as a chain of bilinear equations, one per step, with affine
rescalings of Bob's coordinates, which gives the strategy counts `n + 1`, `D − m + 1` and `D + 1`
with `D = −1 + ∑ⱼ ∏ᵢ (1 + d_ij)`. Here the `F_j` share one table of monomials, so the scaling
`1 / K` keeps Bob's probabilities in the open simplex without affine shifts. The counts differ
from the paper's; they do not matter for universality. When every `F_j` has degree `d` in every
variable, write `N = (d + 1)ⁿ`. Then the paper gives Bob and Critter `m (N − 1)` and `m N`
strategies, and this game gives them `N + 1` and `N + m + 1`. So this game is smaller exactly when
`(m − 1) N > m + 1`; it is larger for one equation, and for two linear equations in one variable.
On sparse systems it can be exponentially larger. Datta fixes Critter's probabilities at
`1 / D` (p. 6), which leaves Critter's reference strategy with probability `0` when `m ≤ n`;
dividing by the number of Critter's strategies avoids this. The exact Horner construction and
counts stay open in #6701.

## Main definitions

* `Cslib.GameTheory.DattaThree.game F`: the game.

## Main results

* `Cslib.GameTheory.DattaThree.isTotallyMixedNash_game_iff`: its totally mixed Nash equilibria.
* `Cslib.GameTheory.DattaThree.card_strategies`: the numbers of pure strategies.

## References

* [Datta2003]
-/

public section

namespace Cslib.GameTheory.DattaThree

open MvPolynomial Finset Function

/-- The three players. -/
inductive Who
  | alice
  | bob
  | critter
  deriving DecidableEq

instance : Fintype Who := ⟨{.alice, .bob, .critter}, fun w => by cases w <;> simp⟩

/-- Exponent vectors of `n` variables with entries at most `d`. -/
abbrev Expo (n d : ℕ) : Type := Fin n → Fin (d + 1)

/-- The non-reference pure strategies of each player. -/
abbrev Strat (n d m : ℕ) : Who → Type
  | .alice => Fin n
  | .bob => Expo n d
  | .critter => Expo n d ⊕ Fin m

variable {n d m : ℕ}

instance instFintypeStrat : ∀ w, Fintype (Strat n d m w)
  | .alice => inferInstanceAs (Fintype (Fin n))
  | .bob => inferInstanceAs (Fintype (Expo n d))
  | .critter => inferInstanceAs (Fintype (Expo n d ⊕ Fin m))

instance instDecidableEqStrat : ∀ w, DecidableEq (Strat n d m w)
  | .alice => inferInstanceAs (DecidableEq (Fin n))
  | .bob => inferInstanceAs (DecidableEq (Expo n d))
  | .critter => inferInstanceAs (DecidableEq (Expo n d ⊕ Fin m))

/-- The coordinates of a profile: one per non-reference strategy. -/
abbrev Coord (n d m : ℕ) : Type := Σ w, Strat n d m w

/-- Alice's coordinate `i`, standing for `xᵢ`. -/
abbrev aCoord (i : Fin n) : Coord n d m := ⟨.alice, i⟩

/-- Bob's coordinate `e`, standing for `xᵉ / K`. -/
abbrev bCoord (e : Expo n d) : Coord n d m := ⟨.bob, e⟩

/-- Critter's coordinate `s`. -/
abbrev cCoord (s : Expo n d ⊕ Fin m) : Coord n d m := ⟨.critter, s⟩

/-- The scale `K = (d + 1)ⁿ + 1` of Bob's coordinates: Bob's number of pure strategies. -/
noncomputable abbrev bobScale (n d : ℕ) : ℝ := (d + 1 : ℝ) ^ n + 1

/-- The probability `1 / ((d + 1)ⁿ + m + 1)` at which Critter's coordinates are fixed: one over
Critter's number of pure strategies. -/
noncomputable abbrev critterWeight (n d m : ℕ) : ℝ := 1 / ((d + 1 : ℝ) ^ n + m + 1)

/-- The monomial `xᵉ = ∏ xᵢ ^ eᵢ`. -/
@[expose] noncomputable def expoPow (x : Fin n → ℝ) (e : Expo n d) : ℝ := ∏ i, x i ^ (e i : ℕ)

/-- `e` with entry `l` lowered by one. -/
def lower (e : Expo n d) (l : Fin n) : Expo n d :=
  update e l ⟨(e l : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) (e l).2⟩

/-- The total degree of `e`. -/
def weight (e : Expo n d) : ℕ := ∑ i, (e i : ℕ)

/-- Critter's monomial chain equation for `e`: `K b_e - K a_l b_{e - 1_l}` for a variable `l` with
`e_l ≥ 1`, and `K b_0 - 1`. -/
noncomputable def chainEq (e : Expo n d) : MvPolynomial (Coord n d m) ℝ :=
  if h : ∃ l, (e l : ℕ) ≠ 0 then
    C (bobScale n d) * X (bCoord e) -
      C (bobScale n d) * (X (aCoord h.choose) * X (bCoord (lower e h.choose)))
  else C (bobScale n d) * X (bCoord e) - 1

/-- The exponent vector of a monomial, with entries cut off at `d`. -/
def toExpo (s : Fin n →₀ ℕ) : Expo n d := fun i => ⟨min (s i) d, by omega⟩

/-- The encoding of `F` in Bob's block: each monomial `xˢ` becomes `K b_s`. -/
noncomputable def encode (F : MvPolynomial (Fin n) ℝ) : MvPolynomial (Coord n d m) ℝ :=
  ∑ s ∈ F.support, C (F.coeff s * bobScale n d) * X (bCoord (toExpo s))

/-- The indifference equations of the three players. -/
noncomputable def equation (F : Fin m → MvPolynomial (Fin n) ℝ) :
    ∀ w, Strat n d m w → MvPolynomial (Coord n d m) ℝ
  | .alice, i => if h : i.val < m then X (cCoord (.inr ⟨i, h⟩)) - C (critterWeight n d m) else 0
  | .bob, e => X (cCoord (.inl e)) - C (critterWeight n d m)
  | .critter, .inl e => chainEq e
  | .critter, .inr j => encode (F j)

/-- **The three-player game** for the system `F`. -/
noncomputable def game (F : Fin m → MvPolynomial (Fin n) ℝ) :
    CostGame Who (fun w => Option (Strat n d m w)) :=
  CostGame.simplexGame (equation (d := d) F)

/-- Alice, Bob and Critter have `n + 1`, `(d + 1)ⁿ + 1` and `(d + 1)ⁿ + m + 1` pure strategies. -/
theorem card_strategies :
    Fintype.card (Option (Strat n d m .alice)) = n + 1 ∧
      Fintype.card (Option (Strat n d m .bob)) = (d + 1) ^ n + 1 ∧
      Fintype.card (Option (Strat n d m .critter)) = (d + 1) ^ n + m + 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Fintype.card_option, Fintype.card_sum]

/-! ### The monomial chain -/

theorem bobScale_pos : 0 < bobScale n d := by positivity

theorem critterWeight_pos : 0 < critterWeight n d m := by positivity

theorem expoPow_lower (x : Fin n → ℝ) {e : Expo n d} {l : Fin n} (hl : (e l : ℕ) ≠ 0) :
    expoPow x e = x l * expoPow x (lower e l) := by
  unfold expoPow lower
  rw [← mul_prod_erase _ _ (mem_univ l), ← mul_prod_erase _ _ (mem_univ l)]
  rw [update_self, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hl)]
  congr 1
  refine prod_congr rfl fun i hi => ?_
  rw [update_of_ne (ne_of_mem_erase hi)]

theorem weight_lower_lt {e : Expo n d} {l : Fin n} (hl : (e l : ℕ) ≠ 0) :
    weight (lower e l) < weight e := by
  unfold weight lower
  refine sum_lt_sum (fun i _ => ?_) ⟨l, mem_univ l, ?_⟩
  · by_cases hi : i = l
    · subst hi
      simp
    · simp [update_of_ne hi]
  · simp only [update_self]
    omega

theorem expoPow_of_forall_eq_zero (x : Fin n → ℝ) {e : Expo n d} (he : ∀ l, (e l : ℕ) = 0) :
    expoPow x e = 1 := by
  simp [expoPow, he]

/-- The monomial chain forces `K b_e = xᵉ`. -/
theorem bobScale_mul_eq_expoPow {q : Coord n d m → ℝ}
    (h : ∀ e, eval q (chainEq (m := m) e) = 0) (e : Expo n d) :
    bobScale n d * q (bCoord e) = expoPow (fun i => q (aCoord i)) e := by
  induction hk : weight e using Nat.strong_induction_on generalizing e with
  | _ k ih =>
    have he := h e
    unfold chainEq at he
    split_ifs at he with hne
    · have hl := hne.choose_spec
      have hrec := ih _ (hk ▸ weight_lower_lt hl) (lower e hne.choose) rfl
      rw [expoPow_lower _ hl, ← hrec]
      simp only [map_sub, map_mul, eval_C, eval_X] at he
      linarith
    · simp only [not_exists, not_not] at hne
      rw [expoPow_of_forall_eq_zero _ hne]
      simp only [map_sub, map_mul, eval_C, eval_X, map_one] at he
      linarith

theorem eval_chainEq_of_eq {q : Coord n d m → ℝ}
    (h : ∀ e, bobScale n d * q (bCoord e) = expoPow (fun i => q (aCoord i)) e) (e : Expo n d) :
    eval q (chainEq (m := m) e) = 0 := by
  unfold chainEq
  split_ifs with hne
  · simp only [map_sub, map_mul, eval_C, eval_X]
    linear_combination h e - q (aCoord hne.choose) * h (lower e hne.choose) +
      expoPow_lower (fun i => q (aCoord i)) hne.choose_spec
  · simp only [not_exists, not_not] at hne
    simp only [map_sub, map_mul, eval_C, eval_X, map_one]
    linear_combination h e + expoPow_of_forall_eq_zero (fun i => q (aCoord i)) hne

/-- Under the monomial chain, the encoding of `F` evaluates to `F(x)`. -/
theorem eval_encode {F : MvPolynomial (Fin n) ℝ} (hF : ∀ s ∈ F.support, ∀ i, s i ≤ d)
    {q : Coord n d m → ℝ}
    (h : ∀ e, bobScale n d * q (bCoord e) = expoPow (fun i => q (aCoord i)) e) :
    eval q (encode F) = eval (fun i => q (aCoord i)) F := by
  rw [encode, map_sum, eval_eq']
  refine sum_congr rfl fun s hs => ?_
  simp only [map_mul, eval_C, eval_X]
  rw [mul_assoc, h, expoPow]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  simp [toExpo, min_eq_left (hF s hs i)]

/-! ### Shape of the equations -/

private theorem C_mem_supported {s : Set (Coord n d m)} (c : ℝ) :
    MvPolynomial.C c ∈ supported ℝ s := by
  rw [← algebraMap_eq]
  exact Subalgebra.algebraMap_mem _ c

/-- Each player's equations only involve the other players. -/
theorem mem_supported_equation (F : Fin m → MvPolynomial (Fin n) ℝ) (w : Who)
    (t : Strat n d m w) : equation (d := d) F w t ∈ supported ℝ {v | v.1 ≠ w} := by
  have hX : ∀ v : Coord n d m, v.1 ≠ w → X v ∈ supported ℝ {v : Coord n d m | v.1 ≠ w} :=
    fun v hv => (X_mem_supported).2 hv
  rcases w with _ | _ | _
  · simp only [equation]
    split_ifs
    · exact sub_mem (hX _ nofun) (C_mem_supported _)
    · exact zero_mem _
  · exact sub_mem (hX _ nofun) (C_mem_supported _)
  · rcases t with e | j
    · simp only [equation, chainEq]
      split_ifs
      · exact sub_mem (mul_mem (C_mem_supported _) (hX _ nofun))
          (mul_mem (C_mem_supported _) (mul_mem (hX _ nofun) (hX _ nofun)))
      · exact sub_mem (mul_mem (C_mem_supported _) (hX _ nofun)) (one_mem _)
    · exact sum_mem fun s _ => mul_mem (C_mem_supported _) (hX _ nofun)

theorem notMem_vars_equation (F : Fin m → MvPolynomial (Fin n) ℝ) (w : Who)
    (t : Strat n d m w) : ∀ v ∈ (equation (d := d) F w t).vars, v.1 ≠ w := fun _ hv =>
  (mem_supported.1 (mem_supported_equation F w t)) hv

theorem isBlockAffine_equation (F : Fin m → MvPolynomial (Fin n) ℝ) (w : Who)
    (t : Strat n d m w) : IsBlockAffine (equation (d := d) F w t) := by
  have hCX : ∀ (c : ℝ) (v : Coord n d m), IsBlockAffine (C c * X v) := fun c v =>
    (IsBlockAffine.C c).mul (IsBlockAffine.X v) fun w hw => by rw [vars_C] at hw; simp at hw
  rcases w with _ | _ | _
  · simp only [equation]
    split_ifs
    · exact (IsBlockAffine.X _).sub (IsBlockAffine.C _)
    · exact IsBlockAffine.zero
  · exact (IsBlockAffine.X _).sub (IsBlockAffine.C _)
  · rcases t with e | j
    · simp only [equation, chainEq]
      split_ifs
      · refine (hCX _ _).sub ((IsBlockAffine.C _).mul ((IsBlockAffine.X _).mul
          (IsBlockAffine.X _) ?_) fun v hv => by rw [vars_C] at hv; simp at hv)
        simp [vars_X]
      · exact (hCX _ _).sub (by simpa using IsBlockAffine.C (T := Strat n d m) 1)
    · exact IsBlockAffine.sum fun s _ => hCX _ _

/-! ### The totally mixed equilibria -/

theorem expoPow_pos {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) (e : Expo n d) : 0 < expoPow x e :=
  prod_pos fun i _ => pow_pos (hx i) _

theorem expoPow_le_one {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (e : Expo n d) : expoPow x e ≤ 1 :=
  prod_le_one₀ (fun i _ => pow_nonneg (hx i) _) fun i _ => pow_le_one₀ (hx i) (hx1 i)

/-- Bob's weights `xᵉ / K` sum to less than `1` on the open simplex. -/
theorem sum_expoPow_div_lt_one {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) (hx1 : ∑ i, x i < 1) :
    ∑ e : Expo n d, expoPow x e / bobScale n d < 1 := by
  have hle : ∀ i, x i ≤ 1 := fun i =>
    (single_le_sum (fun j _ => (hx j).le) (mem_univ i)).trans hx1.le
  calc ∑ e : Expo n d, expoPow x e / bobScale n d
      ≤ ∑ _e : Expo n d, 1 / bobScale n d :=
        sum_le_sum fun e _ => div_le_div_of_nonneg_right
          (expoPow_le_one (fun i => (hx i).le) hle e) bobScale_pos.le
    _ = (d + 1 : ℝ) ^ n / bobScale n d := by
        simp [div_eq_mul_inv]
    _ < 1 := by
        rw [div_lt_one bobScale_pos]
        linarith

/-- **The three-player construction** (original variant of the proof of Theorem 5 of
[Datta2003]). If each `F j` has degree at most `d` in every variable, the totally mixed Nash
equilibria of the three-player game are the profiles `simplexProfile q` such that:
* Alice's weights `x = q ∘ aCoord` lie in the open simplex and solve every `F j = 0`;
* Bob plays each monomial `xᵉ / K`;
* Critter plays `1 / (number of Critter's strategies)` on its strategies for the exponent vectors
  and for the equations `j < n`;
* Critter's remaining weights are positive, and all of Critter's weights sum to less than `1`. -/
theorem isTotallyMixedNash_game_iff {F : Fin m → MvPolynomial (Fin n) ℝ}
    (hF : ∀ j, ∀ s ∈ (F j).support, ∀ i, s i ≤ d) (q : Coord n d m → ℝ) :
    (game (d := d) F).IsTotallyMixedNash (simplexProfile q) ↔
      ((∀ i, 0 < q (aCoord i)) ∧ ∑ i, q (aCoord i) < 1 ∧
        ∀ j, eval (fun i => q (aCoord i)) (F j) = 0) ∧
      (∀ e, q (bCoord e) = expoPow (fun i => q (aCoord i)) e / bobScale n d) ∧
      (∀ e, q (cCoord (.inl e)) = critterWeight n d m) ∧
      (∀ j : Fin m, j.val < n → q (cCoord (.inr j)) = critterWeight n d m) ∧
      (∀ j, 0 < q (cCoord (.inr j))) ∧ ∑ s, q (cCoord s) < 1 := by
  rw [game, CostGame.isTotallyMixedNash_simplexGame_iff (isBlockAffine_equation F)
    (notMem_vars_equation F)]
  have hb : (∀ e, q (bCoord e) = expoPow (fun i => q (aCoord i)) e / bobScale n d) ↔
      ∀ e, bobScale n d * q (bCoord e) = expoPow (fun i => q (aCoord i)) e := by
    refine forall_congr' fun e => ?_
    rw [eq_div_iff bobScale_pos.ne', mul_comm]
  rw [hb]
  constructor
  · rintro ⟨hpos, hsum, heq⟩
    have hchain := bobScale_mul_eq_expoPow fun e => heq .critter (.inl e)
    refine ⟨⟨fun i => hpos _, hsum .alice, fun j => ?_⟩, hchain, fun e => ?_, fun j hj => ?_,
      fun j => hpos _, hsum .critter⟩
    · rw [← eval_encode (hF j) hchain]
      exact heq .critter (.inr j)
    · have := heq .bob e
      simp only [equation, map_sub, eval_X, eval_C] at this
      linarith
    · have := heq .alice ⟨j, hj⟩
      simp only [equation, j.2, ↓reduceDIte, map_sub, eval_X, eval_C] at this
      linarith
  · rintro ⟨⟨ha, hasum, hF0⟩, hchain, hcb, hca, hcpos, hcsum⟩
    refine ⟨fun v => ?_, fun w => ?_, fun w t => ?_⟩
    · rcases v with ⟨_ | _ | _, t⟩
      · exact ha t
      · rw [← mul_pos_iff_of_pos_left bobScale_pos]
        exact (hchain t).symm ▸ expoPow_pos ha t
      · rcases t with e | j
        · exact (hcb e).symm ▸ critterWeight_pos
        · exact hcpos j
    · rcases w with _ | _ | _
      · exact hasum
      · have := sum_expoPow_div_lt_one (d := d) ha hasum
        refine lt_of_eq_of_lt (sum_congr rfl fun e _ => ?_) this
        rw [eq_div_iff bobScale_pos.ne', mul_comm]
        exact hchain e
      · exact hcsum
    · rcases w with _ | _ | _
      · simp only [equation]
        split_ifs with h
        · simp [hca _ (show (⟨t, h⟩ : Fin m).val < n from t.2)]
        · simp
      · simp [equation, hcb]
      · rcases t with e | j
        · exact eval_chainEq_of_eq hchain e
        · simp only [equation]
          rw [eval_encode (hF j) hchain, hF0]

end Cslib.GameTheory.DattaThree
