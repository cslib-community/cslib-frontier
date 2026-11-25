/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Universality.SimplexGame
public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.Algebra.MvPolynomial.Degrees
public import CslibFrontier.Foundations.Data.Finsupp.Interval
public import CslibFrontier.Foundations.Data.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A three-player universality game

An original three-player variant of the construction in the proof of Theorem 5 of [Datta2003]
(statement p. 4, proof pp. 4–6). Let `F₀, …, F_{m-1}` be polynomials in `n` variables, and let
`E` be a finite set of exponent vectors that is closed downwards (coordinatewise) and contains the
exponents of every monomial of every `F_j`. There is a game with three players, Alice, Bob and
Critter, with `n + 1`, `|E| + 1` and `|E| + m + 1` pure strategies, whose totally mixed Nash
equilibria are the points `x` of the open simplex `{x | 0 < xᵢ, ∑ xᵢ < 1}` with `F_j(x) = 0`,
encoded together with the monomials `xᵉ`, `e ∈ E`, and, when `m > n`, `m - n` free probabilities
of Critter.

The smallest admissible table is the **sparse table** `sparseTable F`: the exponents lying
coordinatewise below some monomial of some `F_j` (`sparseTable_subset`). The full box `{0, …, d}ⁿ`
is admissible when every `F_j` has degree at most `d` in every variable.

## The construction

Every player has a reference strategy (`none`, `CostGame.simplexGame`). The non-reference
strategies (`DattaThree.Strat`) are:
* for Alice, `i < n`, whose probability is `xᵢ`;
* for Bob, the exponent vectors `e ∈ E`, whose probability stands for `xᵉ / K` with `K = |E| + 1`
  (`bobScale`);
* for Critter, the exponent vectors `e ∈ E` and the equations `j < m`.

Each player's indifference equations involve only the other two players:
* Critter's equation for `e` is the **monomial chain** `K b_e = a_l · K b_{e - 1_l}`, where `l` is a
  variable with `e_l ≥ 1`, and `K b_0 = 1` (`chainEq`). Since `E` is closed downwards,
  `e - 1_l ∈ E`. By induction on the total degree the chain forces `b_e = xᵉ / K`.
* Critter's equation for `j` is `F_j` with each monomial `xᵉ` replaced by `K b_e` (`encode`),
  which is affine in Bob's block.
* Bob's equation for `e` and, for `j < min(m, n)`, Alice's equation for `j` fix Critter's
  probability of the strategy for `e`, resp. `j`, at `1 / (number of Critter's strategies)`
  (`critterWeight`). Alice's remaining equations are `0`.

**Differences from the source.** The monomial table is this library's, not Datta's. Datta
writes each `F_j` by Horner's rule as a chain of bilinear equations, one per step, with affine
rescalings of Bob's coordinates (`Cslib.GameTheory.DattaHorner.game`). Here the `F_j` share one
table of monomials, so the scaling `1 / K` keeps Bob's probabilities in the open simplex without
affine shifts. With `d_ij` the degree of `xᵢ` in `F_j`, the sparse table satisfies
`|sparseTable F| + m ≤ 1 + ∑ⱼ ∏ᵢ (1 + d_ij)` (`card_sparseTable_add_le`). Against the counts
`D − m + 1` and `D + 1` printed in the paper, with `D = −1 + ∑ⱼ ∏ᵢ (1 + d_ij)`, Bob and Critter
have at most two more strategies. Against the Horner game's actual counts, whose `D` is the number
`∑ⱼ (∏ᵢ (1 + d_ij) − 1)` of chain equations, they have at most `m + 1` more
(`DattaHorner.card_sparseTable_le`), and fewer when the `F_j` share monomials or are sparse within
their degree boxes (`DattaHorner.card_table_sub_card`). With the full box `{0, …, d}ⁿ`, write
`N = (d + 1)ⁿ`; Bob and Critter have `N + 1` and `N + m + 1` strategies, and the sparse table is
never larger (`card_sparseTable_le_pow`). Datta fixes Critter's probabilities at `1 / D` (p. 6),
which leaves Critter's reference strategy with probability `0` when `m ≤ n`; dividing by the
number of Critter's strategies avoids this.

## Main definitions

* `Cslib.GameTheory.DattaThree.game E F`: the game on the table `E`.
* `Cslib.GameTheory.DattaThree.sparseTable F`: the smallest admissible table.

## Main results

* `Cslib.GameTheory.DattaThree.isTotallyMixedNash_game_iff`: its totally mixed Nash equilibria.
* `Cslib.GameTheory.DattaThree.card_strategies`: the numbers of pure strategies.
* `Cslib.GameTheory.DattaThree.card_sparseTable_add_le`: the sparse table against the paper's `D`.
* `Cslib.GameTheory.DattaThree.card_sparseTable_le_pow`: the sparse table against the full box.

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

variable {n m : ℕ}

/-- The non-reference pure strategies of each player, for the table of exponents `E`. -/
abbrev Strat (E : Finset (Fin n →₀ ℕ)) (m : ℕ) : Who → Type
  | .alice => Fin n
  | .bob => E
  | .critter => E ⊕ Fin m

variable {E : Finset (Fin n →₀ ℕ)}

instance instFintypeStrat : ∀ w, Fintype (Strat E m w)
  | .alice => inferInstanceAs (Fintype (Fin n))
  | .bob => inferInstanceAs (Fintype E)
  | .critter => inferInstanceAs (Fintype (E ⊕ Fin m))

instance instDecidableEqStrat : ∀ w, DecidableEq (Strat E m w)
  | .alice => inferInstanceAs (DecidableEq (Fin n))
  | .bob => inferInstanceAs (DecidableEq E)
  | .critter => inferInstanceAs (DecidableEq (E ⊕ Fin m))

/-- The coordinates of a profile: one per non-reference strategy. -/
abbrev Coord (E : Finset (Fin n →₀ ℕ)) (m : ℕ) : Type := Σ w, Strat E m w

/-- Alice's coordinate `i`, standing for `xᵢ`. -/
abbrev aCoord (i : Fin n) : Coord E m := ⟨.alice, i⟩

/-- Bob's coordinate `e`, standing for `xᵉ / K`. -/
abbrev bCoord (e : E) : Coord E m := ⟨.bob, e⟩

/-- Critter's coordinate `s`. -/
abbrev cCoord (s : E ⊕ Fin m) : Coord E m := ⟨.critter, s⟩

/-- The scale `K = |E| + 1` of Bob's coordinates: Bob's number of pure strategies. -/
noncomputable abbrev bobScale (E : Finset (Fin n →₀ ℕ)) : ℝ := #E + 1

/-- The probability `1 / (|E| + m + 1)` at which Critter's coordinates are fixed: one over
Critter's number of pure strategies. -/
noncomputable abbrev critterWeight (E : Finset (Fin n →₀ ℕ)) (m : ℕ) : ℝ := 1 / (#E + m + 1)

/-- The monomial `xᵉ = ∏ xᵢ ^ eᵢ`. -/
@[expose] noncomputable def expoPow (x : Fin n → ℝ) (e : Fin n →₀ ℕ) : ℝ := ∏ i, x i ^ e i

/-- Critter's monomial chain equation for `e`: `K b_e - K a_l b_{e - 1_l}` for a variable `l` with
`e_l ≥ 1` and `e - 1_l ∈ E`, and `K b_e - 1` if there is none. -/
noncomputable def chainEq (e : E) : MvPolynomial (Coord E m) ℝ :=
  if h : ∃ l, e.1 l ≠ 0 ∧ e.1 - Finsupp.single l 1 ∈ E then
    C (bobScale E) * X (bCoord e) -
      C (bobScale E) * (X (aCoord h.choose) * X (bCoord ⟨_, h.choose_spec.2⟩))
  else C (bobScale E) * X (bCoord e) - 1

/-- The encoding of `F` in Bob's block: each monomial `xᵉ`, `e ∈ E`, becomes `K b_e`. -/
noncomputable def encode (F : MvPolynomial (Fin n) ℝ) : MvPolynomial (Coord E m) ℝ :=
  ∑ e : E, C (F.coeff e * bobScale E) * X (bCoord e)

/-- The indifference equations of the three players. -/
noncomputable def equation (F : Fin m → MvPolynomial (Fin n) ℝ) :
    ∀ w, Strat E m w → MvPolynomial (Coord E m) ℝ
  | .alice, i => if h : i.val < m then X (cCoord (.inr ⟨i, h⟩)) - C (critterWeight E m) else 0
  | .bob, e => X (cCoord (.inl e)) - C (critterWeight E m)
  | .critter, .inl e => chainEq e
  | .critter, .inr j => encode (F j)

/-- **The three-player game** for the system `F` on the table of exponents `E`. -/
noncomputable def game (E : Finset (Fin n →₀ ℕ)) (F : Fin m → MvPolynomial (Fin n) ℝ) :
    CostGame Who (fun w => Option (Strat E m w)) :=
  CostGame.simplexGame (equation (E := E) F)

/-- Alice, Bob and Critter have `n + 1`, `|E| + 1` and `|E| + m + 1` pure strategies. -/
theorem card_strategies :
    Fintype.card (Option (Strat E m .alice)) = n + 1 ∧
      Fintype.card (Option (Strat E m .bob)) = #E + 1 ∧
      Fintype.card (Option (Strat E m .critter)) = #E + m + 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Fintype.card_option, Fintype.card_sum]

/-! ### The sparse table -/

/-- The **sparse table** of `F`: the exponent vectors lying coordinatewise below the exponents of
some monomial of some `F j`. -/
noncomputable def sparseTable (F : Fin m → MvPolynomial (Fin n) ℝ) : Finset (Fin n →₀ ℕ) :=
  univ.biUnion fun j => (F j).support.biUnion Iic

theorem mem_sparseTable {F : Fin m → MvPolynomial (Fin n) ℝ} {e : Fin n →₀ ℕ} :
    e ∈ sparseTable F ↔ ∃ j, ∃ s ∈ (F j).support, e ≤ s := by
  simp [sparseTable]

theorem isLowerSet_sparseTable (F : Fin m → MvPolynomial (Fin n) ℝ) :
    IsLowerSet (sparseTable F : Set (Fin n →₀ ℕ)) := fun _ _ hba ha => by
  obtain ⟨j, s, hs, has⟩ := mem_sparseTable.1 ha
  exact mem_sparseTable.2 ⟨j, s, hs, hba.trans has⟩

theorem support_subset_sparseTable (F : Fin m → MvPolynomial (Fin n) ℝ) (j : Fin m) :
    (F j).support ⊆ sparseTable F := fun s hs => mem_sparseTable.2 ⟨j, s, hs, le_rfl⟩

/-- The sparse table is the smallest table that is closed downwards and contains every monomial
of every `F j`. -/
theorem sparseTable_subset {F : Fin m → MvPolynomial (Fin n) ℝ}
    (hE : IsLowerSet (E : Set (Fin n →₀ ℕ))) (hF : ∀ j, (F j).support ⊆ E) :
    sparseTable F ⊆ E := fun e he => by
  obtain ⟨j, s, hs, hes⟩ := mem_sparseTable.1 he
  exact hE hes (hF j hs)

/-- **The sparse table against Datta's count.** With `d_ij = degreeOf i (F j)` and the paper's
printed `D = −1 + ∑ⱼ ∏ᵢ (1 + d_ij)`, this says `|sparseTable F| + m ≤ D + 2`: Bob's and Critter's
`|E| + 1` and `|E| + m + 1` strategies exceed the printed `D − m + 1` and `D + 1` by at most `2`.
The Horner chain has only `D − m + 1` equations, so against the Horner game's actual counts the
excess is at most `m + 1` (`DattaHorner.card_sparseTable_le`). -/
theorem card_sparseTable_add_le (F : Fin m → MvPolynomial (Fin n) ℝ) :
    #(sparseTable F) + m ≤ 1 + ∑ j, ∏ i, (1 + degreeOf i (F j)) := by
  classical
  have hsub : sparseTable F ⊆ insert 0 (univ.biUnion fun j => (Iic (degreeVec (F j))).erase 0) :=
    fun e he => by
      obtain ⟨j, s, hs, hes⟩ := mem_sparseTable.1 he
      exact if h0 : e = 0 then mem_insert.2 (.inl h0)
        else mem_insert_of_mem (mem_biUnion.2 ⟨j, mem_univ j,
          mem_erase.2 ⟨h0, mem_Iic.2 (hes.trans (le_degreeVec hs))⟩⟩)
  calc #(sparseTable F) + m
      ≤ (1 + ∑ j, #((Iic (degreeVec (F j))).erase 0)) + ∑ _j : Fin m, 1 := by
        simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
        exact Nat.add_le_add_right ((card_le_card hsub).trans ((card_insert_le _ _).trans
          (by rw [add_comm]; exact Nat.add_le_add_left card_biUnion_le 1))) _
    _ = 1 + ∑ j, ∏ i, (1 + degreeOf i (F j)) := by
        rw [add_assoc, ← sum_add_distrib]
        refine congrArg (1 + ·) (sum_congr rfl fun j _ => ?_)
        rw [card_erase_add_one (mem_Iic.2 zero_le), Finsupp.card_Iic_eq_prod]
        simp

/-- **The sparse table against the full box.** If every `F j` has degree at most `d` in every
variable, the sparse table has at most `(d + 1)ⁿ` elements. -/
theorem card_sparseTable_le_pow {F : Fin m → MvPolynomial (Fin n) ℝ} {d : ℕ}
    (hF : ∀ j i, degreeOf i (F j) ≤ d) : #(sparseTable F) ≤ (d + 1) ^ n := by
  have hsub : sparseTable F ⊆ Iic (Finsupp.equivFunOnFinite.symm fun _ => d) := fun e he => by
    obtain ⟨j, s, hs, hes⟩ := mem_sparseTable.1 he
    exact mem_Iic.2 fun i => (hes i).trans (by simpa using (degreeOf_le_iff.1 (hF j i)) s hs)
  refine (card_le_card hsub).trans_eq ?_
  rw [Finsupp.card_Iic_eq_prod]
  simp [add_comm]

/-! ### The monomial chain -/

theorem bobScale_pos : 0 < bobScale E := by positivity

theorem critterWeight_pos : 0 < critterWeight E m := by positivity

theorem expoPow_sub_single (x : Fin n → ℝ) {e : Fin n →₀ ℕ} {l : Fin n} (hl : e l ≠ 0) :
    expoPow x e = x l * expoPow x (e - Finsupp.single l 1) := by
  conv_lhs => rw [← tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hl))]
  simp only [expoPow, Finsupp.add_apply, pow_add, prod_mul_distrib, Finsupp.single_apply, pow_ite,
    pow_one, pow_zero, prod_ite_eq, mem_univ, ite_true]
  ring

private theorem sum_sub_single_lt {e : Fin n →₀ ℕ} {l : Fin n} (hl : e l ≠ 0) :
    ∑ i, (e - Finsupp.single l 1 : Fin n →₀ ℕ) i < ∑ i, e i :=
  sum_lt_sum (fun _ _ => by simp) ⟨l, mem_univ l, by
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]; omega⟩

theorem expoPow_zero (x : Fin n → ℝ) : expoPow x 0 = 1 := by
  simp [expoPow]

/-- On a table closed downwards, the only `e` without a lowered neighbour in the table is `0`. -/
private theorem eq_zero_of_forall_sub_single_notMem (hE : IsLowerSet (E : Set (Fin n →₀ ℕ)))
    {e : E} (h : ¬∃ l, e.1 l ≠ 0 ∧ e.1 - Finsupp.single l 1 ∈ E) : e.1 = 0 := by
  ext l; exact by_contra fun hl => h ⟨l, hl, hE tsub_le_self e.2⟩

/-- On a table closed downwards, the monomial chain forces `K b_e = xᵉ`. -/
theorem bobScale_mul_eq_expoPow (hE : IsLowerSet (E : Set (Fin n →₀ ℕ))) {q : Coord E m → ℝ}
    (h : ∀ e, eval q (chainEq (m := m) e) = 0) (e : E) :
    bobScale E * q (bCoord e) = expoPow (fun i => q (aCoord i)) e := by
  induction hk : ∑ i, e.1 i using Nat.strong_induction_on generalizing e with
  | _ k ih =>
    have he := h e
    unfold chainEq at he
    split_ifs at he with hne
    · have hl := hne.choose_spec
      have hrec := ih _ (hk ▸ sum_sub_single_lt hl.1) ⟨_, hl.2⟩ rfl
      rw [expoPow_sub_single _ hl.1, ← hrec]
      simp only [map_sub, map_mul, eval_C, eval_X] at he
      linarith
    · rw [eq_zero_of_forall_sub_single_notMem hE hne, expoPow_zero]
      simp only [map_sub, map_mul, eval_C, eval_X, map_one] at he
      linarith

theorem eval_chainEq_of_eq (hE : IsLowerSet (E : Set (Fin n →₀ ℕ))) {q : Coord E m → ℝ}
    (h : ∀ e, bobScale E * q (bCoord e) = expoPow (fun i => q (aCoord i)) e) (e : E) :
    eval q (chainEq (m := m) e) = 0 := by
  unfold chainEq
  split_ifs with hne
  · simp only [map_sub, map_mul, eval_C, eval_X]
    linear_combination h e - q (aCoord hne.choose) * h ⟨_, hne.choose_spec.2⟩ +
      expoPow_sub_single (fun i => q (aCoord i)) hne.choose_spec.1
  · have he := h e
    rw [eq_zero_of_forall_sub_single_notMem hE hne, expoPow_zero] at he
    simp only [map_sub, map_mul, eval_C, eval_X, map_one]
    linear_combination he

/-- Under the monomial chain, the encoding of `F` evaluates to `F(x)`. -/
theorem eval_encode {F : MvPolynomial (Fin n) ℝ} (hF : F.support ⊆ E) {q : Coord E m → ℝ}
    (h : ∀ e, bobScale E * q (bCoord e) = expoPow (fun i => q (aCoord i)) e) :
    eval q (encode F) = eval (fun i => q (aCoord i)) F := by
  rw [encode, map_sum, eval_eq', sum_subset hF fun s _ hs => by
    rw [notMem_support_iff.1 hs, zero_mul], ← sum_coe_sort E]
  refine sum_congr rfl fun e _ => ?_
  simp only [map_mul, eval_C, eval_X]
  rw [mul_assoc, h, expoPow]

/-! ### Shape of the equations -/

private theorem C_mem_supported {s : Set (Coord E m)} (c : ℝ) :
    MvPolynomial.C c ∈ supported ℝ s :=
  mem_supported.2 (by simp [vars_C])

/-- Each player's equations only involve the other players. -/
theorem mem_supported_equation (F : Fin m → MvPolynomial (Fin n) ℝ) (w : Who)
    (t : Strat E m w) : equation F w t ∈ supported ℝ {v | v.1 ≠ w} := by
  have hX : ∀ v : Coord E m, v.1 ≠ w → X v ∈ supported ℝ {v : Coord E m | v.1 ≠ w} :=
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
    (t : Strat E m w) : ∀ v ∈ (equation F w t).vars, v.1 ≠ w := fun _ hv =>
  (mem_supported.1 (mem_supported_equation F w t)) hv

theorem isBlockAffine_equation (F : Fin m → MvPolynomial (Fin n) ℝ) (w : Who)
    (t : Strat E m w) : IsBlockAffine (equation F w t) := by
  have hCX : ∀ (c : ℝ) (v : Coord E m), IsBlockAffine (C c * X v) := fun c v =>
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
      · exact (hCX _ _).sub (by simpa using IsBlockAffine.C (T := Strat E m) 1)
    · exact IsBlockAffine.sum fun s _ => hCX _ _

/-! ### The totally mixed equilibria -/

theorem expoPow_pos {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) (e : Fin n →₀ ℕ) : 0 < expoPow x e :=
  prod_pos fun i _ => pow_pos (hx i) _

theorem expoPow_le_one {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (e : Fin n →₀ ℕ) : expoPow x e ≤ 1 :=
  prod_le_one₀ (fun i _ => pow_nonneg (hx i) _) fun i _ => pow_le_one₀ (hx i) (hx1 i)

/-- Bob's weights `xᵉ / K` sum to less than `1` on the open simplex. -/
theorem sum_expoPow_div_lt_one {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) (hx1 : ∑ i, x i < 1) :
    ∑ e : E, expoPow x e / bobScale E < 1 := by
  have hle (i : Fin n) : x i ≤ 1 :=
    (single_le_sum (fun j _ => (hx j).le) (mem_univ i)).trans hx1.le
  calc ∑ e : E, expoPow x e / bobScale E
      ≤ ∑ _e : E, 1 / bobScale E := sum_le_sum fun e _ =>
        div_le_div_of_nonneg_right (expoPow_le_one (fun i => (hx i).le) hle e) bobScale_pos.le
    _ < 1 := by
      simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul, ← div_eq_mul_one_div,
        div_lt_one bobScale_pos]
      linarith

/-- **The three-player construction** (original variant of the proof of Theorem 5 of
[Datta2003]). If the table `E` is closed downwards and contains the exponents of every monomial of
every `F j`, the totally mixed Nash equilibria of the three-player game are the profiles
`simplexProfile q` such that:
* Alice's weights `x = q ∘ aCoord` lie in the open simplex and solve every `F j = 0`;
* Bob plays each monomial `xᵉ / K`, `e ∈ E`;
* Critter plays `1 / (number of Critter's strategies)` on its strategies for the exponent vectors
  and for the equations `j < n`;
* Critter's remaining weights are positive, and its non-reference weights sum to less than `1`.

`sparseTable F` is the smallest such table (`isLowerSet_sparseTable`,
`support_subset_sparseTable`, `sparseTable_subset`). -/
theorem isTotallyMixedNash_game_iff (hE : IsLowerSet (E : Set (Fin n →₀ ℕ)))
    {F : Fin m → MvPolynomial (Fin n) ℝ} (hF : ∀ j, (F j).support ⊆ E) (q : Coord E m → ℝ) :
    (game E F).IsTotallyMixedNash (simplexProfile q) ↔
      ((∀ i, 0 < q (aCoord i)) ∧ ∑ i, q (aCoord i) < 1 ∧
        ∀ j, eval (fun i => q (aCoord i)) (F j) = 0) ∧
      (∀ e : E, q (bCoord e) = expoPow (fun i => q (aCoord i)) e / bobScale E) ∧
      (∀ e, q (cCoord (.inl e)) = critterWeight E m) ∧
      (∀ j : Fin m, j.val < n → q (cCoord (.inr j)) = critterWeight E m) ∧
      (∀ j, 0 < q (cCoord (.inr j))) ∧ ∑ s, q (cCoord s) < 1 := by
  rw [game, CostGame.isTotallyMixedNash_simplexGame_iff (isBlockAffine_equation F)
    (notMem_vars_equation F), forall_congr' fun e : E => by
      rw [eq_div_iff bobScale_pos.ne', mul_comm]]
  refine ⟨fun ⟨hpos, hsum, heq⟩ => ?_,
    fun ⟨⟨ha, hasum, hF0⟩, hchain, hcb, hca, hcpos, hcsum⟩ => ⟨?_, ?_, ?_⟩⟩
  · have hchain := bobScale_mul_eq_expoPow hE fun e => heq .critter (.inl e)
    refine ⟨⟨fun _ => hpos _, hsum .alice, fun j => ?_⟩, hchain, fun e => ?_, fun j hj => ?_,
      fun _ => hpos _, hsum .critter⟩
    · rw [← eval_encode (hF j) hchain]; exact heq .critter (.inr j)
    · simpa only [equation, map_sub, eval_X, eval_C, sub_eq_zero] using heq .bob e
    · simpa only [equation, j.2, ↓reduceDIte, map_sub, eval_X, eval_C, sub_eq_zero] using
        heq .alice ⟨j, hj⟩
  · rintro ⟨_ | _ | _, t⟩
    · exact ha t
    · exact (mul_pos_iff_of_pos_left bobScale_pos).1 ((hchain t).symm ▸ expoPow_pos ha t)
    · exact t.rec (fun e => (hcb e).symm ▸ critterWeight_pos) hcpos
  · rintro (_ | _ | _)
    · exact hasum
    · refine lt_of_eq_of_lt (sum_congr rfl fun e _ => ?_) (sum_expoPow_div_lt_one ha hasum)
      rw [eq_div_iff bobScale_pos.ne', mul_comm]; exact hchain e
    · exact hcsum
  · rintro (_ | _ | _) t
    · simp only [equation]; split_ifs with h
      · simp [hca _ (show (⟨t, h⟩ : Fin m).val < n from t.2)]
      · simp
    · simp [equation, hcb]
    · rcases t with e | j
      · exact eval_chainEq_of_eq hE hchain e
      · simp only [equation, eval_encode (hF j) hchain, hF0]

end Cslib.GameTheory.DattaThree
