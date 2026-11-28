/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Universality.DattaThree
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Datta's three-player game: the Horner chain

The construction in the proof of Theorem 5 of [Datta2003] (arXiv:math/0301001, statement p. 4,
proof pp. 4–6). Let `F₀, …, F_{m-1}` be polynomials in `n` variables and let `d_ij` be the degree
of `xᵢ` in `F_j` (`MvPolynomial.degreeOf`). There is a game with three players, Alice, Bob and
Critter. When every `F_j` involves a variable, they have `n + 1`, `D − m + 1` and `D + 1` pure
strategies, where `D = ∑ⱼ (∏ᵢ (1 + d_ij) − 1)` is the number of chain equations (`chainLength`);
a constant `F_j` contributes no chain equation but still gives Critter a strategy. For any `F`,
its totally mixed Nash equilibria are the points `x` of the open simplex `{x | 0 < xᵢ, ∑ xᵢ < 1}`
with `F_j(x) = 0`, encoded together with the intermediate values of Horner's rule and, when
`m > n`, `m − n` free probabilities of Critter.

## Horner's rule

Datta writes `F_j = x₁^{d₁ⱼ} F_j^{d₁ⱼ}(x₂, …, xₙ) + ⋯ + F_j^0(x₂, …, xₙ)` and recursively expands
the coefficients, `x₁` outermost and `xₙ` innermost. With variables indexed from `0`, the
intermediate value of Horner's rule at the variable `k` and the exponent prefix `e` (supported on
`{0, …, k}`) is
`horner F x k e = ∑_{f ∈ supp F, e ≤ f, f_i = e_i for i < k} coeff_f(F) · x^{f − e}`.
It satisfies `horner F x 0 0 = F(x)` (`horner_zero`), `horner F x n e = coeff_e(F)`
(`horner_of_le`) and the Horner step (`horner_eq`)
`horner F x k e = x_k · horner F x k (e + 1_k) + horner F x (k + 1) e`.
For `k` and `e_k < d_k` this is one equation of Datta's chain: the first term is the previous
step of Horner's rule in `x_k`, the second is the next coefficient, itself a polynomial in
`x_{k+1}, …, x_{n-1}`. When `e_k ≥ d_k` the first term vanishes, so `horner F x k e` is read off at
the first variable `k' ≥ k` with `e_{k'} < d_{k'}`, or is the constant `coeff_e(F)` if there is
none (`level`, `horner_level`).

## The construction

The **nodes** of the chain of `F_j` are the pairs `(k, e)` with `e ≤ d_j`, `e_k < d_{kj}` and
`e_i = 0` for `i > k` (`nodes`). They correspond to the nonzero exponents `e + 1_k` of the box
`∏ᵢ {0, …, d_ij}`, so there are `∏ᵢ (1 + d_ij) − 1` of them (`card_nodes`). Each node carries a
**chain equation** (`chainEq`)
`s_j b_{(k,e)} + δ_j = a_k · (value of (k, e + 1_k)) + (value of (k + 1, e))`,
where a value is `s_j b + δ_j` for the node it is read from, or a constant coefficient of `F_j`.
The **root** of the chain (`root`) is the node `(k, 0)` at the first variable that occurs in
`F_j`; its value is `horner F_j x 0 0 = F_j(x)`, and its chain equation has left side `0`. So it
encodes `F_j(x) = 0`.

Every player has a reference strategy (`none`, `CostGame.simplexGame`). The non-reference
strategies (`Strat`) are:
* for Alice, `i < n`, whose probability is `xᵢ`;
* for Bob, the non-root nodes of all the chains (`bobNodes`);
* for Critter, Bob's nodes and the equations `j < m`.

Critter's equation for a node is its chain equation, and for `j` the chain equation of the root of
`F_j` (`rootEq`). Bob's equation for a node and, for `j < min(m, n)`, Alice's equation for `j` fix
Critter's corresponding probability at `critterWeight F`, one over Critter's number
`|bobNodes F| + m + 1` of strategies. This is `1 / (D + 1)` when every `F_j` involves a variable.
Alice's remaining equations are `0`.

## Choices where the source is not explicit

* **The rescaling.** Datta asks for constants `s_k ≠ 0`, `δ_k` with `0 < b_k` and `∑ b_k < 1` on
  `S`, without giving them. Here `s = 2 M_j K` and `δ = −M_j` for every node of `F_j`, with
  `M_j = 1 + ∑ |coeff(F_j)|` (`coeffBound`) and `K` Bob's number of strategies. Every
  Horner value is smaller than `M_j` in absolute value on the whole open simplex
  (`abs_horner_lt`), so every `b` lies in `(0, 1/K)`.
* **The order of the nodes.** The paper builds the chain in `xₙ` first; the nodes `(k, e)` index
  the same equations, with `x₀` outermost.
* **Constant equations.** A constant `F_j` has no chain; its root equation is `F_j = 0` itself.
  The characterization allows it, but the strategy counts need every `F_j` to involve a variable:
  the paper's counts are impossible otherwise (one constant equation in one variable gives Bob
  `0` strategies).

## Source repairs

* **Critter's fixed probabilities.** Datta sets them at `1 / D` (p. 6). When `m ≤ n` all `D` of
  them are fixed, so Critter's reference strategy gets probability `0`. Here they are one over
  Critter's number of strategies (`critterWeight`), which is `1 / (D + 1)` when every `F_j`
  involves a variable.
* **The value of `D`.** The paper's chain for `F_j` has `∏ᵢ (1 + d_ij) − 1` equations (p. 6), so
  the `m` chains have `∑ⱼ (∏ᵢ (1 + d_ij) − 1)` equations. The paper calls this number
  `D = −1 + ∑ⱼ ∏ᵢ (1 + d_ij)`, which is larger by `m − 1` (`chainLength_add`); the two agree when
  `m = 1`. The counts here use the number of chain equations, so the game is smaller than the
  printed statement says when `m ≥ 2`.

## Comparison with the shared-table games

The games of `Cslib.GameTheory.DattaThree` on a table `E` give Bob and Critter `|E| + 1` and
`|E| + m + 1` strategies. Both exceed the Horner game's counts by the same `|E| + m − D`
(`card_table_sub_card`). The sparse table has at most `D + 1` exponents (`card_sparseTable_le`), so
it costs at most `m + 1` more strategies per player. For equations of full degree `d` in every
variable, `D = m (N − 1)` with `N = (d + 1)ⁿ` (`chainLength_of_degreeOf_eq`), and the full box is
smaller exactly when `(m − 1) N > 2m` (`pow_add_lt_chainLength_iff`). With the paper's printed `D`
the condition would read `(m − 1) N > m + 1`.

## Main definitions

* `Cslib.GameTheory.DattaHorner.horner`: the intermediate values of Horner's rule.
* `Cslib.GameTheory.DattaHorner.game F`: Datta's game for the system `F`.
* `Cslib.GameTheory.DattaHorner.chainLength F`: the number `D` of chain equations.

## Main results

* `Cslib.GameTheory.DattaHorner.isTotallyMixedNash_game_iff`: its totally mixed Nash equilibria.
* `Cslib.GameTheory.DattaHorner.card_strategies`: the numbers of pure strategies.
* `Cslib.GameTheory.DattaHorner.card_table_sub_card`: the comparison with the shared-table games.

## References

* [Datta2003]
-/

public section

namespace Cslib.GameTheory.DattaHorner

open MvPolynomial Finset Function
open DattaThree (Who expoPow)

variable {n m : ℕ}

/-! ### Horner's rule -/

/-- The intermediate value of Horner's rule for `F` at the variable `k` and the exponent prefix
`e`: `∑ coeff_f(F) · x^{f − e}` over the monomials `f` of `F` with `e ≤ f` and `f_i = e_i` for
`i < k`. -/
noncomputable def horner (F : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (k : ℕ)
    (e : Fin n →₀ ℕ) : ℝ :=
  ∑ f ∈ F.support with e ≤ f ∧ ∀ i : Fin n, i.val < k → f i = e i, F.coeff f * expoPow x (f - e)

theorem horner_zero (F : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) : horner F x 0 0 = eval x F := by
  simp [horner, eval_eq', expoPow]

/-- Each Horner value is a polynomial, hence continuous, function of the point. -/
theorem continuous_horner (F : MvPolynomial (Fin n) ℝ) (k : ℕ) (e : Fin n →₀ ℕ) :
    Continuous fun x => horner F x k e := by
  simp only [horner, expoPow]
  exact continuous_finsetSum _ fun f _ => continuous_const.mul
    (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _)

theorem horner_of_le (F : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) {k : ℕ} (hk : n ≤ k)
    (e : Fin n →₀ ℕ) : horner F x k e = F.coeff e := by
  have hf : ∀ f : Fin n →₀ ℕ, (e ≤ f ∧ ∀ i : Fin n, i.val < k → f i = e i) ↔ f = e := fun f =>
    ⟨fun h => Finsupp.ext fun i => h.2 i (i.isLt.trans_le hk),
      fun h => h ▸ ⟨le_rfl, fun _ _ => rfl⟩⟩
  simp only [horner, hf, filter_eq']
  split_ifs with h
  · simp [expoPow]
  · simp [notMem_support_iff.1 h]

private theorem add_single_le {d e : Fin n →₀ ℕ} {k : Fin n} (he : e ≤ d) (hk : e k < d k) :
    e + Finsupp.single k 1 ≤ d := fun i => by
  rcases eq_or_ne k i with rfl | hi
  · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
    omega
  · simpa [Finsupp.single_apply, hi] using he i

/-- **The Horner step**: `horner F x k e = x_k · horner F x k (e + 1_k) + horner F x (k + 1) e`. -/
theorem horner_eq (F : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (l : Fin n) (e : Fin n →₀ ℕ) :
    horner F x l e =
      x l * horner F x l (e + Finsupp.single l 1) + horner F x (l + 1) e := by
  have hs : ∀ i : Fin n, i.val < l.val → (e + Finsupp.single l 1 : Fin n →₀ ℕ) i = e i :=
    fun i hi => by
      have : l ≠ i := fun h => by subst h; omega
      simp [this]
  rw [horner, ← sum_filter_add_sum_filter_not _ (fun f => f l = e l), add_comm]
  congr 1
  · rw [horner, mul_sum, filter_filter]
    refine sum_congr (filter_congr fun f _ => ?_) fun f hf => ?_
    · constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨add_single_le h1 ((h1 l).lt_of_ne fun h => h3 h.symm),
          fun i hi => (h2 i hi).trans (hs i hi).symm⟩
      · rintro ⟨h1, h2⟩
        have hl := h1 l
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at hl
        exact ⟨⟨fun i => le_trans (by simp) (h1 i), fun i hi => (h2 i hi).trans (hs i hi)⟩,
          by omega⟩
    · have h1 := (mem_filter.1 hf).2.1 l
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at h1
      have hfe : (f - e) l ≠ 0 := by
        simp only [Finsupp.coe_tsub, Pi.sub_apply]
        omega
      rw [DattaThree.expoPow_sub_single x hfe, tsub_tsub]
      ring
  · rw [horner, filter_filter]
    refine sum_congr (filter_congr fun f _ => ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, fun i hi => ?_⟩,
      fun ⟨h1, h2⟩ => ⟨⟨h1, fun i hi => h2 i (by omega)⟩, h2 l (by omega)⟩⟩) fun _ _ => rfl
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · exact h2 i hi
    · exact Fin.ext hi ▸ h3

theorem horner_eq_zero_of_lt (F : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (k : ℕ)
    {e : Fin n →₀ ℕ} {i : Fin n} (h : degreeOf i F < e i) : horner F x k e = 0 :=
  sum_eq_zero fun f hf => by
    obtain ⟨hfs, hef, _⟩ := mem_filter.1 hf
    exact absurd ((hef i).trans (monomial_le_degreeOf i hfs)) (not_le.2 h)

/-- The variable at which Horner's rule reads `horner F x k e`, for `d` the degree vector of `F`:
the first `i ≥ k` with `e i < d i`, or `none` if there is none. -/
def level (d : Fin n →₀ ℕ) (k : ℕ) (e : Fin n →₀ ℕ) : Option (Fin n) :=
  if h : k < n then
    if e ⟨k, h⟩ < d ⟨k, h⟩ then some ⟨k, h⟩ else level d (k + 1) e
  else none
termination_by n - k

/-- `horner F x k e` is the value at the node `(level k e, e)`, or the constant `coeff_e(F)`. -/
theorem horner_level (F : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (k : ℕ) (e : Fin n →₀ ℕ) :
    horner F x k e =
      (level (degreeVec F) k e).elim (F.coeff e) fun i => horner F x i e := by
  fun_induction level (degreeVec F) k e with
  | case1 k h hlt => rfl
  | case2 k h hlt ih =>
    rw [← ih, horner_eq F x ⟨k, h⟩ e,
      horner_eq_zero_of_lt F x _ (i := ⟨k, h⟩) (by simp at hlt ⊢; omega), mul_zero, zero_add]
  | case3 k h => exact horner_of_le F x (not_lt.1 h) e

theorem le_of_level_eq_some {d : Fin n →₀ ℕ} {k : ℕ} {e : Fin n →₀ ℕ} {i : Fin n}
    (h : level d k e = some i) : k ≤ i ∧ e i < d i := by
  fun_induction level d k e with
  | case1 k hk hlt =>
    cases Option.some_inj.1 h
    exact ⟨le_rfl, hlt⟩
  | case2 k hk hlt ih =>
    have := ih h
    exact ⟨by omega, this.2⟩
  | case3 k hk => cases h

theorem le_of_level_eq_none {d : Fin n →₀ ℕ} {k : ℕ} {e : Fin n →₀ ℕ}
    (h : level d k e = none) (i : Fin n) (hi : k ≤ i) : d i ≤ e i := by
  fun_induction level d k e with
  | case1 k hk hlt => cases h
  | case2 k hk hlt ih =>
    rcases Nat.lt_or_eq_of_le hi with hi | hi
    · exact ih h (by omega)
    · obtain rfl : (⟨k, hk⟩ : Fin n) = i := Fin.ext hi
      omega
  | case3 k hk => omega

/-! ### The nodes of the chain -/

/-- A node of the Horner chain of one equation: the step of Horner's rule in the variable `var`
at the exponent prefix `expo`. -/
structure Node (n : ℕ) where
  /-- The variable of this step of Horner's rule. -/
  var : Fin n
  /-- The exponent prefix: the exponents of the variables before `var`, and the position in
  Horner's rule in `var`. -/
  expo : Fin n →₀ ℕ
  deriving DecidableEq

/-- The nodes of the chain for the degree vector `d`: the pairs `(k, e)` with `e ≤ d`,
`e_k < d_k` and `e_i = 0` for `i > k`. -/
noncomputable def nodes (d : Fin n →₀ ℕ) : Finset (Node n) :=
  ((univ ×ˢ Iic d).filter fun p : Fin n × (Fin n →₀ ℕ) =>
    p.2 p.1 < d p.1 ∧ ∀ i, p.1 < i → p.2 i = 0).map
    ⟨fun p => ⟨p.1, p.2⟩, fun p p' h => by cases p; cases p'; cases h; rfl⟩

theorem mem_nodes {d : Fin n →₀ ℕ} {p : Node n} :
    p ∈ nodes d ↔ p.expo ≤ d ∧ p.expo p.var < d p.var ∧ ∀ i, p.var < i → p.expo i = 0 := by
  simp only [nodes, mem_map, mem_filter, mem_product, mem_univ, mem_Iic, true_and]
  exact ⟨by rintro ⟨_, hp, rfl⟩; exact hp, fun h => ⟨(p.var, p.expo), h, rfl⟩⟩

/-- The node at which `horner F x k e` is read is a node of the chain. -/
theorem mem_nodes_of_level {d : Fin n →₀ ℕ} {k : ℕ} {e : Fin n →₀ ℕ} {i : Fin n}
    (he : e ≤ d) (hz : ∀ i : Fin n, k < i.val → e i = 0) (h : level d k e = some i) :
    ⟨i, e⟩ ∈ nodes d := by
  obtain ⟨hki, hlt⟩ := le_of_level_eq_some h
  exact mem_nodes.2 ⟨he, hlt, fun i' (hi' : i < i') => hz i' (by rw [Fin.lt_def] at hi'; omega)⟩

/-- The chain of the degree vector `d` has `∏ᵢ (1 + d i) − 1` nodes: `(k, e) ↦ e + 1_k` is a
bijection onto the nonzero exponents of the box. -/
theorem card_nodes (d : Fin n →₀ ℕ) : #(nodes d) + 1 = ∏ i, (1 + d i) := by
  rw [← Finsupp.card_Iic_eq_prod, ← card_erase_add_one (mem_Iic.2 zero_le)]
  congr 1
  refine card_bij (fun p _ => p.expo + Finsupp.single p.var 1) (fun p hp => ?_)
    (fun p hp p' hp' h => ?_) fun g hg => ?_
  · obtain ⟨hle, hlt, -⟩ := mem_nodes.1 hp
    refine mem_erase.2 ⟨fun h => ?_, mem_Iic.2 (add_single_le hle hlt)⟩
    simpa using DFunLike.congr_fun h p.var
  · obtain ⟨-, -, hz⟩ := mem_nodes.1 hp
    obtain ⟨-, -, hz'⟩ := mem_nodes.1 hp'
    have key : ∀ {a b : Node n}, (∀ i, a.var < i → a.expo i = 0) →
        a.expo + Finsupp.single a.var 1 = b.expo + Finsupp.single b.var 1 → b.var ≤ a.var :=
      fun {a b} hz h => not_lt.1 fun hlt => by
        have := DFunLike.congr_fun h b.var
        simp [hz _ hlt, hlt.ne] at this
    obtain ⟨k, e⟩ := p
    obtain ⟨k', e'⟩ := p'
    obtain rfl : k = k' := le_antisymm (key hz' h.symm) (key hz h)
    simpa using h
  · obtain ⟨hg0, hgd⟩ := mem_erase.1 hg
    have hne : g.support.Nonempty := Finsupp.support_nonempty_iff.2 hg0
    have hk : 1 ≤ g (g.support.max' hne) :=
      Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 (max'_mem _ _))
    refine ⟨⟨g.support.max' hne, g - Finsupp.single (g.support.max' hne) 1⟩,
      mem_nodes.2 ⟨tsub_le_self.trans (mem_Iic.1 hgd), ?_, fun i hi => ?_⟩,
      tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hk)⟩
    · have := mem_Iic.1 hgd (g.support.max' hne)
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
      omega
    · simp [Finsupp.notMem_support_iff.1 fun h => not_le.2 hi (le_max' _ i h)]

/-- The root of the chain: the node `(k, 0)` at the first variable `k` with `d k ≠ 0`. Its value
`horner F x 0 0` is `F(x)`. -/
def root (d : Fin n →₀ ℕ) : Option (Node n) :=
  (level d 0 0).map fun i => ⟨i, 0⟩

theorem exists_root (d : Fin n →₀ ℕ) (hd : d ≠ 0) : ∃ r ∈ nodes d, root d = some r := by
  cases hl : level d 0 0 with
  | none =>
    exact absurd (Finsupp.ext fun i => Nat.le_zero.1 (le_of_level_eq_none hl i i.val.zero_le)) hd
  | some i =>
    exact ⟨⟨i, 0⟩, mem_nodes_of_level zero_le (fun _ _ => rfl) hl, by simp [root, hl]⟩

/-! ### The game -/

/-- Bob's nodes: the non-root nodes of the chains of all equations. -/
noncomputable def bobNodes (F : Fin m → MvPolynomial (Fin n) ℝ) : Finset (Σ _ : Fin m, Node n) :=
  univ.sigma fun j => (nodes (degreeVec (F j))).filter fun p => root (degreeVec (F j)) ≠ some p

theorem mem_bobNodes {F : Fin m → MvPolynomial (Fin n) ℝ} {j : Fin m} {p : Node n} :
    ⟨j, p⟩ ∈ bobNodes F ↔ p ∈ nodes (degreeVec (F j)) ∧ root (degreeVec (F j)) ≠ some p := by
  simp [bobNodes]

/-- The non-reference pure strategies of each player. -/
noncomputable abbrev Strat (F : Fin m → MvPolynomial (Fin n) ℝ) : Who → Type
  | .alice => Fin n
  | .bob => bobNodes F
  | .critter => bobNodes F ⊕ Fin m

variable {F : Fin m → MvPolynomial (Fin n) ℝ}

noncomputable instance instFintypeStrat : ∀ w, Fintype (Strat F w)
  | .alice => inferInstanceAs (Fintype (Fin n))
  | .bob => inferInstanceAs (Fintype (bobNodes F))
  | .critter => inferInstanceAs (Fintype (bobNodes F ⊕ Fin m))

noncomputable instance instDecidableEqStrat : ∀ w, DecidableEq (Strat F w)
  | .alice => inferInstanceAs (DecidableEq (Fin n))
  | .bob => inferInstanceAs (DecidableEq (bobNodes F))
  | .critter => inferInstanceAs (DecidableEq (bobNodes F ⊕ Fin m))

/-- The coordinates of a profile: one per non-reference strategy. -/
abbrev Coord (F : Fin m → MvPolynomial (Fin n) ℝ) : Type := Σ w, Strat F w

/-- Alice's coordinate `i`, standing for `xᵢ`. -/
abbrev aCoord (i : Fin n) : Coord F := ⟨.alice, i⟩

/-- Bob's coordinate for a node. -/
abbrev bCoord (ν : bobNodes F) : Coord F := ⟨.bob, ν⟩

/-- Critter's coordinate `s`. -/
abbrev cCoord (s : bobNodes F ⊕ Fin m) : Coord F := ⟨.critter, s⟩

/-- `M = 1 + ∑ |coeff(F)|`, a strict bound on the Horner values of `F` on the open simplex. -/
noncomputable abbrev coeffBound (F : MvPolynomial (Fin n) ℝ) : ℝ :=
  1 + ∑ f ∈ F.support, |F.coeff f|

/-- Datta's scale `s` of the nodes of `F j`: `2 M K`, with `K` Bob's number of strategies. -/
noncomputable abbrev scale (F : Fin m → MvPolynomial (Fin n) ℝ) (j : Fin m) : ℝ :=
  2 * coeffBound (F j) * (#(bobNodes F) + 1)

/-- Datta's shift `δ` of the nodes of `F j`: `−M`. -/
noncomputable abbrev shift (F : Fin m → MvPolynomial (Fin n) ℝ) (j : Fin m) : ℝ :=
  -coeffBound (F j)

/-- The probability `1 / (|bobNodes F| + m + 1)` at which Critter's coordinates are fixed: one
over Critter's number of pure strategies. When every `F j` involves a variable this is
`1 / (D + 1)` with `D = chainLength F` (`card_bobNodes_add`); for `n = m = 1` and `F₀ = 0` there
are no chain equations, Critter has `2` strategies and the weight is `1 / 2`. -/
noncomputable abbrev critterWeight (F : Fin m → MvPolynomial (Fin n) ℝ) : ℝ :=
  1 / (#(bobNodes F) + m + 1)

/-- The value `s b + δ` of a node of `F j`, `0` for the root (and for non-nodes). -/
noncomputable def nodeVal (F : Fin m → MvPolynomial (Fin n) ℝ) (j : Fin m) (p : Node n) :
    MvPolynomial (Coord F) ℝ :=
  if h : ⟨j, p⟩ ∈ bobNodes F then C (scale F j) * X (bCoord ⟨_, h⟩) + C (shift F j) else 0

/-- The term standing for `horner (F j) x k e`: the value of the node at which it is read, or the
constant `coeff_e(F j)`. -/
noncomputable def term (F : Fin m → MvPolynomial (Fin n) ℝ) (j : Fin m) (k : ℕ)
    (e : Fin n →₀ ℕ) : MvPolynomial (Coord F) ℝ :=
  (level (degreeVec (F j)) k e).elim (C ((F j).coeff e)) fun i => nodeVal F j ⟨i, e⟩

/-- The chain equation of the node `p = (k, e)` of `F j`:
`s b_p + δ = a_k · term (k, e + 1_k) + term (k + 1, e)`, with left side `0` at the root. -/
noncomputable def chainEq (F : Fin m → MvPolynomial (Fin n) ℝ) (j : Fin m) (p : Node n) :
    MvPolynomial (Coord F) ℝ :=
  nodeVal F j p - (X (aCoord p.var) * term F j p.var (p.expo + Finsupp.single p.var 1) +
    term F j (p.var + 1) p.expo)

/-- The equation `F j = 0`: the chain equation of the root, or `−F j` if `F j` is constant. -/
noncomputable def rootEq (F : Fin m → MvPolynomial (Fin n) ℝ) (j : Fin m) :
    MvPolynomial (Coord F) ℝ :=
  (level (degreeVec (F j)) 0 0).elim (-C ((F j).coeff 0)) fun i => chainEq F j ⟨i, 0⟩

/-- The indifference equations of the three players. -/
noncomputable def equation (F : Fin m → MvPolynomial (Fin n) ℝ) :
    ∀ w, Strat F w → MvPolynomial (Coord F) ℝ
  | .alice, i => if h : i.val < m then X (cCoord (.inr ⟨i, h⟩)) - C (critterWeight F) else 0
  | .bob, ν => X (cCoord (.inl ν)) - C (critterWeight F)
  | .critter, .inl ⟨⟨j, p⟩, _⟩ => chainEq F j p
  | .critter, .inr j => rootEq F j

/-- **Datta's three-player game** for the system `F`, built on Horner's rule. -/
noncomputable def game (F : Fin m → MvPolynomial (Fin n) ℝ) :
    CostGame Who (fun w => Option (Strat F w)) :=
  CostGame.simplexGame (equation F)

/-! ### The strategy counts -/

/-- The number `D = ∑ⱼ (∏ᵢ (1 + d_ij) − 1)` of chain equations, with `d_ij = degreeOf i (F j)`. -/
@[expose] noncomputable def chainLength (F : Fin m → MvPolynomial (Fin n) ℝ) : ℕ :=
  ∑ j, (∏ i, (1 + degreeOf i (F j)) - 1)

/-- The paper's `D = −1 + ∑ⱼ ∏ᵢ (1 + d_ij)` is `chainLength F + m − 1`. -/
theorem chainLength_add (F : Fin m → MvPolynomial (Fin n) ℝ) :
    chainLength F + m = ∑ j, ∏ i, (1 + degreeOf i (F j)) := by
  have h1 : ∀ j, 1 ≤ ∏ i, (1 + degreeOf i (F j)) := fun j =>
    Nat.one_le_iff_ne_zero.2 (prod_ne_zero_iff.2 fun i _ => by omega)
  rw [chainLength]
  calc ∑ j, (∏ i, (1 + degreeOf i (F j)) - 1) + m
      = ∑ j, (∏ i, (1 + degreeOf i (F j)) - 1 + 1) := by simp [sum_add_distrib]
    _ = ∑ j, ∏ i, (1 + degreeOf i (F j)) := sum_congr rfl fun j _ => Nat.sub_add_cancel (h1 j)

theorem card_bobNodes_add (hF : ∀ j, ∃ i, degreeOf i (F j) ≠ 0) :
    #(bobNodes F) + m = chainLength F := by
  have hj : ∀ j, #((nodes (degreeVec (F j))).filter fun p => root (degreeVec (F j)) ≠ some p) + 2 =
      ∏ i, (1 + degreeOf i (F j)) := fun j => by
    obtain ⟨r, hr, hroot⟩ := exists_root (degreeVec (F j)) fun h => by
      obtain ⟨i, hi⟩ := hF j
      exact hi (by simpa using DFunLike.congr_fun h i)
    have hfilter : ((nodes (degreeVec (F j))).filter fun p => root (degreeVec (F j)) ≠ some p) =
        (nodes (degreeVec (F j))).erase r := by
      ext p
      simp [hroot, eq_comm, and_comm]
    have h1 := card_nodes (degreeVec (F j))
    simp only [degreeVec_apply] at h1
    have h2 := card_erase_add_one hr
    rw [hfilter]
    omega
  have := chainLength_add F
  rw [bobNodes, card_sigma] at *
  simp only [← hj, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega

/-- **The strategy counts.** If every `F j` involves a variable, Alice, Bob and Critter have
`n + 1`, `D − m + 1` and `D + 1` pure strategies, with `D = chainLength F`. -/
theorem card_strategies (hF : ∀ j, ∃ i, degreeOf i (F j) ≠ 0) :
    Fintype.card (Option (Strat F .alice)) = n + 1 ∧
      Fintype.card (Option (Strat F .bob)) = chainLength F - m + 1 ∧
      Fintype.card (Option (Strat F .critter)) = chainLength F + 1 := by
  have := card_bobNodes_add hF
  refine ⟨?_, ?_, ?_⟩ <;> simp [Fintype.card_option, Fintype.card_sum] <;> omega

/-! ### Shape of the equations -/

private theorem C_mem_supported {s : Set (Coord F)} (c : ℝ) :
    MvPolynomial.C c ∈ supported ℝ s :=
  mem_supported.2 (by simp [vars_C])

private theorem nodeVal_mem_supported (j : Fin m) (p : Node n) :
    nodeVal F j p ∈ supported ℝ {v : Coord F | v.1 = .bob} := by
  unfold nodeVal
  split_ifs
  · exact add_mem (mul_mem (C_mem_supported _) (X_mem_supported.2 rfl)) (C_mem_supported _)
  · exact zero_mem _

theorem term_mem_supported (j : Fin m) (k : ℕ) (e : Fin n →₀ ℕ) :
    term F j k e ∈ supported ℝ {v : Coord F | v.1 = .bob} := by
  unfold term
  cases level (degreeVec (F j)) k e
  · exact C_mem_supported _
  · exact nodeVal_mem_supported j _

private theorem isBlockAffine_nodeVal (j : Fin m) (p : Node n) :
    IsBlockAffine (nodeVal F j p) := by
  unfold nodeVal
  split_ifs
  · exact ((IsBlockAffine.C _).mul (IsBlockAffine.X _) fun w hw => by
      rw [vars_C] at hw; simp at hw).add (IsBlockAffine.C _)
  · exact IsBlockAffine.zero

theorem isBlockAffine_term (j : Fin m) (k : ℕ) (e : Fin n →₀ ℕ) :
    IsBlockAffine (term F j k e) := by
  unfold term
  cases level (degreeVec (F j)) k e
  · exact IsBlockAffine.C _
  · exact isBlockAffine_nodeVal j _

theorem chainEq_mem_supported (j : Fin m) (p : Node n) :
    chainEq F j p ∈ supported ℝ {v : Coord F | v.1 ≠ .critter} := by
  have hmono := supported_mono (R := ℝ)
    (show {v : Coord F | v.1 = .bob} ⊆ {v | v.1 ≠ .critter} from fun v (hv : v.1 = .bob) => by
      simp [hv])
  exact sub_mem (hmono (nodeVal_mem_supported j p)) (add_mem (mul_mem (X_mem_supported.2 nofun)
    (hmono (term_mem_supported j p.var (p.expo + Finsupp.single p.var 1))))
    (hmono (term_mem_supported j (p.var + 1) p.expo)))

theorem isBlockAffine_chainEq (j : Fin m) (p : Node n) : IsBlockAffine (chainEq F j p) := by
  refine (isBlockAffine_nodeVal j p).sub (((IsBlockAffine.X _).mul
    (isBlockAffine_term j p.var (p.expo + Finsupp.single p.var 1)) fun v hv w hw => ?_).add
    (isBlockAffine_term j (p.var + 1) p.expo))
  rw [vars_X, Finset.mem_singleton] at hv
  have : w.1 = .bob :=
    mem_supported.1 (term_mem_supported j p.var (p.expo + Finsupp.single p.var 1)) hw
  rw [hv, this]
  exact nofun

/-- Each player's equations only involve the other players. -/
theorem mem_supported_equation (w : Who) (t : Strat F w) :
    equation F w t ∈ supported ℝ {v | v.1 ≠ w} := by
  rcases w with _ | _ | _
  · simp only [equation]
    split_ifs
    · exact sub_mem (X_mem_supported.2 nofun) (C_mem_supported _)
    · exact zero_mem _
  · exact sub_mem (X_mem_supported.2 nofun) (C_mem_supported _)
  · rcases t with ⟨⟨j, p⟩, _⟩ | j
    · exact chainEq_mem_supported j p
    · simp only [equation, rootEq]
      cases level (degreeVec (F j)) 0 0
      · exact neg_mem (C_mem_supported _)
      · exact chainEq_mem_supported j _

theorem notMem_vars_equation (w : Who) (t : Strat F w) : ∀ v ∈ (equation F w t).vars, v.1 ≠ w :=
  fun _ hv => (mem_supported.1 (mem_supported_equation w t)) hv

theorem isBlockAffine_equation (w : Who) (t : Strat F w) : IsBlockAffine (equation F w t) := by
  rcases w with _ | _ | _
  · simp only [equation]
    split_ifs
    · exact (IsBlockAffine.X _).sub (IsBlockAffine.C _)
    · exact IsBlockAffine.zero
  · exact (IsBlockAffine.X _).sub (IsBlockAffine.C _)
  · rcases t with ⟨⟨j, p⟩, _⟩ | j
    · exact isBlockAffine_chainEq j p
    · simp only [equation, rootEq]
      cases level (degreeVec (F j)) 0 0
      · exact (IsBlockAffine.C _).neg
      · exact isBlockAffine_chainEq j _

/-! ### Evaluating the chain -/

theorem eval_nodeVal_of_mem {q : Coord F → ℝ} {j : Fin m} {p : Node n}
    (h : ⟨j, p⟩ ∈ bobNodes F) :
    eval q (nodeVal F j p) = scale F j * q (bCoord ⟨_, h⟩) + shift F j := by
  simp [nodeVal, h]

theorem eval_nodeVal_of_notMem {q : Coord F → ℝ} {j : Fin m} {p : Node n}
    (h : ⟨j, p⟩ ∉ bobNodes F) : eval q (nodeVal F j p) = 0 := by
  simp [nodeVal, h]

/-- A term evaluates to its Horner value once the node it is read from does. -/
theorem eval_term {q : Coord F → ℝ} {j : Fin m} {k : ℕ} {e : Fin n →₀ ℕ}
    (h : ∀ i, level (degreeVec (F j)) k e = some i →
      eval q (nodeVal F j ⟨i, e⟩) = horner (F j) (fun i => q (aCoord i)) i e) :
    eval q (term F j k e) = horner (F j) (fun i => q (aCoord i)) k e := by
  rw [term, horner_level]
  cases hl : level (degreeVec (F j)) k e with
  | none => simp
  | some i => exact h i hl

/-- The first successor of a node `(k, e)`, read at `level k (e + 1_k)`, is a node. -/
private theorem mem_nodes_of_level_add_single {d : Fin n →₀ ℕ} {p : Node n} (hp : p ∈ nodes d)
    {i : Fin n} (hi : level d p.var (p.expo + Finsupp.single p.var 1) = some i) :
    ⟨i, p.expo + Finsupp.single p.var 1⟩ ∈ nodes d := by
  obtain ⟨hle, hlt, hz⟩ := mem_nodes.1 hp
  refine mem_nodes_of_level (add_single_le hle hlt) (fun i' hi' => ?_) hi
  have := hz i' (by rw [Fin.lt_def]; exact hi')
  have hne : p.var ≠ i' := fun h => by subst h; omega
  simp [this, hne]

/-- The second successor of a node `(k, e)`, read at `level (k + 1) e`, is a node. -/
private theorem mem_nodes_of_level_succ {d : Fin n →₀ ℕ} {p : Node n} (hp : p ∈ nodes d)
    {i : Fin n} (hi : level d (p.var + 1) p.expo = some i) : ⟨i, p.expo⟩ ∈ nodes d := by
  obtain ⟨hle, -, hz⟩ := mem_nodes.1 hp
  exact mem_nodes_of_level hle (fun i' hi' => hz i' (by rw [Fin.lt_def]; omega)) hi

/-- **The chain determines the node values.** If every chain equation of `F j` holds, every node
of `F j` has value `horner (F j) x k e`; the root has value `0`, so `F j (x) = 0`. -/
theorem eval_nodeVal_of_chainEq {q : Coord F → ℝ} {j : Fin m}
    (hc : ∀ p ∈ nodes (degreeVec (F j)), eval q (chainEq F j p) = 0) :
    ∀ p ∈ nodes (degreeVec (F j)),
      eval q (nodeVal F j p) = horner (F j) (fun i => q (aCoord i)) p.var p.expo := by
  rintro ⟨k, e⟩ hp
  induction k using (_root_.measure fun k : Fin n => n - k.val).wf.induction generalizing e
  rename_i k iht
  let degreeGap (e : Fin n →₀ ℕ) := degreeVec (F j) k - e k
  induction e using (_root_.measure degreeGap).wf.induction
  rename_i e ihs
  have hlt : e k < degreeVec (F j) k := (mem_nodes.1 hp).2.1
  have hce := hc _ hp
  rw [chainEq, map_sub, sub_eq_zero] at hce
  rw [hce, map_add, map_mul, eval_X, horner_eq (F j) _ k e]
  simp only
  congr 2
  · refine eval_term fun i hi => ?_
    have hmem := mem_nodes_of_level_add_single hp hi
    rcases eq_or_lt_of_le (le_of_level_eq_some hi).1 with hik | hik
    · have : k = i := Fin.ext hik
      subst this
      refine ihs _ ?_ hmem
      change degreeGap (e + Finsupp.single k 1) < degreeGap e
      simp only [degreeGap, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
      omega
    · exact iht i (show n - i.val < n - k.val by omega) _ hmem
  · refine eval_term fun i hi => ?_
    have hmem := mem_nodes_of_level_succ hp hi
    exact iht i (show n - i.val < n - k.val by have := (le_of_level_eq_some hi).1; omega) _ hmem

/-! ### Bob's weights -/

theorem coeffBound_pos (F : MvPolynomial (Fin n) ℝ) : 0 < coeffBound F :=
  add_pos_of_pos_of_nonneg one_pos (sum_nonneg fun _ _ => abs_nonneg _)

/-- On `[0, 1]ⁿ` every Horner value of `F` is smaller than `coeffBound F` in absolute value. -/
theorem abs_horner_lt (F : MvPolynomial (Fin n) ℝ) {x : Fin n → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i ≤ 1) (k : ℕ) (e : Fin n →₀ ℕ) : |horner F x k e| < coeffBound F := by
  calc |horner F x k e|
      ≤ ∑ f ∈ F.support with e ≤ f ∧ ∀ i : Fin n, i.val < k → f i = e i,
          |F.coeff f * expoPow x (f - e)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ f ∈ F.support with e ≤ f ∧ ∀ i : Fin n, i.val < k → f i = e i, |F.coeff f| :=
        sum_le_sum fun f _ => by
          rw [abs_mul, abs_of_nonneg (show 0 ≤ expoPow x (f - e) from
            prod_nonneg fun i _ => pow_nonneg (hx0 i) _)]
          exact mul_le_of_le_one_right (abs_nonneg _) (DattaThree.expoPow_le_one hx0 hx1 _)
    _ ≤ ∑ f ∈ F.support, |F.coeff f| :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => abs_nonneg _
    _ < coeffBound F := lt_one_add _

theorem scale_pos (j : Fin m) : 0 < scale F j := by
  have := coeffBound_pos (F j)
  positivity

/-- On the open simplex, Bob's weight `(h − δ) / s` of a node lies in `(0, 1 / K)`. -/
theorem bobWeight_mem {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) (hx1 : ∑ i, x i < 1) (j : Fin m)
    (k : ℕ) (e : Fin n →₀ ℕ) :
    0 < (horner (F j) x k e - shift F j) / scale F j ∧
      (horner (F j) x k e - shift F j) / scale F j < 1 / (#(bobNodes F) + 1) := by
  have hle : ∀ i, x i ≤ 1 := fun i =>
    (single_le_sum (fun j _ => (hx j).le) (mem_univ i)).trans hx1.le
  have hb := abs_lt.1 (abs_horner_lt (F j) (fun i => (hx i).le) hle k e)
  have hM := coeffBound_pos (F j)
  have hK : (0 : ℝ) < #(bobNodes F) + 1 := by positivity
  refine ⟨div_pos (by simp only [shift]; linarith) (scale_pos j), ?_⟩
  rw [div_lt_div_iff₀ (scale_pos j) hK, scale]
  nlinarith

/-! ### The totally mixed equilibria -/

/-- **Datta's three-player construction** (proof of Theorem 5 of [Datta2003], with Critter's
probabilities repaired to `critterWeight F`, one over its number of strategies). The totally
mixed Nash equilibria of `game F` are the profiles `simplexProfile q` such that:
* Alice's weights `x = q ∘ aCoord` lie in the open simplex and solve every `F j = 0`;
* Bob plays each non-root node `(k, e)` of `F j` with probability `(horner (F j) x k e − δ) / s`,
  the rescaled intermediate value of Horner's rule;
* Critter plays `critterWeight F` on its strategies for Bob's nodes and for the equations
  `j < n`;
* Critter's remaining weights are positive, and its non-reference weights sum to less than `1`. -/
theorem isTotallyMixedNash_game_iff (q : Coord F → ℝ) :
    (game F).IsTotallyMixedNash (simplexProfile q) ↔
      ((∀ i, 0 < q (aCoord i)) ∧ ∑ i, q (aCoord i) < 1 ∧
        ∀ j, eval (fun i => q (aCoord i)) (F j) = 0) ∧
      (∀ j p (h : ⟨j, p⟩ ∈ bobNodes F), q (bCoord ⟨_, h⟩) =
        (horner (F j) (fun i => q (aCoord i)) p.var p.expo - shift F j) / scale F j) ∧
      (∀ ν, q (cCoord (.inl ν)) = critterWeight F) ∧
      (∀ j : Fin m, j.val < n → q (cCoord (.inr j)) = critterWeight F) ∧
      (∀ j, 0 < q (cCoord (.inr j))) ∧ ∑ s, q (cCoord s) < 1 := by
  rw [game, CostGame.isTotallyMixedNash_simplexGame_iff isBlockAffine_equation
    notMem_vars_equation]
  have hroot : ∀ {j : Fin m} {p : Node n}, root (degreeVec (F j)) = some p →
      ∃ i, level (degreeVec (F j)) 0 0 = some i ∧ p = ⟨i, 0⟩ := fun hr => by
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 hr
    exact ⟨i, hi, rfl⟩
  have hmem0 : ∀ {j : Fin m} {i : Fin n}, level (degreeVec (F j)) 0 0 = some i →
      (⟨i, 0⟩ : Node n) ∈ nodes (degreeVec (F j)) := fun hl =>
    mem_nodes_of_level zero_le (fun _ _ => rfl) hl
  have hnot0 : ∀ {j : Fin m} {i : Fin n}, level (degreeVec (F j)) 0 0 = some i →
      (⟨j, ⟨i, 0⟩⟩ : Σ _ : Fin m, Node n) ∉ bobNodes F := fun hl h =>
    (mem_bobNodes.1 h).2 (by simp [root, hl])
  constructor
  · rintro ⟨hpos, hsum, heq⟩
    have hchain : ∀ j, ∀ p ∈ nodes (degreeVec (F j)), eval q (chainEq F j p) = 0 := by
      intro j p hp
      by_cases hr : root (degreeVec (F j)) = some p
      · obtain ⟨i, hl, rfl⟩ := hroot hr
        simpa [equation, rootEq, hl] using heq .critter (.inr j)
      · exact heq .critter (.inl ⟨⟨j, p⟩, mem_bobNodes.2 ⟨hp, hr⟩⟩)
    have hval := fun j => eval_nodeVal_of_chainEq (hchain j)
    refine ⟨⟨fun i => hpos _, hsum .alice, fun j => ?_⟩, fun j p h => ?_, fun ν => ?_,
      fun j hj => ?_, fun j => hpos _, hsum .critter⟩
    · rw [← horner_zero, horner_level]
      cases hl : level (degreeVec (F j)) 0 0 with
      | none => simpa [equation, rootEq, hl] using heq .critter (.inr j)
      | some i =>
        rw [Option.elim, ← hval j _ (hmem0 hl), eval_nodeVal_of_notMem (hnot0 hl)]
    · rw [eq_div_iff (scale_pos j).ne', ← hval j p (mem_bobNodes.1 h).1, eval_nodeVal_of_mem h]
      ring
    · simpa only [equation, map_sub, eval_X, eval_C, sub_eq_zero] using heq .bob ν
    · simpa only [equation, j.isLt, ↓reduceDIte, map_sub, eval_X, eval_C, sub_eq_zero] using
        heq .alice ⟨j, hj⟩
  · rintro ⟨⟨ha, hasum, hF0⟩, hb, hcb, hca, hcpos, hcsum⟩
    have hval : ∀ j, ∀ p ∈ nodes (degreeVec (F j)),
        eval q (nodeVal F j p) = horner (F j) (fun i => q (aCoord i)) p.var p.expo := by
      intro j p hp
      by_cases h : ⟨j, p⟩ ∈ bobNodes F
      · rw [eval_nodeVal_of_mem h, hb j p h, mul_div_cancel₀ _ (scale_pos j).ne']
        ring
      · obtain ⟨i, hl, rfl⟩ := hroot (not_not.1 fun hr => h (mem_bobNodes.2 ⟨hp, hr⟩))
        have := horner_level (F j) (fun i => q (aCoord i)) 0 0
        rw [hl, Option.elim, horner_zero, hF0] at this
        exact (eval_nodeVal_of_notMem h).trans this
    have hchain : ∀ j, ∀ p ∈ nodes (degreeVec (F j)), eval q (chainEq F j p) = 0 := by
      intro j p hp
      rw [chainEq, map_sub, map_add, map_mul, eval_X, hval j p hp,
        eval_term fun i hi => hval j _ (mem_nodes_of_level_add_single hp hi),
        eval_term fun i hi => hval j _ (mem_nodes_of_level_succ hp hi), sub_eq_zero]
      exact horner_eq (F j) _ p.var p.expo
    refine ⟨fun v => ?_, fun w => ?_, fun w t => ?_⟩
    · rcases v with ⟨_ | _ | _, t⟩
      · exact ha t
      · obtain ⟨⟨j, p⟩, h⟩ := t
        rw [hb j p h]
        exact (bobWeight_mem ha hasum j _ _).1
      · rcases t with e | j
        · exact (hcb e).symm ▸ by positivity
        · exact hcpos j
    · rcases w with _ | _ | _
      · exact hasum
      · calc ∑ ν : bobNodes F, q (bCoord ν)
            ≤ ∑ _ν : bobNodes F, 1 / ((#(bobNodes F) : ℝ) + 1) := sum_le_sum fun ν _ => by
              obtain ⟨⟨j, p⟩, h⟩ := ν
              rw [hb j p h]
              exact (bobWeight_mem ha hasum j _ _).2.le
          _ = #(bobNodes F) / ((#(bobNodes F) : ℝ) + 1) := by simp [div_eq_mul_inv]
          _ < 1 := by
              rw [div_lt_one (by positivity)]
              linarith
      · exact hcsum
    · rcases w with _ | _ | _
      · simp only [equation]
        split_ifs with h
        · simp [hca _ (show (⟨t, h⟩ : Fin m).val < n from t.isLt)]
        · simp
      · simp [equation, hcb]
      · rcases t with ⟨⟨j, p⟩, h⟩ | j
        · exact hchain j p (mem_bobNodes.1 h).1
        · simp only [equation, rootEq]
          cases hl : level (degreeVec (F j)) 0 0 with
          | none =>
            have := horner_level (F j) (fun i => q (aCoord i)) 0 0
            rw [hl, Option.elim, horner_zero, hF0] at this
            simp [← this]
          | some i => exact hchain j _ (hmem0 hl)

/-! ### Comparison with the shared-table games -/

/-- **The Horner game against the shared-table games.** For any table `E`, the game
`DattaThree.game E F` gives Bob and Critter each exactly `|E| + m − D` more pure strategies than
`game F`, with `D = chainLength F`. So the table game is smaller for both players iff
`|E| + m < D`, and larger for both iff `D < |E| + m`. -/
theorem card_table_sub_card (hF : ∀ j, ∃ i, degreeOf i (F j) ≠ 0) (E : Finset (Fin n →₀ ℕ)) :
    (Fintype.card (Option (DattaThree.Strat E m .bob)) : ℤ) -
        Fintype.card (Option (Strat F .bob)) = #E + m - chainLength F ∧
      (Fintype.card (Option (DattaThree.Strat E m .critter)) : ℤ) -
        Fintype.card (Option (Strat F .critter)) = #E + m - chainLength F := by
  obtain ⟨-, hb, hc⟩ := card_strategies hF
  obtain ⟨-, hb', hc'⟩ := DattaThree.card_strategies (E := E) (m := m) (n := n)
  have := card_bobNodes_add hF
  rw [hb, hc, hb', hc']
  constructor <;> push_cast [show m ≤ chainLength F by omega] <;> ring

/-- The sparse table has at most `D + 1` exponents, so `DattaThree.game (sparseTable F) F` has at
most `m + 1` more strategies per player than `game F`. -/
theorem card_sparseTable_le (F : Fin m → MvPolynomial (Fin n) ℝ) :
    #(DattaThree.sparseTable F) ≤ chainLength F + 1 := by
  have := DattaThree.card_sparseTable_add_le F
  have := chainLength_add F
  omega

/-- For equations of degree `d` in every variable, `D = m ((d + 1)ⁿ − 1)`. -/
theorem chainLength_of_degreeOf_eq {d : ℕ} (h : ∀ j i, degreeOf i (F j) = d) :
    chainLength F = m * ((d + 1) ^ n - 1) := by
  simp [chainLength, h, add_comm]

/-- **The full box against the Horner chain.** For equations of degree `d` in every variable,
with `N = (d + 1)ⁿ`, the shared-table game on the full box `{0, …, d}ⁿ` (Bob and Critter have
`N + 1` and `N + m + 1` strategies) is smaller than the Horner game iff `(m − 1) N > 2m`. -/
theorem pow_add_lt_chainLength_iff {d : ℕ} (h : ∀ j i, degreeOf i (F j) = d) :
    (d + 1) ^ n + m < chainLength F ↔ 2 * m < (m - 1) * (d + 1) ^ n := by
  rw [chainLength_of_degreeOf_eq h]
  have hN : 1 ≤ (d + 1) ^ n := Nat.one_le_pow _ _ (Nat.succ_pos d)
  generalize (d + 1) ^ n = N at *
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have h1 : m ≤ m * N := Nat.le_mul_of_pos_right m hN
  have h2 : N ≤ m * N := Nat.le_mul_of_pos_left N hm
  rw [Nat.mul_sub_one, Nat.sub_one_mul]
  omega

end Cslib.GameTheory.DattaHorner
