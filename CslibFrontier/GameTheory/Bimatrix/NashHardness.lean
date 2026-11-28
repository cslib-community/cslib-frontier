/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.GameTheory.Bimatrix.FNP
public import CslibFrontier.GameTheory.Bimatrix.Symmetric
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Logics.Propositional.CNF.Compact
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# NP-hardness of Nash equilibrium decision problems

This module formalizes the `NP`-hardness direction of [Papadimitriou2007], Section 2.2.2,
Theorem 2.3 (p. 33; originally Gilboa and Zemel, with the symmetric SAT reduction of Conitzer and
Sandholm sketched on p. 33): even for symmetric two-player games, deciding whether a game admits

1. at least two distinct mixed Nash equilibria (`BimatrixCode.SymGameHasTwoNash`),
2. a mixed Nash equilibrium in which player 1 receives payoff at least `u`
   (`BimatrixCode.SymGameHasNashPayoffGe`),
3. a mixed Nash equilibrium in which the two players receive total payoff at least `u`
   (`BimatrixCode.SymGameHasNashTotalPayoffGe`),
4. a mixed Nash equilibrium whose support has size strictly greater than `k`
   (`BimatrixCode.SymGameHasNashSupportGt`),
5. a mixed Nash equilibrium whose support contains a given pure strategy `s`
   (`BimatrixCode.SymGameHasNashSupportContains`), or
6. a mixed Nash equilibrium whose support omits a given pure strategy `s`
   (`BimatrixCode.SymGameHasNashSupportOmits`)

is `NP`-hard under native multi-tape Turing-machine polynomial-time many-one reductions from `SAT`.
Proving `NP` membership (`InNP`) for these six real-valued Nash decision problems (completing
`NP`-completeness) remains open under #7789.

## Construction

For a CNF formula `φ : CNF (Fin N)` with `2 ≤ N`, `BimatrixGame.gilboaZemelGame N φ` is the
symmetric two-player game `⟨A, Aᵀ⟩` on `GilboaZemelStrategy N φ.length` (literal strategies
`lit v b`, variable-penalty strategies `var v`, clause-penalty strategies `cl c`, and default
strategy `default`) with integer payoffs:

* `A (lit v b) (lit v' b') = 0` if `v = v' ∧ b ≠ b'`, else `N - 1`;
* `A (lit v b) other = -2` for `other ∈ {var, cl, default}`;
* `A (var v) (lit v' b') = 0` if `v = v'`, else `N`; `A (var v) other = -1`;
* `A (cl c) (lit v' b') = 0` if `(v', b') ∈ φ[c]`, else `N`; `A (cl c) other = -1`;
* `A default s = 1` for all `s`.

The theorem `BimatrixGame.isNash_gilboaZemelGame_iff` classifies **all** mixed Nash equilibria
(symmetric and asymmetric alike): `(x, y)` is a Nash equilibrium of `gilboaZemelGame N φ` if and
only if either `(x, y) = (Pi.single .default 1, Pi.single .default 1)` (payoffs `(1, 1)`, support
`{.default}` of size `1`), or `x = y = gilboaZemelAssignmentStrategy φ.length α` for a satisfying
truth assignment `α` of `φ` (payoffs `(N - 1, N - 1)`, support `{lit v (α v)}` of size `N`).

Compacting an arbitrary `φ : CNF ℕ` and padding with three forced-true dummy variables `0, 1, 2`
ensures `N ≥ 3` (hence `N - 1 ≥ 2 > 1`, total payoff `2(N - 1) ≥ 4 > 2`, support size `N ≥ 3 > 1`,
and `lit 0 true` in every satisfying support) and yields a single polynomial-time computable
symmetric `BimatrixCode` reducing `SAT` to all six problems simultaneously.

## Main definitions

* `Cslib.GameTheory.BimatrixGame.GilboaZemelStrategy`, `gilboaZemelGame`,
  `gilboaZemelAssignmentStrategy`: the Conitzer–Sandholm symmetric game for a CNF formula and the
  uniform mixed strategy on a truth assignment.
* `Cslib.GameTheory.BimatrixThresholdInstance`, `encBimatrixThresholdInstance`: encoded pair of a
  rational bimatrix game and a rational payoff threshold.
* `Cslib.GameTheory.BimatrixSupportBoundInstance`, `encBimatrixSupportBoundInstance`: encoded pair
  of a rational bimatrix game and a binary natural support-size threshold.
* `Cslib.GameTheory.BimatrixStrategyIndexInstance`, `encBimatrixStrategyIndexInstance`: encoded
  pair of a rational bimatrix game and a binary natural pure-strategy index.
* `Cslib.GameTheory.BimatrixCode.SymGameHasTwoNash`, `SymGameHasNashPayoffGe`,
  `SymGameHasNashTotalPayoffGe`, `SymGameHasNashSupportGt`, `SymGameHasNashSupportContains`,
  `SymGameHasNashSupportOmits`: the six symmetric two-player Nash decision problems of
  [Papadimitriou2007], Theorem 2.3 (p. 33).

## Main results

* `Cslib.GameTheory.BimatrixGame.isNash_gilboaZemelGame_iff`: complete classification of all
  (symmetric and asymmetric) mixed Nash equilibria of `gilboaZemelGame N φ` for `2 ≤ N`.
* `Cslib.GameTheory.BimatrixCode.polyTimeReducible_SAT_SymGameHasTwoNash`,
  `polyTimeReducible_SAT_SymGameHasNashPayoffGe`,
  `polyTimeReducible_SAT_SymGameHasNashTotalPayoffGe`,
  `polyTimeReducible_SAT_SymGameHasNashSupportGt`,
  `polyTimeReducible_SAT_SymGameHasNashSupportContains`,
  `polyTimeReducible_SAT_SymGameHasNashSupportOmits`: polynomial-time many-one reductions from
  `SAT` to all six problems.
* `Cslib.GameTheory.BimatrixCode.SymGameHasTwoNash_npHard`, `SymGameHasNashPayoffGe_npHard`,
  `SymGameHasNashTotalPayoffGe_npHard`, `SymGameHasNashSupportGt_npHard`,
  `SymGameHasNashSupportContains_npHard`, `SymGameHasNashSupportOmits_npHard`: `NP`-hardness of
  all six Nash equilibrium decision problems on symmetric two-player rational games
  ([Papadimitriou2007], Theorem 2.3, p. 33; `InNP` remains open under #7789).

## References

* [C. H. Papadimitriou, *The Complexity of Finding Nash Equilibria*][Papadimitriou2007],
  Section 2.2.2, Theorem 2.3, p. 33
-/

public section

open Finset Matrix

namespace Cslib.GameTheory.BimatrixGame

/-! ### Section 1: The Conitzer–Sandholm symmetric game for CNF formulas -/

section GilboaZemelGame

open Cslib.Logic.PL

/-- Pure strategies of the Conitzer–Sandholm symmetric game for a CNF formula with `N` variables
and `M` clauses ([Papadimitriou2007], Section 2.2.2, p. 33). -/
inductive GilboaZemelStrategy (N M : ℕ) where
  /-- Literal `(v, b)` for variable `v : Fin N` and polarity `b : Bool`. -/
  | lit (v : Fin N) (b : Bool)
  /-- Variable-penalty strategy for variable `v : Fin N`. -/
  | var (v : Fin N)
  /-- Clause-penalty strategy for clause `c : Fin M`. -/
  | cl (c : Fin M)
  /-- Default strategy (denoted `d` in [Papadimitriou2007], p. 33). -/
  | default
  deriving DecidableEq, Repr

private def gilboaZemelStrategyEquiv (N M : ℕ) :
    GilboaZemelStrategy N M ≃ (Fin N × Bool) ⊕ Fin N ⊕ Fin M ⊕ Unit where
  toFun
    | .lit v b => Sum.inl (v, b)
    | .var v => Sum.inr (Sum.inl v)
    | .cl c => Sum.inr (Sum.inr (Sum.inl c))
    | .default => Sum.inr (Sum.inr (Sum.inr ()))
  invFun
    | Sum.inl (v, b) => .lit v b
    | Sum.inr (Sum.inl v) => .var v
    | Sum.inr (Sum.inr (Sum.inl c)) => .cl c
    | Sum.inr (Sum.inr (Sum.inr ())) => .default
  left_inv s := by cases s <;> rfl
  right_inv x := by
    rcases x with ⟨v, b⟩ | v | c | ⟨⟩ <;> rfl

instance (N M : ℕ) : Fintype (GilboaZemelStrategy N M) :=
  Fintype.ofEquiv ((Fin N × Bool) ⊕ Fin N ⊕ Fin M ⊕ Unit)
    { toFun := fun
        | Sum.inl (v, b) => .lit v b
        | Sum.inr (Sum.inl v) => .var v
        | Sum.inr (Sum.inr (Sum.inl c)) => .cl c
        | Sum.inr (Sum.inr (Sum.inr ())) => .default
      invFun := fun
        | .lit v b => Sum.inl (v, b)
        | .var v => Sum.inr (Sum.inl v)
        | .cl c => Sum.inr (Sum.inr (Sum.inl c))
        | .default => Sum.inr (Sum.inr (Sum.inr ()))
      left_inv := fun x => by rcases x with ⟨v, b⟩ | v | c | ⟨⟩ <;> rfl
      right_inv := fun s => by cases s <;> rfl }

private theorem sum_gilboaZemelStrategy {N M : ℕ} {α : Type*} [AddCommMonoid α]
    (f : GilboaZemelStrategy N M → α) :
    ∑ s : GilboaZemelStrategy N M, f s =
      (∑ v : Fin N, (f (.lit v true) + f (.lit v false))) +
        (∑ v : Fin N, f (.var v)) + (∑ c : Fin M, f (.cl c)) + f .default := by
  rw [Fintype.sum_equiv (gilboaZemelStrategyEquiv N M) f
    (fun x => f ((gilboaZemelStrategyEquiv N M).symm x)) (fun s => by simp)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_unique,
    gilboaZemelStrategyEquiv, Equiv.coe_fn_symm_mk]
  ac_rfl

/-- The Conitzer–Sandholm symmetric bimatrix game `⟨A, Aᵀ⟩` associated to a CNF formula
`φ : CNF (Fin N)` ([Papadimitriou2007], Section 2.2.2, p. 33). -/
noncomputable def gilboaZemelGame (N : ℕ) (φ : CNF (Fin N)) :
    BimatrixGame (GilboaZemelStrategy N φ.length) (GilboaZemelStrategy N φ.length) :=
  ofSymmetric <| Matrix.of fun s₁ s₂ =>
    match s₁, s₂ with
    | .default, _ => 1
    | .lit v b, .lit v' b' => if v = v' ∧ b ≠ b' then 0 else (N : ℝ) - 1
    | .lit _ _, _ => -2
    | .var v, .lit v' _ => if v = v' then 0 else (N : ℝ)
    | .var _, _ => -1
    | .cl c, .lit v' b' => if (v', b') ∈ φ[c.val] then 0 else (N : ℝ)
    | .cl _, _ => -1

theorem isSymmetric_gilboaZemelGame (N : ℕ) (φ : CNF (Fin N)) :
    (gilboaZemelGame N φ).IsSymmetric :=
  isSymmetric_ofSymmetric _

@[simp]
theorem gilboaZemelGame_A_default (N : ℕ) (φ : CNF (Fin N))
    (s : GilboaZemelStrategy N φ.length) :
    (gilboaZemelGame N φ).A .default s = 1 := by
  cases s <;> simp [gilboaZemelGame]

@[simp]
theorem gilboaZemelGame_A_lit_lit (N : ℕ) (φ : CNF (Fin N))
    (v v' : Fin N) (b b' : Bool) :
    (gilboaZemelGame N φ).A (.lit v b) (.lit v' b') =
      if v = v' ∧ b ≠ b' then 0 else (N : ℝ) - 1 := by
  simp [gilboaZemelGame]

@[simp]
theorem gilboaZemelGame_A_lit_var (N : ℕ) (φ : CNF (Fin N)) (v v' : Fin N) (b : Bool) :
    (gilboaZemelGame N φ).A (.lit v b) (.var v') = -2 := by simp [gilboaZemelGame]

@[simp]
theorem gilboaZemelGame_A_lit_cl (N : ℕ) (φ : CNF (Fin N)) (v : Fin N) (b : Bool)
    (c : Fin φ.length) :
    (gilboaZemelGame N φ).A (.lit v b) (.cl c) = -2 := by simp [gilboaZemelGame]

@[simp]
theorem gilboaZemelGame_A_lit_default (N : ℕ) (φ : CNF (Fin N)) (v : Fin N) (b : Bool) :
    (gilboaZemelGame N φ).A (.lit v b) .default = -2 := by simp [gilboaZemelGame]

@[simp]
theorem gilboaZemelGame_A_var_lit (N : ℕ) (φ : CNF (Fin N)) (v v' : Fin N) (b' : Bool) :
    (gilboaZemelGame N φ).A (.var v) (.lit v' b') = if v = v' then 0 else (N : ℝ) := by
  simp [gilboaZemelGame]

@[simp]
theorem gilboaZemelGame_A_var_var (N : ℕ) (φ : CNF (Fin N)) (v v' : Fin N) :
    (gilboaZemelGame N φ).A (.var v) (.var v') = -1 := by simp [gilboaZemelGame]

@[simp]
theorem gilboaZemelGame_A_var_cl (N : ℕ) (φ : CNF (Fin N)) (v : Fin N) (c : Fin φ.length) :
    (gilboaZemelGame N φ).A (.var v) (.cl c) = -1 := by simp [gilboaZemelGame]

@[simp]
theorem gilboaZemelGame_A_var_default (N : ℕ) (φ : CNF (Fin N)) (v : Fin N) :
    (gilboaZemelGame N φ).A (.var v) .default = -1 := by simp [gilboaZemelGame]

@[simp]
theorem gilboaZemelGame_A_cl_lit (N : ℕ) (φ : CNF (Fin N)) (c : Fin φ.length) (v' : Fin N)
    (b' : Bool) :
    (gilboaZemelGame N φ).A (.cl c) (.lit v' b') =
      if (v', b') ∈ φ[c.val] then 0 else (N : ℝ) := by simp [gilboaZemelGame]

@[simp]
theorem gilboaZemelGame_A_cl_var (N : ℕ) (φ : CNF (Fin N)) (c : Fin φ.length) (v' : Fin N) :
    (gilboaZemelGame N φ).A (.cl c) (.var v') = -1 := by simp [gilboaZemelGame]

@[simp]
theorem gilboaZemelGame_A_cl_cl (N : ℕ) (φ : CNF (Fin N)) (c c' : Fin φ.length) :
    (gilboaZemelGame N φ).A (.cl c) (.cl c') = -1 := by simp [gilboaZemelGame]

@[simp]
theorem gilboaZemelGame_A_cl_default (N : ℕ) (φ : CNF (Fin N)) (c : Fin φ.length) :
    (gilboaZemelGame N φ).A (.cl c) .default = -1 := by simp [gilboaZemelGame]

/-- The uniform mixed strategy putting probability `1 / N` on each literal `lit v (α v)` selected
by truth assignment `α : Fin N → Bool`, and `0` on all other strategies. -/
noncomputable def gilboaZemelAssignmentStrategy {N : ℕ} (M : ℕ) (α : Fin N → Bool) :
    GilboaZemelStrategy N M → ℝ
  | .lit v b => if α v = b then 1 / (N : ℝ) else 0
  | _ => 0

@[simp]
theorem gilboaZemelAssignmentStrategy_lit {N : ℕ} (M : ℕ) (α : Fin N → Bool) (v : Fin N)
    (b : Bool) :
    gilboaZemelAssignmentStrategy M α (.lit v b) = if α v = b then 1 / (N : ℝ) else 0 := by
  rw [gilboaZemelAssignmentStrategy]

@[simp]
theorem gilboaZemelAssignmentStrategy_var {N : ℕ} (M : ℕ) (α : Fin N → Bool) (v : Fin N) :
    gilboaZemelAssignmentStrategy M α (.var v) = 0 := by simp [gilboaZemelAssignmentStrategy]

@[simp]
theorem gilboaZemelAssignmentStrategy_cl {N : ℕ} (M : ℕ) (α : Fin N → Bool) (c : Fin M) :
    gilboaZemelAssignmentStrategy M α (.cl c) = 0 := by simp [gilboaZemelAssignmentStrategy]

@[simp]
theorem gilboaZemelAssignmentStrategy_default {N : ℕ} (M : ℕ) (α : Fin N → Bool) :
    gilboaZemelAssignmentStrategy M α .default = 0 := by simp [gilboaZemelAssignmentStrategy]

/-- For `0 < N`, `gilboaZemelAssignmentStrategy M α` is a valid mixed strategy. -/
theorem isMixedStrategy_gilboaZemelAssignmentStrategy {N : ℕ} (hN : 0 < N) (M : ℕ)
    (α : Fin N → Bool) :
    IsMixedStrategy (gilboaZemelAssignmentStrategy M α) := by
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  refine isMixedStrategy_iff.2 ⟨fun s => ?_, ?_⟩
  · cases s with
    | lit v b => simp only [gilboaZemelAssignmentStrategy_lit]; split_ifs <;> positivity
    | _ => simp
  · rw [sum_gilboaZemelStrategy]
    have hpair (v : Fin N) :
        gilboaZemelAssignmentStrategy M α (.lit v true) +
          gilboaZemelAssignmentStrategy M α (.lit v false) = 1 / (N : ℝ) := by
      cases h : α v <;> simp [h]
    simp only [hpair, gilboaZemelAssignmentStrategy_var, gilboaZemelAssignmentStrategy_cl,
      gilboaZemelAssignmentStrategy_default, sum_const_zero, add_zero, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one_div_cancel hNne]

/-- The support of `gilboaZemelAssignmentStrategy M α` has cardinality `N` whenever `0 < N`. -/
theorem ncard_support_gilboaZemelAssignmentStrategy {N : ℕ} (hN : 0 < N) (M : ℕ)
    (α : Fin N → Bool) :
    (Function.support (gilboaZemelAssignmentStrategy M α)).ncard = N := by
  have hpos : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have hsupp : Function.support (gilboaZemelAssignmentStrategy M α) =
      Set.range (fun v : Fin N => GilboaZemelStrategy.lit (M := M) v (α v)) := by
    ext s
    simp only [Function.mem_support, Set.mem_range]
    cases s with
    | lit v b =>
      simp only [gilboaZemelAssignmentStrategy_lit, GilboaZemelStrategy.lit.injEq]
      constructor
      · intro h
        by_cases hb : α v = b
        · exact ⟨v, rfl, hb⟩
        · simp [hb] at h
      · rintro ⟨v', rfl, rfl⟩
        simpa using hpos.ne'
    | var _ => simp
    | cl _ => simp
    | default => simp
  rw [hsupp, Set.ncard_range_of_injective (fun u v h => by injection h), Nat.card_fin]

/-! #### Expected row-payoff formulas for `gilboaZemelGame` -/

/-- Total probability mass a mixed strategy places on literal strategies. -/
private def litMass {N M : ℕ} (y : GilboaZemelStrategy N M → ℝ) : ℝ :=
  ∑ v : Fin N, (y (.lit v true) + y (.lit v false))

/-- Probability mass a mixed strategy places on the two literals of variable `v`. -/
private def varMass {N M : ℕ} (y : GilboaZemelStrategy N M → ℝ) (v : Fin N) : ℝ :=
  y (.lit v true) + y (.lit v false)

private theorem litMass_eq_sum_varMass {N M : ℕ} (y : GilboaZemelStrategy N M → ℝ) :
    litMass y = ∑ v : Fin N, varMass y v := rfl

private theorem nonLitMass_eq {N M : ℕ} {y : GilboaZemelStrategy N M → ℝ}
    (hy : IsMixedStrategy y) :
    (∑ v : Fin N, y (.var v)) + (∑ c : Fin M, y (.cl c)) + y .default = 1 - litMass y := by
  have hsum := hy.sum_eq_one
  rw [sum_gilboaZemelStrategy] at hsum
  dsimp only [litMass]
  linarith

private theorem litMass_nonneg {N M : ℕ} {y : GilboaZemelStrategy N M → ℝ}
    (hy : IsMixedStrategy y) : 0 ≤ litMass y :=
  Finset.sum_nonneg fun _ _ => add_nonneg (hy.nonneg _) (hy.nonneg _)

private theorem litMass_le_one {N M : ℕ} {y : GilboaZemelStrategy N M → ℝ}
    (hy : IsMixedStrategy y) : litMass y ≤ 1 := by
  have hnn : 0 ≤ (∑ v : Fin N, y (.var v)) + (∑ c : Fin M, y (.cl c)) + y .default :=
    add_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => hy.nonneg _)
      (Finset.sum_nonneg fun _ _ => hy.nonneg _)) (hy.nonneg _)
  linarith [nonLitMass_eq hy]

private theorem mulVec_default {N : ℕ} (φ : CNF (Fin N))
    {y : GilboaZemelStrategy N φ.length → ℝ} (hy : IsMixedStrategy y) :
    ((gilboaZemelGame N φ).A *ᵥ y) .default = 1 := by
  simp only [mulVec, dotProduct, gilboaZemelGame_A_default, one_mul, hy.sum_eq_one]

private theorem mulVec_lit {N : ℕ} (φ : CNF (Fin N))
    {y : GilboaZemelStrategy N φ.length → ℝ} (hy : IsMixedStrategy y) (v : Fin N) (b : Bool) :
    ((gilboaZemelGame N φ).A *ᵥ y) (.lit v b) =
      ((N : ℝ) - 1) * (litMass y - y (.lit v (!b))) - 2 * (1 - litMass y) := by
  change ∑ s, (gilboaZemelGame N φ).A (.lit v b) s * y s = _
  rw [sum_gilboaZemelStrategy]
  simp only [gilboaZemelGame_A_lit_lit, gilboaZemelGame_A_lit_var, gilboaZemelGame_A_lit_cl,
    gilboaZemelGame_A_lit_default]
  have hterm (v' : Fin N) :
      (if v = v' ∧ b ≠ true then (0 : ℝ) else (N : ℝ) - 1) * y (.lit v' true) +
        (if v = v' ∧ b ≠ false then (0 : ℝ) else (N : ℝ) - 1) * y (.lit v' false) =
        ((N : ℝ) - 1) * (y (.lit v' true) + y (.lit v' false)) -
          if v' = v then ((N : ℝ) - 1) * y (.lit v (!b)) else 0 := by
    by_cases hv : v' = v
    · subst hv; cases b <;> simp <;> ring
    · have hv' : v ≠ v' := Ne.symm hv
      simp [hv, hv']; ring
  simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  have hnon := nonLitMass_eq hy
  change ((N : ℝ) - 1) * litMass y - ((N : ℝ) - 1) * y (.lit v (!b)) +
      (-2) * ∑ v' : Fin N, y (.var v') + (-2) * ∑ c : Fin φ.length, y (.cl c) +
      (-2) * y .default = _
  linarith

private theorem mulVec_var {N : ℕ} (φ : CNF (Fin N))
    {y : GilboaZemelStrategy N φ.length → ℝ} (hy : IsMixedStrategy y) (v : Fin N) :
    ((gilboaZemelGame N φ).A *ᵥ y) (.var v) =
      (N : ℝ) * (litMass y - varMass y v) - (1 - litMass y) := by
  change ∑ s, (gilboaZemelGame N φ).A (.var v) s * y s = _
  rw [sum_gilboaZemelStrategy]
  simp only [gilboaZemelGame_A_var_lit, gilboaZemelGame_A_var_var, gilboaZemelGame_A_var_cl,
    gilboaZemelGame_A_var_default]
  have hterm (v' : Fin N) :
      (if v = v' then (0 : ℝ) else (N : ℝ)) * y (.lit v' true) +
        (if v = v' then (0 : ℝ) else (N : ℝ)) * y (.lit v' false) =
        (N : ℝ) * (y (.lit v' true) + y (.lit v' false)) -
          if v' = v then (N : ℝ) * varMass y v else 0 := by
    by_cases hv : v' = v
    · subst hv; simp [varMass]
    · have hv' : v ≠ v' := Ne.symm hv
      simp [hv, hv']; ring
  simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  have hnon := nonLitMass_eq hy
  change (N : ℝ) * litMass y - (N : ℝ) * varMass y v +
      (-1) * ∑ v' : Fin N, y (.var v') + (-1) * ∑ c : Fin φ.length, y (.cl c) +
      (-1) * y .default = _
  linarith

private theorem mulVec_cl {N : ℕ} (φ : CNF (Fin N))
    {y : GilboaZemelStrategy N φ.length → ℝ} (hy : IsMixedStrategy y) (c : Fin φ.length) :
    ((gilboaZemelGame N φ).A *ᵥ y) (.cl c) =
      (∑ v' : Fin N,
        ((if (v', true) ∈ φ[c.val] then (0 : ℝ) else (N : ℝ)) * y (.lit v' true) +
          (if (v', false) ∈ φ[c.val] then (0 : ℝ) else (N : ℝ)) * y (.lit v' false))) -
        (1 - litMass y) := by
  change ∑ s, (gilboaZemelGame N φ).A (.cl c) s * y s = _
  rw [sum_gilboaZemelStrategy]
  simp only [gilboaZemelGame_A_cl_lit, gilboaZemelGame_A_cl_var, gilboaZemelGame_A_cl_cl,
    gilboaZemelGame_A_cl_default, ← Finset.mul_sum]
  have hnon := nonLitMass_eq hy
  linarith

/-- Player 1's payoff at the default pure profile `(default, default)` is `1`. -/
theorem payoff₁_gilboaZemelGame_default (N : ℕ) (φ : CNF (Fin N)) :
    (gilboaZemelGame N φ).payoff₁ (Pi.single .default 1) (Pi.single .default 1) = 1 := by
  rw [payoff₁_eq_dotProduct, single_dotProduct, one_mul,
    mulVec_default φ (isMixedStrategy_single .default)]

/-- Player 1's payoff at `(uniform α, uniform α)` is `N - 1` whenever `0 < N`. -/
theorem payoff₁_gilboaZemelGame_assignment {N : ℕ} (hN : 0 < N) (φ : CNF (Fin N))
    (α : Fin N → Bool) :
    (gilboaZemelGame N φ).payoff₁ (gilboaZemelAssignmentStrategy φ.length α)
        (gilboaZemelAssignmentStrategy φ.length α) = (N : ℝ) - 1 := by
  set x := gilboaZemelAssignmentStrategy φ.length α
  have hx : IsMixedStrategy x := isMixedStrategy_gilboaZemelAssignmentStrategy hN φ.length α
  have hxL : litMass x = 1 := by
    have hnon := nonLitMass_eq hx
    simp only [x, gilboaZemelAssignmentStrategy_var, gilboaZemelAssignmentStrategy_cl,
      gilboaZemelAssignmentStrategy_default, sum_const_zero, add_zero] at hnon
    linarith
  rw [payoff₁_eq_dotProduct]
  refine hx.dotProduct_eq_of_forall_pos fun s hs => ?_
  cases s with
  | lit v b =>
    have hb : α v = b := by
      by_contra hne
      simp [x, hne] at hs
    rw [mulVec_lit φ hx v b, hxL]
    have hopp : x (.lit v (!b)) = 0 := by
      simp [x, hb]
    rw [hopp]
    ring
  | var _ => simp [x] at hs
  | cl _ => simp [x] at hs
  | default => simp [x] at hs

/-! #### Complete Nash equilibrium characterization -/

/-- If `x` has zero literal mass, then `default` is the unique pure best response to `x`, forcing
any best response `y` to be `Pi.single .default 1`. -/
private theorem eq_pure_default_of_litMass_eq_zero {N : ℕ} (φ : CNF (Fin N))
    {x y : GilboaZemelStrategy N φ.length → ℝ} (hx : IsMixedStrategy x)
    (hxL : litMass x = 0) (hbr : (gilboaZemelGame N φ).IsBestResponse₁ y x) :
    y = Pi.single .default 1 := by
  have hxLit0 (v : Fin N) (b : Bool) : x (.lit v b) = 0 := by
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun v' _ =>
      add_nonneg (hx.nonneg (.lit v' true)) (hx.nonneg (.lit v' false))).1 hxL v (Finset.mem_univ v)
    cases b
    · linarith [hx.nonneg (.lit v true), hx.nonneg (.lit v false)]
    · linarith [hx.nonneg (.lit v true), hx.nonneg (.lit v false)]
  have hlt (s : GilboaZemelStrategy N φ.length) (hs : s ≠ .default) :
      ((gilboaZemelGame N φ).A *ᵥ x) s < ((gilboaZemelGame N φ).A *ᵥ x) .default := by
    rw [mulVec_default φ hx]
    cases s with
    | lit v b => rw [mulVec_lit φ hx v b, hxL, hxLit0]; norm_num
    | var v => rw [mulVec_var φ hx v, hxL]; simp [varMass, hxLit0]
    | cl c => rw [mulVec_cl φ hx c, hxL]; simp [hxLit0]
    | default => exact absurd rfl hs
  have hy0 (s : GilboaZemelStrategy N φ.length) (hs : s ≠ .default) : y s = 0 := by
    by_contra hne
    have hpos : 0 < y s := lt_of_le_of_ne (hbr.isMixedStrategy.nonneg s) (Ne.symm hne)
    have hopt := isPureBestResponse₁_iff.1 ((isBestResponse₁_iff.1 hbr).2 s hpos) .default
    linarith [hlt s hs]
  funext s
  by_cases hs : s = .default
  · subst hs
    have hsum := hbr.isMixedStrategy.sum_eq_one
    rw [Finset.sum_eq_single .default (fun s' _ hs' => hy0 s' hs') (by simp)] at hsum
    simpa using hsum
  · simp [hs, hy0 s hs]

/-- Step 1: whenever `1 ≤ N` and `y` places mass strictly less than `1` on literals, every Nash
equilibrium `(x, y)` must equal `(Pi.single .default 1, Pi.single .default 1)`. -/
private theorem eq_default_of_litMass_lt_one {N : ℕ} (hN : 1 ≤ N) (φ : CNF (Fin N))
    {x y : GilboaZemelStrategy N φ.length → ℝ}
    (hNash : (gilboaZemelGame N φ).IsNash x y) (hyL : litMass y < 1) :
    x = Pi.single .default 1 ∧ y = Pi.single .default 1 := by
  have hsym := isSymmetric_gilboaZemelGame N φ
  have hbr₁ : (gilboaZemelGame N φ).IsBestResponse₁ x y := (isNash_iff.1 hNash).1
  have hbr₂ : (gilboaZemelGame N φ).IsBestResponse₁ y x :=
    hsym.isBestResponse₂_iff_isBestResponse₁.1 (isNash_iff.1 hNash).2
  have hx := hbr₁.isMixedStrategy
  have hy := hbr₂.isMixedStrategy
  have : Nonempty (Fin N) := Fin.pos_iff_nonempty.1 hN
  obtain ⟨v₀, hv₀min⟩ := Finite.exists_min (varMass y)
  have hN_mul_le : (N : ℝ) * varMass y v₀ ≤ litMass y := by
    calc (N : ℝ) * varMass y v₀
        = ∑ _v : Fin N, varMass y v₀ := by simp [Finset.sum_const]
      _ ≤ ∑ v : Fin N, varMass y v := Finset.sum_le_sum fun v _ => hv₀min v
      _ = litMass y := rfl
  have hvar_ge :
      ((N : ℝ) - 1) * litMass y - (1 - litMass y) ≤ ((gilboaZemelGame N φ).A *ᵥ y) (.var v₀) := by
    rw [mulVec_var φ hy v₀]
    nlinarith
  have hlit_lt (v : Fin N) (b : Bool) :
      ((gilboaZemelGame N φ).A *ᵥ y) (.lit v b) < ((gilboaZemelGame N φ).A *ᵥ y) (.var v₀) := by
    rw [mulVec_lit φ hy v b]
    have hN1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hprod : 0 ≤ ((N : ℝ) - 1) * y (.lit v (!b)) := mul_nonneg hN1 (hy.nonneg _)
    linarith
  have hxLit0 (v : Fin N) (b : Bool) : x (.lit v b) = 0 := by
    by_contra hne
    have hpos : 0 < x (.lit v b) := lt_of_le_of_ne (hx.nonneg _) (Ne.symm hne)
    have hopt :=
      isPureBestResponse₁_iff.1 ((isBestResponse₁_iff.1 hbr₁).2 (.lit v b) hpos) (.var v₀)
    linarith [hlit_lt v b]
  have hxL0 : litMass x = 0 := Finset.sum_eq_zero fun v _ => by simp [hxLit0]
  have hy_eq : y = Pi.single .default 1 := eq_pure_default_of_litMass_eq_zero φ hx hxL0 hbr₂
  have hyL0 : litMass y = 0 := by
    rw [hy_eq]
    exact Finset.sum_eq_zero fun v _ => by simp
  have hx_eq : x = Pi.single .default 1 := eq_pure_default_of_litMass_eq_zero φ hy hyL0 hbr₁
  exact ⟨hx_eq, hy_eq⟩

/-- Step 3 half: when `2 ≤ N`, `x` is a best response to `y`, and both have full literal mass `1`,
every variable has `varMass y v = 1 / N`, the equilibrium payoff is `N - 1`, and opposite literals
to `supp(x)` have probability `0` under `y`. -/
private theorem varMass_eq_and_opp_zero {N : ℕ} (hN : 2 ≤ N) (φ : CNF (Fin N))
    {x y : GilboaZemelStrategy N φ.length → ℝ}
    (hbr : (gilboaZemelGame N φ).IsBestResponse₁ x y) (hy : IsMixedStrategy y)
    (hxL : litMass x = 1) (hyL : litMass y = 1) :
    (∀ v : Fin N, varMass y v = 1 / (N : ℝ)) ∧
      (gilboaZemelGame N φ).payoff₁ x y = (N : ℝ) - 1 ∧
      ∀ v : Fin N, ∀ b : Bool, 0 < x (.lit v b) → y (.lit v (!b)) = 0 := by
  have hx := hbr.isMixedStrategy
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1pos : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hexLit : ∃ v : Fin N, ∃ b : Bool, 0 < x (.lit v b) := by
    by_contra hall
    push Not at hall
    have h0 : litMass x = 0 := Finset.sum_eq_zero fun v _ => by
      have ht : x (.lit v true) = 0 := le_antisymm (hall v true) (hx.nonneg _)
      have hf : x (.lit v false) = 0 := le_antisymm (hall v false) (hx.nonneg _)
      linarith
    linarith
  obtain ⟨v₀, b₀, hv₀pos⟩ := hexLit
  have hpay_le : (gilboaZemelGame N φ).payoff₁ x y ≤ (N : ℝ) - 1 := by
    rw [hbr.payoff₁_eq_of_pos hv₀pos, mulVec_lit φ hy v₀ b₀, hyL]
    have hprod : 0 ≤ ((N : ℝ) - 1) * y (.lit v₀ (!b₀)) := mul_nonneg hN1pos.le (hy.nonneg _)
    linarith
  have hvar_ge (v : Fin N) : (1 : ℝ) ≤ (N : ℝ) * varMass y v := by
    have hle := (hbr.le_payoff₁ (.var v)).trans hpay_le
    rw [mulVec_var φ hy v, hyL] at hle
    linarith
  have hvar_eq (v : Fin N) : (N : ℝ) * varMass y v = 1 := by
    have hsum_eq : ∑ u : Fin N, ((N : ℝ) * varMass y u - 1) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← litMass_eq_sum_varMass, hyL,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hall0 := (Finset.sum_eq_zero_iff_of_nonneg fun u _ => sub_nonneg.2 (hvar_ge u)).1 hsum_eq
    linarith [hall0 v (Finset.mem_univ v)]
  have hvar_div (v : Fin N) : varMass y v = 1 / (N : ℝ) := by
    rw [eq_div_iff hNpos.ne', mul_comm]
    exact hvar_eq v
  have hpay_eq : (gilboaZemelGame N φ).payoff₁ x y = (N : ℝ) - 1 := by
    have hle := hbr.le_payoff₁ (.var ⟨0, by omega⟩)
    rw [mulVec_var φ hy ⟨0, by omega⟩, hyL] at hle
    have h0 := hvar_eq ⟨0, by omega⟩
    linarith
  refine ⟨hvar_div, hpay_eq, fun v b hpos => ?_⟩
  have heq := hbr.payoff₁_eq_of_pos hpos
  rw [hpay_eq, mulVec_lit φ hy v b, hyL] at heq
  have hmul0 : ((N : ℝ) - 1) * y (.lit v (!b)) = 0 := by linarith
  exact (mul_eq_zero.1 hmul0).resolve_left hN1pos.ne'

/-- **Complete mixed Nash equilibrium characterization for `gilboaZemelGame`**
([Papadimitriou2007], Section 2.2.2, p. 33): for any `N ≥ 2` and `φ : CNF (Fin N)`, a pair `(x, y)`
is a mixed Nash equilibrium of `gilboaZemelGame N φ` (symmetric or asymmetric) if and only if
either `(x, y) = (Pi.single .default 1, Pi.single .default 1)` or there exists a satisfying truth
assignment `α` of `φ` with `x = y = gilboaZemelAssignmentStrategy φ.length α`. -/
theorem isNash_gilboaZemelGame_iff {N : ℕ} (hN : 2 ≤ N) (φ : CNF (Fin N))
    {x y : GilboaZemelStrategy N φ.length → ℝ} :
    (gilboaZemelGame N φ).IsNash x y ↔
      (x = Pi.single .default 1 ∧ y = Pi.single .default 1) ∨
        ∃ α : Fin N → Bool, φ.eval α = true ∧
          x = gilboaZemelAssignmentStrategy φ.length α ∧
          y = gilboaZemelAssignmentStrategy φ.length α := by
  have hsym := isSymmetric_gilboaZemelGame N φ
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  constructor
  · intro hNash
    have hbr₁ : (gilboaZemelGame N φ).IsBestResponse₁ x y := (isNash_iff.1 hNash).1
    have hbr₂ : (gilboaZemelGame N φ).IsBestResponse₁ y x :=
      hsym.isBestResponse₂_iff_isBestResponse₁.1 (isNash_iff.1 hNash).2
    have hx := hbr₁.isMixedStrategy
    have hy := hbr₂.isMixedStrategy
    by_cases hyL : litMass y < 1
    · exact Or.inl (eq_default_of_litMass_lt_one (by omega) φ hNash hyL)
    · by_cases hxL : litMass x < 1
      · obtain ⟨hy', hx'⟩ :=
          eq_default_of_litMass_lt_one (by omega) φ (hsym.isNash_comm.1 hNash) hxL
        exact Or.inl ⟨hx', hy'⟩
      · have hyL1 : litMass y = 1 := le_antisymm (litMass_le_one hy) (not_lt.1 hyL)
        have hxL1 : litMass x = 1 := le_antisymm (litMass_le_one hx) (not_lt.1 hxL)
        obtain ⟨hyVar, hpay₁, hyOpp⟩ := varMass_eq_and_opp_zero hN φ hbr₁ hy hxL1 hyL1
        obtain ⟨hxVar, -, hxOpp⟩ := varMass_eq_and_opp_zero hN φ hbr₂ hx hyL1 hxL1
        have hnonZero {z : GilboaZemelStrategy N φ.length → ℝ} (hz : IsMixedStrategy z)
            (hzL : litMass z = 1) :
            (∀ v, z (.var v) = 0) ∧ (∀ c, z (.cl c) = 0) ∧ z .default = 0 := by
          have hnon := nonLitMass_eq hz
          rw [hzL, sub_self] at hnon
          have hvnn : 0 ≤ ∑ v : Fin N, z (.var v) := Finset.sum_nonneg fun _ _ => hz.nonneg _
          have hcnn : 0 ≤ ∑ c : Fin φ.length, z (.cl c) := Finset.sum_nonneg fun _ _ => hz.nonneg _
          have hdnn : 0 ≤ z .default := hz.nonneg _
          refine ⟨fun v => (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => hz.nonneg _).1
              (by linarith) v (Finset.mem_univ v),
            fun c => (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => hz.nonneg _).1
              (by linarith) c (Finset.mem_univ c),
            by linarith⟩
        obtain ⟨hxVar0, hxCl0, hxDef0⟩ := hnonZero hx hxL1
        obtain ⟨hyVar0, hyCl0, hyDef0⟩ := hnonZero hy hyL1
        let α : Fin N → Bool := fun v => decide (0 < x (.lit v true))
        have hxyLit (v : Fin N) (b : Bool) :
            x (.lit v b) = gilboaZemelAssignmentStrategy φ.length α (.lit v b) ∧
              y (.lit v b) = gilboaZemelAssignmentStrategy φ.length α (.lit v b) := by
          have hxV : x (.lit v true) + x (.lit v false) = 1 / (N : ℝ) := hxVar v
          have hyV : y (.lit v true) + y (.lit v false) = 1 / (N : ℝ) := hyVar v
          have hinvPos : (0 : ℝ) < 1 / (N : ℝ) := by positivity
          by_cases hxt : 0 < x (.lit v true)
          · have hαv : α v = true := decide_eq_true hxt
            have hyf0 : y (.lit v false) = 0 := hyOpp v true hxt
            have hyt : y (.lit v true) = 1 / (N : ℝ) := by linarith
            have hxf0 : x (.lit v false) = 0 := hxOpp v true (by linarith)
            have hxtEq : x (.lit v true) = 1 / (N : ℝ) := by linarith
            cases b
            · simp only [gilboaZemelAssignmentStrategy_lit, hαv, Bool.true_eq_false, ↓reduceIte,
                hxf0, hyf0, and_self]
            · simp only [gilboaZemelAssignmentStrategy_lit, hαv, ↓reduceIte, hxtEq, hyt, and_self]
          · have hαv : α v = false := decide_eq_false hxt
            have hxt0 : x (.lit v true) = 0 := le_antisymm (not_lt.1 hxt) (hx.nonneg _)
            have hxfEq : x (.lit v false) = 1 / (N : ℝ) := by linarith
            have hyt0 : y (.lit v true) = 0 := hyOpp v false (by linarith)
            have hyfEq : y (.lit v false) = 1 / (N : ℝ) := by linarith
            cases b
            · simp only [gilboaZemelAssignmentStrategy_lit, hαv, ↓reduceIte, hxfEq, hyfEq, and_self]
            · simp only [gilboaZemelAssignmentStrategy_lit, hαv, Bool.false_eq_true, ↓reduceIte,
                hxt0, hyt0, and_self]
        have hxEq : x = gilboaZemelAssignmentStrategy φ.length α := funext fun s => by
          cases s with
          | lit v b => exact (hxyLit v b).1
          | var v => exact hxVar0 v
          | cl c => exact hxCl0 c
          | default => exact hxDef0
        have hyEq : y = gilboaZemelAssignmentStrategy φ.length α := funext fun s => by
          cases s with
          | lit v b => exact (hxyLit v b).2
          | var v => exact hyVar0 v
          | cl c => exact hyCl0 c
          | default => exact hyDef0
        refine Or.inr ⟨α, ?_, hxEq, hyEq⟩
        rw [CNF.eval_eq_true_iff]
        intro cl hcl
        obtain ⟨c, rfl⟩ := List.mem_iff_get.1 hcl
        by_contra hfalse
        have hnotMem : ∀ v : Fin N, (v, α v) ∉ φ[c.val] := fun v hv =>
          hfalse (Clause.eval_eq_true_iff α φ[c.val] |>.2 ⟨(v, α v), hv, rfl⟩)
        have hcl_le : ((gilboaZemelGame N φ).A *ᵥ y) (.cl c) ≤ (N : ℝ) - 1 := by
          rw [← hpay₁]; exact hbr₁.le_payoff₁ (.cl c)
        rw [mulVec_cl φ hy c, hyL1, sub_self, sub_zero, hyEq] at hcl_le
        have hterm (v : Fin N) :
            (if (v, true) ∈ φ[c.val] then (0 : ℝ) else (N : ℝ)) *
                gilboaZemelAssignmentStrategy φ.length α (.lit v true) +
              (if (v, false) ∈ φ[c.val] then (0 : ℝ) else (N : ℝ)) *
                gilboaZemelAssignmentStrategy φ.length α (.lit v false) = 1 := by
          cases hα : α v
          · have hnm : (v, false) ∉ φ[c.val] := by simpa [hα] using hnotMem v
            simp only [gilboaZemelAssignmentStrategy_lit, hα, Bool.false_eq_true, ↓reduceIte,
              mul_zero, zero_add, hnm, mul_one_div_cancel hNpos.ne']
          · have hnm : (v, true) ∉ φ[c.val] := by simpa [hα] using hnotMem v
            simp only [gilboaZemelAssignmentStrategy_lit, hα, Bool.true_eq_false, ↓reduceIte,
              mul_zero, add_zero, hnm, mul_one_div_cancel hNpos.ne']
        simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_one] at hcl_le
        linarith
  · rintro (⟨rfl, rfl⟩ | ⟨α, hα, rfl, rfl⟩)
    · rw [← IsSymmetricNash, hsym.isSymmetricNash_iff]
      have hd : IsMixedStrategy (Pi.single (.default : GilboaZemelStrategy N φ.length) (1 : ℝ)) :=
        isMixedStrategy_single (.default : GilboaZemelStrategy N φ.length)
      have hdL : litMass (Pi.single (.default : GilboaZemelStrategy N φ.length) (1 : ℝ)) = 0 :=
        Finset.sum_eq_zero fun v _ => by simp
      refine ⟨hd, fun s => ?_⟩
      rw [payoff₁_gilboaZemelGame_default]
      cases s with
      | lit v b => rw [mulVec_lit φ hd v b, hdL]; simp; norm_num
      | var v => rw [mulVec_var φ hd v, hdL]; simp [varMass]
      | cl c => rw [mulVec_cl φ hd c, hdL]; simp
      | default => rw [mulVec_default φ hd]
    · rw [← IsSymmetricNash, hsym.isSymmetricNash_iff]
      set x := gilboaZemelAssignmentStrategy φ.length α
      have hx : IsMixedStrategy x :=
        isMixedStrategy_gilboaZemelAssignmentStrategy (by omega) φ.length α
      have hxL : litMass x = 1 := by
        have hnon := nonLitMass_eq hx
        simp only [x, gilboaZemelAssignmentStrategy_var, gilboaZemelAssignmentStrategy_cl,
          gilboaZemelAssignmentStrategy_default, sum_const_zero, add_zero] at hnon
        linarith
      refine ⟨hx, fun s => ?_⟩
      rw [payoff₁_gilboaZemelGame_assignment (by omega) φ α]
      cases s with
      | lit v b =>
        rw [mulVec_lit φ hx v b, hxL]
        have hN1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by
          have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          linarith
        have hprod : 0 ≤ ((N : ℝ) - 1) * x (.lit v (!b)) := mul_nonneg hN1 (hx.nonneg _)
        linarith
      | var v =>
        rw [mulVec_var φ hx v, hxL]
        have hv : varMass x v = 1 / (N : ℝ) := by
          dsimp only [varMass, x]
          cases h : α v <;> simp [h]
        rw [hv, mul_sub, mul_one, mul_one_div_cancel hNpos.ne']
        linarith
      | cl c =>
        rw [mulVec_cl φ hx c, hxL, sub_self, sub_zero]
        have hcSat : φ[c.val].eval α = true :=
          (CNF.eval_eq_true_iff α φ).1 hα _ (List.getElem_mem c.isLt)
        obtain ⟨⟨v₀, b₀⟩, hv₀mem, hv₀eq⟩ := (Clause.eval_eq_true_iff α φ[c.val]).1 hcSat
        have hv₀mem' : (v₀, α v₀) ∈ φ[c.val] := hv₀eq ▸ hv₀mem
        have hle_term (v : Fin N) :
            (if (v, true) ∈ φ[c.val] then (0 : ℝ) else (N : ℝ)) * x (.lit v true) +
              (if (v, false) ∈ φ[c.val] then (0 : ℝ) else (N : ℝ)) * x (.lit v false) ≤
              if v = v₀ then 0 else 1 := by
          by_cases hvv : v = v₀
          · subst hvv
            cases hαv : α v
            · have hm : (v, false) ∈ φ[c.val] := by simpa [hαv] using hv₀mem'
              simp only [x, gilboaZemelAssignmentStrategy_lit, hαv, Bool.false_eq_true, ↓reduceIte,
                mul_zero, zero_add, hm, zero_mul, le_refl]
            · have hm : (v, true) ∈ φ[c.val] := by simpa [hαv] using hv₀mem'
              simp only [x, gilboaZemelAssignmentStrategy_lit, hαv, Bool.true_eq_false, ↓reduceIte,
                mul_zero, add_zero, hm, zero_mul, le_refl]
          · simp only [hvv, ↓reduceIte]
            cases hαv : α v
            · simp only [x, gilboaZemelAssignmentStrategy_lit, hαv, Bool.false_eq_true, ↓reduceIte,
                mul_zero, zero_add]
              split_ifs
              · norm_num
              · rw [mul_one_div_cancel hNpos.ne']
            · simp only [x, gilboaZemelAssignmentStrategy_lit, hαv, Bool.true_eq_false, ↓reduceIte,
                mul_zero, add_zero]
              split_ifs
              · norm_num
              · rw [mul_one_div_cancel hNpos.ne']
        have hsum_le := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hle_term v
        have hrhs : ∑ v : Fin N, (if v = v₀ then (0 : ℝ) else 1) = (N : ℝ) - 1 := by
          have hrew (v : Fin N) :
              (if v = v₀ then (0 : ℝ) else 1) = 1 - if v = v₀ then 1 else 0 := by
            split_ifs <;> ring
          simp only [hrew, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ,
            ↓reduceIte]
        linarith
      | default =>
        rw [mulVec_default φ hx]
        have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith

end GilboaZemelGame

end Cslib.GameTheory.BimatrixGame

/-! ### Section 2: Encoded symmetric two-player Nash decision problems and NP-hardness -/

namespace Cslib.GameTheory

open Cslib Cslib.Complexity Cslib.GameTheory.BimatrixGame Cslib.Logic.PL
open Turing.MultiTapeTM ComputableInPolyTime

/-- An instance of a bimatrix-game Nash payoff-threshold decision problem: an explicitly presented
two-player rational game paired with a rational utility threshold `threshold`. -/
@[ext]
structure BimatrixThresholdInstance where
  /-- The explicitly presented two-player rational payoff matrices. -/
  game : BimatrixCode
  /-- The rational payoff lower bound. -/
  threshold : ℚ
  deriving DecidableEq, Repr

/-- Framed `encBimatrix` followed by binary `encRat`, encoding `BimatrixThresholdInstance`. -/
enc_structure encBimatrixThresholdInstance : BimatrixThresholdInstance where
  game : encBimatrix,
  threshold : encRat

attribute [fun_prop] encBimatrixThresholdInstance_game_polyTime
  encBimatrixThresholdInstance_threshold_polyTime encBimatrixThresholdInstance_mk_polyTime

/-- An instance of a bimatrix-game Nash support-size decision problem: an explicitly presented
two-player rational game paired with a binary natural support-size threshold `bound`. -/
@[ext]
structure BimatrixSupportBoundInstance where
  /-- The explicitly presented two-player rational payoff matrices. -/
  game : BimatrixCode
  /-- The strict lower bound on support cardinality (`bound < support size`). -/
  bound : ℕ
  deriving DecidableEq, Repr

/-- Framed `encBimatrix` followed by binary `encNat`, encoding `BimatrixSupportBoundInstance`. -/
enc_structure encBimatrixSupportBoundInstance : BimatrixSupportBoundInstance where
  game : encBimatrix,
  bound : encNat

attribute [fun_prop] encBimatrixSupportBoundInstance_game_polyTime
  encBimatrixSupportBoundInstance_bound_polyTime encBimatrixSupportBoundInstance_mk_polyTime

/-- An instance of a bimatrix-game Nash strategy-support decision problem: an explicitly presented
two-player rational game paired with a binary natural pure-strategy index `strategy`. -/
@[ext]
structure BimatrixStrategyIndexInstance where
  /-- The explicitly presented two-player rational payoff matrices. -/
  game : BimatrixCode
  /-- Pure-strategy index of player 1 (valid when `strategy < game.rows`). -/
  strategy : ℕ
  deriving DecidableEq, Repr

/-- Framed `encBimatrix` followed by binary `encNat`, encoding
`BimatrixStrategyIndexInstance`. -/
enc_structure encBimatrixStrategyIndexInstance : BimatrixStrategyIndexInstance where
  game : encBimatrix,
  strategy : encNat

attribute [fun_prop] encBimatrixStrategyIndexInstance_game_polyTime
  encBimatrixStrategyIndexInstance_strategy_polyTime encBimatrixStrategyIndexInstance_mk_polyTime

namespace BimatrixCode

/-- **Second Nash equilibrium** ([Papadimitriou2007], Theorem 2.3, bullet 1, p. 33): well-formed
symmetric rational bimatrix codes (`B = Aᵀ`) admitting at least two distinct mixed Nash
equilibria. -/
@[expose] def SymGameHasTwoNash : Set BimatrixCode :=
  {c | c.IsSymmetric ∧
    ∃ x₁ y₁ x₂ y₂, c.toSymGame.IsNash x₁ y₁ ∧ c.toSymGame.IsNash x₂ y₂ ∧
      (x₁, y₁) ≠ (x₂, y₂)}

/-- **Player-1 Nash payoff lower bound** ([Papadimitriou2007], Theorem 2.3, bullet 2, p. 33):
symmetric rational bimatrix games admitting a mixed Nash equilibrium in which player 1 receives
expected payoff at least `threshold`. -/
@[expose] def SymGameHasNashPayoffGe : Set BimatrixThresholdInstance :=
  {inst | inst.game.IsSymmetric ∧
    ∃ x y, inst.game.toSymGame.IsNash x y ∧
      (inst.threshold : ℝ) ≤ inst.game.toSymGame.payoff₁ x y}

/-- **Total Nash payoff lower bound** ([Papadimitriou2007], Theorem 2.3, bullet 3, p. 33):
symmetric rational bimatrix games admitting a mixed Nash equilibrium in which the sum of both
players' expected payoffs is at least `threshold`. -/
@[expose] def SymGameHasNashTotalPayoffGe : Set BimatrixThresholdInstance :=
  {inst | inst.game.IsSymmetric ∧
    ∃ x y, inst.game.toSymGame.IsNash x y ∧
      (inst.threshold : ℝ) ≤
        inst.game.toSymGame.payoff₁ x y + inst.game.toSymGame.payoff₂ x y}

/-- **Large-support Nash equilibrium** ([Papadimitriou2007], Theorem 2.3, bullet 4, p. 33):
symmetric rational bimatrix games admitting a mixed Nash equilibrium whose player-1 support
cardinality is strictly greater than `bound` (by `IsSymmetric.isNash_comm`, equivalent to player 2
or either player having support size `> bound`). -/
@[expose] def SymGameHasNashSupportGt : Set BimatrixSupportBoundInstance :=
  {inst | inst.game.IsSymmetric ∧
    ∃ x y, inst.game.toSymGame.IsNash x y ∧ inst.bound < (Function.support x).ncard}

/-- **Nash equilibrium containing a strategy** ([Papadimitriou2007], Theorem 2.3, bullet 5, p. 33):
symmetric rational bimatrix games and a valid pure-strategy index `strategy < game.rows` played
with positive probability by player 1 in some mixed Nash equilibrium (by `IsSymmetric.isNash_comm`,
equivalent for player 2 or either player). -/
@[expose] def SymGameHasNashSupportContains : Set BimatrixStrategyIndexInstance :=
  {inst | inst.game.IsSymmetric ∧ ∃ hs : inst.strategy < inst.game.rows,
    ∃ x y, inst.game.toSymGame.IsNash x y ∧ 0 < x ⟨inst.strategy, hs⟩}

/-- **Nash equilibrium omitting a strategy** ([Papadimitriou2007], Theorem 2.3, bullet 6, p. 33):
symmetric rational bimatrix games and a valid pure-strategy index `strategy < game.rows` played
with probability `0` by player 1 in some mixed Nash equilibrium (by `IsSymmetric.isNash_comm`,
equivalent for player 2 or either player). -/
@[expose] def SymGameHasNashSupportOmits : Set BimatrixStrategyIndexInstance :=
  {inst | inst.game.IsSymmetric ∧ ∃ hs : inst.strategy < inst.game.rows,
    ∃ x y, inst.game.toSymGame.IsNash x y ∧ x ⟨inst.strategy, hs⟩ = 0}

/-! #### Relabeling invariance for symmetric bimatrix games -/

private theorem isMixedStrategy_comp_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (x : β → ℝ) :
    IsMixedStrategy (x ∘ e) ↔ IsMixedStrategy x := by
  simp only [isMixedStrategy_iff, Function.comp_apply, e.forall_congr_left,
    Equiv.apply_symm_apply, Fintype.sum_equiv e _ _ (fun _ => rfl)]

private theorem payoff₁_relabel {α β : Type*} [Fintype α] [Fintype β]
    {G₁ : BimatrixGame α α} {G₂ : BimatrixGame β β} (e : α ≃ β)
    (hA : ∀ i j, G₁.A i j = G₂.A (e i) (e j)) (x y : β → ℝ) :
    G₁.payoff₁ (x ∘ e) (y ∘ e) = G₂.payoff₁ x y := by
  simp only [payoff₁_eq_dotProduct, dotProduct, mulVec, Function.comp_apply, hA]
  exact Fintype.sum_equiv e _ _ fun i => by
    congr 1
    exact Fintype.sum_equiv e _ _ fun j => rfl

private theorem isBestResponse₁_relabel {α β : Type*} [Fintype α] [Fintype β]
    {G₁ : BimatrixGame α α} {G₂ : BimatrixGame β β} (e : α ≃ β)
    (hA : ∀ i j, G₁.A i j = G₂.A (e i) (e j)) {x y : β → ℝ} :
    G₁.IsBestResponse₁ (x ∘ e) (y ∘ e) ↔ G₂.IsBestResponse₁ x y := by
  have hmul (i : α) : (G₁.A *ᵥ (y ∘ e)) i = (G₂.A *ᵥ y) (e i) := by
    simp only [mulVec, dotProduct, Function.comp_apply, hA]
    exact Fintype.sum_equiv e _ _ fun _ => rfl
  rw [isBestResponse₁_iff_le_payoff₁, isBestResponse₁_iff_le_payoff₁,
    isMixedStrategy_comp_equiv, payoff₁_relabel e hA]
  refine and_congr_right fun _ => ⟨fun h j => ?_, fun h i => ?_⟩
  · simpa only [hmul, Equiv.apply_symm_apply] using h (e.symm j)
  · simpa only [hmul] using h (e i)

private theorem isNash_relabel_symm {α β : Type*} [Fintype α] [Fintype β]
    {G₁ : BimatrixGame α α} {G₂ : BimatrixGame β β} (h₁ : G₁.IsSymmetric) (h₂ : G₂.IsSymmetric)
    (e : α ≃ β) (hA : ∀ i j, G₁.A i j = G₂.A (e i) (e j)) {x y : β → ℝ} :
    G₁.IsNash (x ∘ e) (y ∘ e) ↔ G₂.IsNash x y := by
  rw [isNash_iff, isNash_iff, h₁.isBestResponse₂_iff_isBestResponse₁,
    h₂.isBestResponse₂_iff_isBestResponse₁, isBestResponse₁_relabel e hA,
    isBestResponse₁_relabel e hA]

private theorem ncard_support_comp_equiv {α β : Type*} (e : α ≃ β) (x : β → ℝ) :
    (Function.support (x ∘ e)).ncard = (Function.support x).ncard := by
  have himg : Function.support (x ∘ e) = e.symm '' Function.support x := by
    ext a
    simp only [Function.mem_support, Function.comp_apply, Set.mem_image]
    exact ⟨fun h => ⟨e a, h, e.symm_apply_apply a⟩, fun ⟨b, hb, hba⟩ => by simpa [← hba] using hb⟩
  rw [himg, Set.ncard_image_of_injective _ e.symm.injective]

/-! #### Padded CNF and computable Conitzer–Sandholm matrix code -/

/-- Padded CNF formula over `ℕ`: three forced-true dummy unit clauses on variables `0, 1, 2`
followed by `φ.compact` shifted up by `3`. -/
private def paddedCNF (φ : CNF ℕ) : CNF ℕ :=
  [[(0, true)], [(1, true)], [(2, true)]] ++ φ.compact.relabel (· + 3)

/-- Padded variable count `φ.vars.length + 3` (always at least `3`). -/
private def paddedNumVars (φ : CNF ℕ) : ℕ :=
  φ.vars.length + 3

private theorem paddedNumVars_ge_three (φ : CNF ℕ) : 3 ≤ paddedNumVars φ :=
  Nat.le_add_left 3 _

private theorem mem_vars_paddedCNF_lt (φ : CNF ℕ) {v : ℕ} (hv : v ∈ (paddedCNF φ).vars) :
    v < paddedNumVars φ := by
  obtain ⟨c, hc, b, hmem⟩ := CNF.mem_vars.1 hv
  simp only [paddedCNF, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl) | hc'
  · simp only [List.mem_singleton, Prod.mk.injEq] at hmem
    rw [hmem.1]; dsimp [paddedNumVars]; omega
  · simp only [List.mem_singleton, Prod.mk.injEq] at hmem
    rw [hmem.1]; dsimp [paddedNumVars]; omega
  · simp only [List.mem_singleton, Prod.mk.injEq] at hmem
    rw [hmem.1]; dsimp [paddedNumVars]; omega
  · simp only [CNF.relabel, Clause.relabel, List.mem_map] at hc'
    obtain ⟨c₀, hc₀, rfl⟩ := hc'
    simp only [List.mem_map] at hmem
    obtain ⟨⟨u, b₀⟩, hu, heq⟩ := hmem
    have hu_eq : u + 3 = v := (Prod.mk.inj heq).1
    have hu_lt : u < φ.vars.length :=
      CNF.mem_vars_compact_lt φ (CNF.mem_vars.2 ⟨c₀, hc₀, b₀, hu⟩)
    dsimp [paddedNumVars]
    omega

private def toFinVar (N : ℕ) (hN : 0 < N) (v : ℕ) : Fin N :=
  if hv : v < N then ⟨v, hv⟩ else ⟨0, hN⟩

/-- Padded CNF formula over `Fin (paddedNumVars φ)`. -/
private def paddedCNFFin (φ : CNF ℕ) : CNF (Fin (paddedNumVars φ)) :=
  (paddedCNF φ).relabel (toFinVar (paddedNumVars φ) (by dsimp [paddedNumVars]; omega))

private theorem paddedCNFFin_length (φ : CNF ℕ) :
    (paddedCNFFin φ).length = (paddedCNF φ).length := by
  simp [paddedCNFFin, CNF.relabel]

private theorem mem_paddedCNFFin_getElem_iff (φ : CNF ℕ) (c : Fin (paddedCNFFin φ).length)
    (v : Fin (paddedNumVars φ)) (b : Bool) :
    (v, b) ∈ (paddedCNFFin φ)[c.val] ↔
      (v.val, b) ∈ (paddedCNF φ).getD c.val [] := by
  have hc' : c.val < (paddedCNF φ).length := by rw [← paddedCNFFin_length]; exact c.isLt
  rw [List.getD_eq_getElem _ _ hc']
  simp only [paddedCNFFin, CNF.relabel, List.getElem_map, Clause.relabel, List.mem_map]
  constructor
  · rintro ⟨⟨u, b₀⟩, hu, heq⟩
    have hv : toFinVar (paddedNumVars φ) (by dsimp [paddedNumVars]; omega) u = v :=
      (Prod.mk.inj heq).1
    have hb : b₀ = b := (Prod.mk.inj heq).2
    subst hb
    have hu_lt : u < paddedNumVars φ :=
      mem_vars_paddedCNF_lt φ (CNF.mem_vars.2 ⟨(paddedCNF φ)[c.val], List.getElem_mem hc', b₀, hu⟩)
    have hval : (toFinVar (paddedNumVars φ) (by dsimp [paddedNumVars]; omega) u).val = u := by
      simp [toFinVar, hu_lt]
    have huv : u = v.val := by rw [← hval, hv]
    rwa [← huv]
  · intro hmem
    refine ⟨(v.val, b), hmem, ?_⟩
    ext <;> simp [toFinVar, v.isLt]

private theorem paddedCNFFin_eval_zero_true (φ : CNF ℕ) {α : Fin (paddedNumVars φ) → Bool}
    (hα : (paddedCNFFin φ).eval α = true) :
    α ⟨0, by dsimp [paddedNumVars]; omega⟩ = true := by
  have hmem : [(⟨0, by dsimp [paddedNumVars]; omega⟩, true)] ∈ paddedCNFFin φ := by
    simp only [paddedCNFFin, paddedCNF, CNF.relabel, Clause.relabel, List.cons_append,
      List.map_cons, Prod.map_apply, id_eq, toFinVar, paddedNumVars]
    exact List.mem_cons_self
  have hc := (CNF.eval_eq_true_iff α (paddedCNFFin φ)).1 hα _ hmem
  simpa [Clause.eval_eq_true_iff] using hc

private theorem satisfiable_paddedCNFFin_iff (φ : CNF ℕ) :
    (paddedCNFFin φ).Satisfiable ↔ φ.Satisfiable := by
  rw [← CNF.satisfiable_compact φ]
  constructor
  · rintro ⟨α, hα⟩
    rw [paddedCNFFin, CNF.eval_relabel, paddedCNF, CNF.eval_append, Bool.and_eq_true,
      CNF.eval_relabel] at hα
    exact ⟨(α ∘ toFinVar (paddedNumVars φ) (by dsimp [paddedNumVars]; omega)) ∘ (· + 3), hα.2⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨fun v => if v.val < 3 then true else σ (v.val - 3), ?_⟩
    rw [paddedCNFFin, CNF.eval_relabel, paddedCNF, CNF.eval_append, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · simp [CNF.eval, Clause.eval, Literal.eval, toFinVar, paddedNumVars]
    · rw [CNF.eval_relabel]
      have hcongr :
          φ.compact.eval
              (((fun v : Fin (paddedNumVars φ) => if v.val < 3 then true else σ (v.val - 3)) ∘
                toFinVar (paddedNumVars φ) (by dsimp [paddedNumVars]; omega)) ∘ (· + 3)) =
            φ.compact.eval σ := by
        apply CNF.eval_congr
        intro u hu
        have hlt : u + 3 < paddedNumVars φ := by
          have := CNF.mem_vars_compact_lt φ hu
          dsimp [paddedNumVars]
          omega
        simp only [Function.comp_apply, toFinVar, hlt, ↓reduceDIte]
        have hge : ¬ (u + 3 < 3) := by omega
        simp [hge]
      rwa [hcongr]

/-- Entry `(i, j)` of player 1's payoff matrix for the padded Conitzer–Sandholm game on
`1 + 3 * N + ψ.length` pure strategies:
* `0`: `default`;
* `1 + 2 * v`: `lit v true`, `1 + 2 * v + 1`: `lit v false` (`v < N`);
* `1 + 2 * N + v`: `var v` (`v < N`);
* `1 + 3 * N + c`: `cl c` (`c < ψ.length`). -/
private def gzEntry (N : ℕ) (ψ : CNF ℕ) (i j : ℕ) : ℚ :=
  if i = 0 then 1
  else if i < 1 + 2 * N then
    if 1 ≤ j ∧ j < 1 + 2 * N then
      if (i - 1) / 2 = (j - 1) / 2 ∧ i ≠ j then 0 else ((N - 1 : ℕ) : ℚ)
    else -2
  else if i < 1 + 3 * N then
    if 1 ≤ j ∧ j < 1 + 2 * N then
      if i - (1 + 2 * N) = (j - 1) / 2 then 0 else (N : ℚ)
    else -1
  else
    if 1 ≤ j ∧ j < 1 + 2 * N then
      if ((j - 1) / 2, decide ((j - 1) % 2 = 0)) ∈ ψ.getD (i - (1 + 3 * N)) [] then 0
      else (N : ℚ)
    else -1

/-- Player 1's `d × d` payoff matrix rows for `(N, ψ)`. -/
private def gzMatA (N : ℕ) (ψ : CNF ℕ) (d : ℕ) : List (List ℚ) :=
  (List.range d).map fun i => (List.range d).map fun j => gzEntry N ψ i j

/-- Player 2's `d × d` payoff matrix rows (`gzMatAᵀ`) for `(N, ψ)`. -/
private def gzMatB (N : ℕ) (ψ : CNF ℕ) (d : ℕ) : List (List ℚ) :=
  (List.range d).map fun i => (List.range d).map fun j => gzEntry N ψ j i

private theorem gzMatA_getD {N d i j : ℕ} {ψ : CNF ℕ} (hi : i < d) (hj : j < d) :
    ((gzMatA N ψ d).getD i []).getD j 0 = gzEntry N ψ i j := by
  unfold gzMatA
  have h1 :
      i < ((List.range d).map fun a => (List.range d).map fun b => gzEntry N ψ a b).length := by
    simp [hi]
  have h2 : j < ((List.range d).map fun b => gzEntry N ψ i b).length := by simp [hj]
  rw [List.getD_eq_getElem _ _ h1, List.getElem_map, List.getElem_range,
    List.getD_eq_getElem _ _ h2, List.getElem_map, List.getElem_range]

private theorem gzMatB_getD {N d i j : ℕ} {ψ : CNF ℕ} (hi : i < d) (hj : j < d) :
    ((gzMatB N ψ d).getD i []).getD j 0 = gzEntry N ψ j i := by
  unfold gzMatB
  have h1 :
      i < ((List.range d).map fun a => (List.range d).map fun b => gzEntry N ψ b a).length := by
    simp [hi]
  have h2 : j < ((List.range d).map fun b => gzEntry N ψ b i).length := by simp [hj]
  rw [List.getD_eq_getElem _ _ h1, List.getElem_map, List.getElem_range,
    List.getD_eq_getElem _ _ h2, List.getElem_map, List.getElem_range]

/-- Symmetric rational `BimatrixCode` (`matB = matAᵀ`) implementing the Conitzer–Sandholm game
for a CNF formula `φ : CNF ℕ`. -/
private def gilboaZemelCode (φ : CNF ℕ) : BimatrixCode :=
  let N := paddedNumVars φ
  let ψ := paddedCNF φ
  let d := 1 + 3 * N + ψ.length
  ⟨gzMatA N ψ d, gzMatB N ψ d⟩

private theorem gilboaZemelCode_rows (φ : CNF ℕ) :
    (gilboaZemelCode φ).rows = 1 + 3 * paddedNumVars φ + (paddedCNF φ).length := by
  simp [gilboaZemelCode, rows, gzMatA]

private theorem gilboaZemelCode_isSymmetric (φ : CNF ℕ) :
    (gilboaZemelCode φ).IsSymmetric := by
  have hd : 0 < 1 + 3 * paddedNumVars φ + (paddedCNF φ).length := by omega
  have hrows : (gilboaZemelCode φ).rows = 1 + 3 * paddedNumVars φ + (paddedCNF φ).length :=
    gilboaZemelCode_rows φ
  have hcols : (gilboaZemelCode φ).cols = 1 + 3 * paddedNumVars φ + (paddedCNF φ).length := by
    simp only [gilboaZemelCode, cols, gzMatA]
    rw [show 1 + 3 * paddedNumVars φ + (paddedCNF φ).length =
      (3 * paddedNumVars φ + (paddedCNF φ).length) + 1 by omega, List.range_succ_eq_map]
    simp
  have hlenA :
      ∀ r ∈ (gilboaZemelCode φ).matA,
        r.length = 1 + 3 * paddedNumVars φ + (paddedCNF φ).length := by
    intro r hr
    simp only [gilboaZemelCode, gzMatA, List.mem_map] at hr
    obtain ⟨_, _, rfl⟩ := hr
    simp
  have hlenB :
      ∀ r ∈ (gilboaZemelCode φ).matB,
        r.length = 1 + 3 * paddedNumVars φ + (paddedCNF φ).length := by
    intro r hr
    simp only [gilboaZemelCode, gzMatB, List.mem_map] at hr
    obtain ⟨_, _, rfl⟩ := hr
    simp
  refine ⟨⟨by omega, by omega, by simp [gilboaZemelCode, rows, gzMatA, gzMatB],
      fun r hr => (hlenA r hr).trans hcols.symm,
      fun r hr => (hlenB r hr).trans hcols.symm⟩, hrows.trans hcols.symm, fun i j => ?_⟩
  have hi : i.val < 1 + 3 * paddedNumVars φ + (paddedCNF φ).length := hrows ▸ i.isLt
  have hj : j.val < 1 + 3 * paddedNumVars φ + (paddedCNF φ).length := hrows ▸ j.isLt
  change ((gzMatB (paddedNumVars φ) (paddedCNF φ) _).getD i.val []).getD j.val 0 =
    ((gzMatA (paddedNumVars φ) (paddedCNF φ) _).getD j.val []).getD i.val 0
  rw [gzMatB_getD hi hj, gzMatA_getD hj hi]

/-- Equivalence between `Fin (gilboaZemelCode φ).rows` and
`GilboaZemelStrategy (paddedNumVars φ) (paddedCNFFin φ).length`, sending `0 ↦ default` and
`1 ↦ lit 0 true`. -/
private def gzEquiv (φ : CNF ℕ) :
    Fin (gilboaZemelCode φ).rows ≃
      GilboaZemelStrategy (paddedNumVars φ) (paddedCNFFin φ).length where
  toFun i :=
    let N := paddedNumVars φ
    if h0 : i.val = 0 then .default
    else if h1 : i.val < 1 + 2 * N then
      .lit ⟨(i.val - 1) / 2, by omega⟩ (decide ((i.val - 1) % 2 = 0))
    else if h2 : i.val < 1 + 3 * N then
      .var ⟨i.val - (1 + 2 * N), by omega⟩
    else
      .cl ⟨i.val - (1 + 3 * N), by
        have hi : i.val < 1 + 3 * N + (paddedCNF φ).length := gilboaZemelCode_rows φ ▸ i.isLt
        rw [paddedCNFFin_length]; omega⟩
  invFun s :=
    let N := paddedNumVars φ
    have hrows := gilboaZemelCode_rows φ
    have hlen := paddedCNFFin_length φ
    match s with
    | .default => ⟨0, by rw [hrows]; omega⟩
    | .lit v true => ⟨1 + 2 * v.val, by rw [hrows]; omega⟩
    | .lit v false => ⟨1 + 2 * v.val + 1, by rw [hrows]; omega⟩
    | .var v => ⟨1 + 2 * N + v.val, by rw [hrows]; omega⟩
    | .cl c => ⟨1 + 3 * N + c.val, by rw [hrows, ← hlen]; omega⟩
  left_inv i := by
    ext
    dsimp only
    split_ifs with h0 h1 h2
    · exact h0.symm
    · cases hmod : decide ((i.val - 1) % 2 = 0)
      · have : (i.val - 1) % 2 ≠ 0 := of_decide_eq_false hmod
        dsimp only; omega
      · have : (i.val - 1) % 2 = 0 := of_decide_eq_true hmod
        dsimp only; omega
    · dsimp only; omega
    · dsimp only; omega
  right_inv s := by
    cases s with
    | default => simp
    | lit v b =>
      cases b
      · have h0 : ¬ (1 + 2 * v.val + 1 = 0) := by omega
        have h1 : 1 + 2 * v.val + 1 < 1 + 2 * paddedNumVars φ := by omega
        simp only [h0, ↓reduceDIte, h1, GilboaZemelStrategy.lit.injEq]
        exact ⟨Fin.ext (by dsimp; omega), decide_eq_false (by omega)⟩
      · have h0 : ¬ (1 + 2 * v.val = 0) := by omega
        have h1 : 1 + 2 * v.val < 1 + 2 * paddedNumVars φ := by omega
        simp only [h0, ↓reduceDIte, h1, GilboaZemelStrategy.lit.injEq]
        exact ⟨Fin.ext (by dsimp; omega), decide_eq_true (by omega)⟩
    | var v =>
      have h0 : ¬ (1 + 2 * paddedNumVars φ + v.val = 0) := by omega
      have h1 : ¬ (1 + 2 * paddedNumVars φ + v.val < 1 + 2 * paddedNumVars φ) := by omega
      have h2 : 1 + 2 * paddedNumVars φ + v.val < 1 + 3 * paddedNumVars φ := by omega
      simp only [h0, ↓reduceDIte, h1, h2, GilboaZemelStrategy.var.injEq]
      exact Fin.ext (by dsimp; omega)
    | cl c =>
      have h0 : ¬ (1 + 3 * paddedNumVars φ + c.val = 0) := by omega
      have h1 : ¬ (1 + 3 * paddedNumVars φ + c.val < 1 + 2 * paddedNumVars φ) := by omega
      have h2 : ¬ (1 + 3 * paddedNumVars φ + c.val < 1 + 3 * paddedNumVars φ) := by omega
      simp only [h0, ↓reduceDIte, h1, h2, GilboaZemelStrategy.cl.injEq]
      exact Fin.ext (by dsimp; omega)

private theorem gzEquiv_zero (φ : CNF ℕ) :
    gzEquiv φ ⟨0, by rw [gilboaZemelCode_rows]; omega⟩ = .default := by
  simp [gzEquiv]

private theorem gzEquiv_one (φ : CNF ℕ) :
    gzEquiv φ ⟨1, by rw [gilboaZemelCode_rows]; have := paddedNumVars_ge_three φ; omega⟩ =
      .lit ⟨0, by have := paddedNumVars_ge_three φ; omega⟩ true := by
  have h1 : 1 < 1 + 2 * paddedNumVars φ := by have := paddedNumVars_ge_three φ; omega
  simp [gzEquiv, h1]

private theorem gilboaZemelCode_A_eq (φ : CNF ℕ) (i j : Fin (gilboaZemelCode φ).rows) :
    (gilboaZemelCode φ).toSymGame.A i j =
      (gilboaZemelGame (paddedNumVars φ) (paddedCNFFin φ)).A (gzEquiv φ i) (gzEquiv φ j) := by
  have hN1 : 1 ≤ paddedNumVars φ := by have := paddedNumVars_ge_three φ; omega
  have hi : i.val < 1 + 3 * paddedNumVars φ + (paddedCNF φ).length :=
    gilboaZemelCode_rows φ ▸ i.isLt
  have hj : j.val < 1 + 3 * paddedNumVars φ + (paddedCNF φ).length :=
    gilboaZemelCode_rows φ ▸ j.isLt
  have hA_lhs :
      (gilboaZemelCode φ).toSymGame.A i j =
        (gzEntry (paddedNumVars φ) (paddedCNF φ) i.val j.val : ℝ) := by
    change (((gzMatA (paddedNumVars φ) (paddedCNF φ) _).getD i.val []).getD j.val 0 : ℝ) = _
    rw [gzMatA_getD hi hj]
  rw [hA_lhs]
  dsimp only [gzEquiv, Equiv.coe_fn_mk, gzEntry]
  by_cases hi0 : i.val = 0
  · simp [hi0]
  · simp only [hi0, ↓reduceIte, ↓reduceDIte]
    by_cases hi1 : i.val < 1 + 2 * paddedNumVars φ
    · simp only [hi1, ↓reduceIte, ↓reduceDIte]
      by_cases hj0 : j.val = 0
      · simp [hj0]
      · simp only [hj0, ↓reduceDIte]
        by_cases hj1 : j.val < 1 + 2 * paddedNumVars φ
        · have hj_ok : 1 ≤ j.val ∧ j.val < 1 + 2 * paddedNumVars φ := by omega
          simp only [hj1, ↓reduceDIte, hj_ok, and_self, ↓reduceIte, gilboaZemelGame_A_lit_lit,
            Fin.mk.injEq]
          have hiff : ((i.val - 1) / 2 = (j.val - 1) / 2 ∧ i.val ≠ j.val) ↔
              ((i.val - 1) / 2 = (j.val - 1) / 2 ∧
                decide ((i.val - 1) % 2 = 0) ≠ decide ((j.val - 1) % 2 = 0)) := by
            constructor
            · rintro ⟨hq, hne⟩
              refine ⟨hq, fun heq => hne ?_⟩
              have hmod : ((i.val - 1) % 2 = 0) ↔ ((j.val - 1) % 2 = 0) :=
                decide_eq_decide.1 heq
              omega
            · rintro ⟨hq, hne⟩
              exact ⟨hq, fun heq => hne (by rw [heq])⟩
          by_cases hcond : (i.val - 1) / 2 = (j.val - 1) / 2 ∧ i.val ≠ j.val
          · simp [hcond, hiff.1 hcond]
          · have hcond' : ¬ ((i.val - 1) / 2 = (j.val - 1) / 2 ∧
                decide ((i.val - 1) % 2 = 0) ≠ decide ((j.val - 1) % 2 = 0)) :=
              fun h => hcond (hiff.2 h)
            simp only [hcond, hcond', ↓reduceIte, Rat.cast_natCast]
            rw [Nat.cast_sub hN1, Nat.cast_one]
        · simp only [hj1, ↓reduceDIte, and_false, ↓reduceIte]
          by_cases hj2 : j.val < 1 + 3 * paddedNumVars φ <;> simp [hj2]
    · simp only [hi1, ↓reduceIte, ↓reduceDIte]
      by_cases hi2 : i.val < 1 + 3 * paddedNumVars φ
      · simp only [hi2, ↓reduceIte, ↓reduceDIte]
        by_cases hj0 : j.val = 0
        · simp [hj0]
        · simp only [hj0, ↓reduceDIte]
          by_cases hj1 : j.val < 1 + 2 * paddedNumVars φ
          · have hj_ok : 1 ≤ j.val ∧ j.val < 1 + 2 * paddedNumVars φ := by omega
            simp only [hj1, ↓reduceDIte, hj_ok, and_self, ↓reduceIte, gilboaZemelGame_A_var_lit,
              Fin.mk.injEq]
            split_ifs <;> simp
          · simp only [hj1, ↓reduceDIte, and_false, ↓reduceIte]
            by_cases hj2 : j.val < 1 + 3 * paddedNumVars φ <;> simp [hj2]
      · simp only [hi2, ↓reduceIte, ↓reduceDIte]
        by_cases hj0 : j.val = 0
        · simp [hj0]
        · simp only [hj0, ↓reduceDIte]
          by_cases hj1 : j.val < 1 + 2 * paddedNumVars φ
          · have hj_ok : 1 ≤ j.val ∧ j.val < 1 + 2 * paddedNumVars φ := by omega
            simp only [hj1, ↓reduceDIte, hj_ok, and_self, ↓reduceIte, gilboaZemelGame_A_cl_lit]
            let cFin : Fin (paddedCNFFin φ).length :=
              ⟨i.val - (1 + 3 * paddedNumVars φ), by rw [paddedCNFFin_length]; omega⟩
            let vFin : Fin (paddedNumVars φ) := ⟨(j.val - 1) / 2, by omega⟩
            have hmemIff :=
              mem_paddedCNFFin_getElem_iff φ cFin vFin (decide ((j.val - 1) % 2 = 0))
            by_cases hm : (vFin, decide ((j.val - 1) % 2 = 0)) ∈ (paddedCNFFin φ)[cFin.val]
            · have hm' :
                  ((j.val - 1) / 2, decide ((j.val - 1) % 2 = 0)) ∈
                    (paddedCNF φ).getD cFin.val [] :=
                hmemIff.1 hm
              simp only [cFin, vFin] at hm hm'
              simp only [hm, hm', ↓reduceIte, Rat.cast_zero]
            · have hm' :
                  ((j.val - 1) / 2, decide ((j.val - 1) % 2 = 0)) ∉
                    (paddedCNF φ).getD cFin.val [] :=
                fun h => hm (hmemIff.2 h)
              simp only [cFin, vFin] at hm hm'
              simp only [hm, hm', ↓reduceIte, Rat.cast_natCast]
          · simp only [hj1, ↓reduceDIte, and_false, ↓reduceIte]
            by_cases hj2 : j.val < 1 + 3 * paddedNumVars φ <;> simp [hj2]

/-- Classification of all mixed Nash equilibria of `(gilboaZemelCode φ).toSymGame` obtained by
transporting `isNash_gilboaZemelGame_iff` along `gzEquiv φ`. -/
private theorem isNash_gilboaZemelCode_iff (φ : CNF ℕ)
    {x y : Fin (gilboaZemelCode φ).rows → ℝ} :
    (gilboaZemelCode φ).toSymGame.IsNash x y ↔
      (x = (Pi.single .default 1) ∘ gzEquiv φ ∧ y = (Pi.single .default 1) ∘ gzEquiv φ) ∨
        ∃ α : Fin (paddedNumVars φ) → Bool, (paddedCNFFin φ).eval α = true ∧
          x = (gilboaZemelAssignmentStrategy (paddedCNFFin φ).length α) ∘ gzEquiv φ ∧
          y = (gilboaZemelAssignmentStrategy (paddedCNFFin φ).length α) ∘ gzEquiv φ := by
  have hsym₁ : (gilboaZemelCode φ).toSymGame.IsSymmetric := rfl
  have hsym₂ := isSymmetric_gilboaZemelGame (paddedNumVars φ) (paddedCNFFin φ)
  have hxComp : (x ∘ (gzEquiv φ).symm) ∘ gzEquiv φ = x := funext fun i => by simp
  have hyComp : (y ∘ (gzEquiv φ).symm) ∘ gzEquiv φ = y := funext fun i => by simp
  have hrel : (gilboaZemelCode φ).toSymGame.IsNash x y ↔
      (gilboaZemelGame (paddedNumVars φ) (paddedCNFFin φ)).IsNash
        (x ∘ (gzEquiv φ).symm) (y ∘ (gzEquiv φ).symm) := by
    rw [← isNash_relabel_symm hsym₁ hsym₂ (gzEquiv φ) (gilboaZemelCode_A_eq φ), hxComp, hyComp]
  rw [hrel, isNash_gilboaZemelGame_iff (by have := paddedNumVars_ge_three φ; omega)]
  have hfunEq (u : Fin (gilboaZemelCode φ).rows → ℝ)
      (v : GilboaZemelStrategy (paddedNumVars φ) (paddedCNFFin φ).length → ℝ) :
      u ∘ (gzEquiv φ).symm = v ↔ u = v ∘ gzEquiv φ :=
    ⟨fun h => by rw [← h]; funext i; simp, fun h => by rw [h]; funext s; simp⟩
  simp only [hfunEq]

/-! #### Semantic equivalences for all six decision problems -/

private theorem gilboaZemelCode_mem_SymGameHasTwoNash_iff (φ : CNF ℕ) :
    φ ∈ SAT ↔ gilboaZemelCode φ ∈ SymGameHasTwoNash := by
  rw [mem_SAT, ← satisfiable_paddedCNFFin_iff φ]
  change _ ↔ (gilboaZemelCode φ).IsSymmetric ∧ _
  rw [and_iff_right (gilboaZemelCode_isSymmetric φ)]
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨(Pi.single .default 1) ∘ gzEquiv φ, (Pi.single .default 1) ∘ gzEquiv φ,
      (gilboaZemelAssignmentStrategy (paddedCNFFin φ).length α) ∘ gzEquiv φ,
      (gilboaZemelAssignmentStrategy (paddedCNFFin φ).length α) ∘ gzEquiv φ,
      (isNash_gilboaZemelCode_iff φ).2 (Or.inl ⟨rfl, rfl⟩),
      (isNash_gilboaZemelCode_iff φ).2 (Or.inr ⟨α, hα, rfl, rfl⟩), ?_⟩
    intro heq
    have h0 := congrFun (Prod.mk.inj heq).1 ⟨0, by rw [gilboaZemelCode_rows]; omega⟩
    simp [gzEquiv_zero] at h0
  · rintro ⟨x₁, y₁, x₂, y₂, h₁, h₂, hne⟩
    rcases (isNash_gilboaZemelCode_iff φ).1 h₁ with ⟨rfl, rfl⟩ | ⟨α, hα, -, -⟩
    · rcases (isNash_gilboaZemelCode_iff φ).1 h₂ with ⟨rfl, rfl⟩ | ⟨α, hα, -, -⟩
      · exact absurd rfl hne
      · exact ⟨α, hα⟩
    · exact ⟨α, hα⟩

private theorem gilboaZemelCode_mem_SymGameHasNashPayoffGe_iff (φ : CNF ℕ) :
    φ ∈ SAT ↔ (⟨gilboaZemelCode φ, 2⟩ : BimatrixThresholdInstance) ∈ SymGameHasNashPayoffGe := by
  rw [mem_SAT, ← satisfiable_paddedCNFFin_iff φ]
  change _ ↔ (gilboaZemelCode φ).IsSymmetric ∧ _
  rw [and_iff_right (gilboaZemelCode_isSymmetric φ)]
  have hN3 : (3 : ℝ) ≤ (paddedNumVars φ : ℝ) := by exact_mod_cast paddedNumVars_ge_three φ
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨_, _, (isNash_gilboaZemelCode_iff φ).2 (Or.inr ⟨α, hα, rfl, rfl⟩), ?_⟩
    rw [payoff₁_relabel (gzEquiv φ) (gilboaZemelCode_A_eq φ),
      payoff₁_gilboaZemelGame_assignment (by have := paddedNumVars_ge_three φ; omega)]
    norm_num
    linarith
  · rintro ⟨x, y, hNash, hpay⟩
    rcases (isNash_gilboaZemelCode_iff φ).1 hNash with ⟨rfl, rfl⟩ | ⟨α, hα, -, -⟩
    · rw [payoff₁_relabel (gzEquiv φ) (gilboaZemelCode_A_eq φ),
        payoff₁_gilboaZemelGame_default] at hpay
      norm_num at hpay
    · exact ⟨α, hα⟩

private theorem gilboaZemelCode_mem_SymGameHasNashTotalPayoffGe_iff (φ : CNF ℕ) :
    φ ∈ SAT ↔
      (⟨gilboaZemelCode φ, 4⟩ : BimatrixThresholdInstance) ∈ SymGameHasNashTotalPayoffGe := by
  rw [mem_SAT, ← satisfiable_paddedCNFFin_iff φ]
  change _ ↔ (gilboaZemelCode φ).IsSymmetric ∧ _
  rw [and_iff_right (gilboaZemelCode_isSymmetric φ)]
  have hsym : (gilboaZemelCode φ).toSymGame.IsSymmetric := rfl
  have hN3 : (3 : ℝ) ≤ (paddedNumVars φ : ℝ) := by exact_mod_cast paddedNumVars_ge_three φ
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨_, _, (isNash_gilboaZemelCode_iff φ).2 (Or.inr ⟨α, hα, rfl, rfl⟩), ?_⟩
    rw [hsym.payoff₂_eq, payoff₁_relabel (gzEquiv φ) (gilboaZemelCode_A_eq φ),
      payoff₁_gilboaZemelGame_assignment (by have := paddedNumVars_ge_three φ; omega)]
    norm_num
    linarith
  · rintro ⟨x, y, hNash, hpay⟩
    rcases (isNash_gilboaZemelCode_iff φ).1 hNash with ⟨rfl, rfl⟩ | ⟨α, hα, -, -⟩
    · rw [hsym.payoff₂_eq, payoff₁_relabel (gzEquiv φ) (gilboaZemelCode_A_eq φ),
        payoff₁_gilboaZemelGame_default] at hpay
      norm_num at hpay
    · exact ⟨α, hα⟩

private theorem gilboaZemelCode_mem_SymGameHasNashSupportGt_iff (φ : CNF ℕ) :
    φ ∈ SAT ↔
      (⟨gilboaZemelCode φ, 1⟩ : BimatrixSupportBoundInstance) ∈ SymGameHasNashSupportGt := by
  rw [mem_SAT, ← satisfiable_paddedCNFFin_iff φ]
  change _ ↔ (gilboaZemelCode φ).IsSymmetric ∧ _
  rw [and_iff_right (gilboaZemelCode_isSymmetric φ)]
  have hN3 := paddedNumVars_ge_three φ
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨_, _, (isNash_gilboaZemelCode_iff φ).2 (Or.inr ⟨α, hα, rfl, rfl⟩), ?_⟩
    rw [ncard_support_comp_equiv, ncard_support_gilboaZemelAssignmentStrategy (by omega)]
    dsimp only
    omega
  · rintro ⟨x, y, hNash, hsupp⟩
    rcases (isNash_gilboaZemelCode_iff φ).1 hNash with ⟨rfl, rfl⟩ | ⟨α, hα, -, -⟩
    · have hsing : Function.support
          (Pi.single (.default : GilboaZemelStrategy (paddedNumVars φ) (paddedCNFFin φ).length)
            (1 : ℝ)) = {.default} := by
        ext s; by_cases hs : s = .default <;> simp [hs]
      rw [ncard_support_comp_equiv, hsing, Set.ncard_singleton] at hsupp
      dsimp only at hsupp
      omega
    · exact ⟨α, hα⟩

private theorem gilboaZemelCode_mem_SymGameHasNashSupportContains_iff (φ : CNF ℕ) :
    φ ∈ SAT ↔
      (⟨gilboaZemelCode φ, 1⟩ : BimatrixStrategyIndexInstance) ∈ SymGameHasNashSupportContains := by
  rw [mem_SAT, ← satisfiable_paddedCNFFin_iff φ]
  change _ ↔ (gilboaZemelCode φ).IsSymmetric ∧ _
  rw [and_iff_right (gilboaZemelCode_isSymmetric φ)]
  have hN3 := paddedNumVars_ge_three φ
  have h1lt : 1 < (gilboaZemelCode φ).rows := by rw [gilboaZemelCode_rows]; omega
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨h1lt, _, _, (isNash_gilboaZemelCode_iff φ).2 (Or.inr ⟨α, hα, rfl, rfl⟩), ?_⟩
    simp only [Function.comp_apply, gzEquiv_one, gilboaZemelAssignmentStrategy_lit,
      paddedCNFFin_eval_zero_true φ hα, ↓reduceIte]
    positivity
  · rintro ⟨hs, x, y, hNash, hpos⟩
    rcases (isNash_gilboaZemelCode_iff φ).1 hNash with ⟨rfl, rfl⟩ | ⟨α, hα, -, -⟩
    · simp only [Function.comp_apply, gzEquiv_one, Pi.single_apply, reduceCtorEq, ↓reduceIte,
        lt_self_iff_false] at hpos
    · exact ⟨α, hα⟩

private theorem gilboaZemelCode_mem_SymGameHasNashSupportOmits_iff (φ : CNF ℕ) :
    φ ∈ SAT ↔
      (⟨gilboaZemelCode φ, 0⟩ : BimatrixStrategyIndexInstance) ∈ SymGameHasNashSupportOmits := by
  rw [mem_SAT, ← satisfiable_paddedCNFFin_iff φ]
  change _ ↔ (gilboaZemelCode φ).IsSymmetric ∧ _
  rw [and_iff_right (gilboaZemelCode_isSymmetric φ)]
  have h0lt : 0 < (gilboaZemelCode φ).rows := by rw [gilboaZemelCode_rows]; omega
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨h0lt, _, _, (isNash_gilboaZemelCode_iff φ).2 (Or.inr ⟨α, hα, rfl, rfl⟩), ?_⟩
    simp [gzEquiv_zero]
  · rintro ⟨hs, x, y, hNash, hzero⟩
    rcases (isNash_gilboaZemelCode_iff φ).1 hNash with ⟨rfl, rfl⟩ | ⟨α, hα, -, -⟩
    · simp [gzEquiv_zero] at hzero
    · exact ⟨α, hα⟩

/-! #### Polynomial-time computability of `gilboaZemelCode` -/

private theorem computableInPolyTime_paddedNumVars :
    ComputableInPolyTime paddedNumVars encCNF encUnary :=
  unary_add' (SAT.computableInPolyTime_vars_length .id') (const 3)

private theorem computableInPolyTime_paddedCNF :
    ComputableInPolyTime paddedCNF encCNF encCNF := by
  have hshift : ComputableInPolyTime (fun v : ℕ => v + 3) encUnary encNat :=
    unary_to_binary.comp (unary_add' id' (const 3))
  have hcomp : ComputableInPolyTime (fun φ : CNF ℕ => φ.compact.relabel (· + 3)) encCNF encCNF :=
    (CNF.computableInPolyTime_relabel hshift).comp (CNF.isPolyTime_compact encNat)
  exact (listAppend (encList (encPair encNat encBool))).comp
    ((const ([[(0, true)], [(1, true)], [(2, true)]] : CNF ℕ)).prod hcomp)

private theorem computableInPolyTime_gzEntry :
    ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) => gzEntry p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair (encPair encUnary encCNF) (encPair encUnary encUnary)) encRat := by
  set enc := encPair (encPair encUnary encCNF) (encPair encUnary encUnary)
  have hN : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) => p.1.1) enc encUnary :=
    (fst encUnary encCNF).comp (fst _ _)
  have hψ : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) => p.1.2) enc encCNF :=
    (snd encUnary encCNF).comp (fst _ _)
  have hi : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) => p.2.1) enc encUnary :=
    (fst encUnary encUnary).comp (snd _ _)
  have hj : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) => p.2.2) enc encUnary :=
    (snd encUnary encUnary).comp (snd _ _)
  have h2N : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) => 1 + 2 * p.1.1) enc encUnary :=
    unary_add' (const 1) (unary_mul' (const 2) hN)
  have h3N : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) => 1 + 3 * p.1.1) enc encUnary :=
    unary_add' (const 1) (unary_mul' (const 3) hN)
  have hiBin : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) => p.2.1) enc encNat :=
    unary_to_binary.comp hi
  have hjBin : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) => p.2.2) enc encNat :=
    unary_to_binary.comp hj
  have hiDiv2 :
      ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) => (p.2.1 - 1) / 2) enc encNat :=
    binary_div' (binary_sub' hiBin (const 1)) (const 2)
  have hjDiv2 :
      ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) => (p.2.2 - 1) / 2) enc encNat :=
    binary_div' (binary_sub' hjBin (const 1)) (const 2)
  have hjMod2 :
      ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) => (p.2.2 - 1) % 2) enc encNat :=
    binary_mod' (binary_sub' hjBin (const 1)) (const 2)
  have hjInLit :
      ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) =>
          decide (1 ≤ p.2.2 ∧ p.2.2 < 1 + 2 * p.1.1)) enc encBool :=
    (bool_and' (unary_le' (const 1) hj) (unary_lt' hj h2N)).of_enc_eq fun p =>
      congrArg encBool (by simp)
  have hNrat : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) => (p.1.1 : ℚ)) enc encRat :=
    rat_natCast.comp (unary_to_binary.comp hN)
  have hN1rat :
      ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) => ((p.1.1 - 1 : ℕ) : ℚ)) enc encRat :=
    rat_natCast.comp (unary_to_binary.comp (unary_sub' hN (const 1)))
  have hOppCond :
      ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) =>
          decide ((p.2.1 - 1) / 2 = (p.2.2 - 1) / 2 ∧ p.2.1 ≠ p.2.2)) enc encBool :=
    (bool_and' (decide_eq' hiDiv2 hjDiv2) (bool_not.comp (decide_eq' hi hj))).of_enc_eq fun p =>
      congrArg encBool (by simp)
  have hVarCond :
      ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) =>
          decide (p.2.1 - (1 + 2 * p.1.1) = (p.2.2 - 1) / 2)) enc encBool :=
    decide_eq' (unary_to_binary.comp (unary_sub' hi h2N)) hjDiv2
  have hClause :
      ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) =>
          p.1.2.getD (p.2.1 - (1 + 3 * p.1.1)) []) enc (encList (encPair encNat encBool)) :=
    listGetDWithInput hψ (unary_sub' hi h3N) []
  have hLitPair :
      ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) =>
          ((p.2.2 - 1) / 2, decide ((p.2.2 - 1) % 2 = 0))) enc (encPair encNat encBool) :=
    hjDiv2.prod (decide_eq' hjMod2 (const 0))
  have hClCond :
      ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × (ℕ × ℕ) =>
          decide (((p.2.2 - 1) / 2, decide ((p.2.2 - 1) % 2 = 0)) ∈
            p.1.2.getD (p.2.1 - (1 + 3 * p.1.1)) [])) enc encBool :=
    decide_mem hClause hLitPair
  have hbranchLit := ite' hjInLit (ite' hOppCond (const (0 : ℚ)) hN1rat) (const (-2 : ℚ))
  have hbranchVar := ite' hjInLit (ite' hVarCond (const (0 : ℚ)) hNrat) (const (-1 : ℚ))
  have hbranchCl := ite' hjInLit (ite' hClCond (const (0 : ℚ)) hNrat) (const (-1 : ℚ))
  have hall := ite' (decide_eq' hi (const 0)) (const (1 : ℚ))
    (ite' (unary_lt' hi h2N) hbranchLit (ite' (unary_lt' hi h3N) hbranchVar hbranchCl))
  exact hall.of_enc_eq fun p => congrArg encRat <| by
    dsimp only [gzEntry, Function.comp_apply]
    simp only [decide_eq_true_eq]

section PolyTimeCode

attribute [local irreducible] encRat encNat encUnary encCNF encBimatrix

private theorem computableInPolyTime_gzMatA {α : Type} {encIn : α ↪ List Bool}
    {N d : α → ℕ} {ψ : α → CNF ℕ}
    (hN : ComputableInPolyTime N encIn encUnary)
    (hψ : ComputableInPolyTime ψ encIn encCNF)
    (hd : ComputableInPolyTime d encIn encUnary) :
    ComputableInPolyTime (fun x => gzMatA (N x) (ψ x) (d x))
      encIn (encList (encList encRat)) := by
  unfold gzMatA
  refine mapWithInput (encA := encUnary) (range.comp hd) ?_
  refine mapWithInput (encA := encUnary) (range.comp (hd.comp (fst encIn encUnary))) ?_
  have hf := (fst encIn encUnary).comp (fst (encPair encIn encUnary) encUnary)
  exact computableInPolyTime_gzEntry.comp
    (((hN.comp hf).prod (hψ.comp hf)).prod
      (((snd encIn encUnary).comp (fst (encPair encIn encUnary) encUnary)).prod
        (snd (encPair encIn encUnary) encUnary)))

private theorem computableInPolyTime_gzMatB {α : Type} {encIn : α ↪ List Bool}
    {N d : α → ℕ} {ψ : α → CNF ℕ}
    (hN : ComputableInPolyTime N encIn encUnary)
    (hψ : ComputableInPolyTime ψ encIn encCNF)
    (hd : ComputableInPolyTime d encIn encUnary) :
    ComputableInPolyTime (fun x => gzMatB (N x) (ψ x) (d x))
      encIn (encList (encList encRat)) := by
  unfold gzMatB
  refine mapWithInput (encA := encUnary) (range.comp hd) ?_
  refine mapWithInput (encA := encUnary) (range.comp (hd.comp (fst encIn encUnary))) ?_
  have hf := (fst encIn encUnary).comp (fst (encPair encIn encUnary) encUnary)
  exact computableInPolyTime_gzEntry.comp
    (((hN.comp hf).prod (hψ.comp hf)).prod
      ((snd (encPair encIn encUnary) encUnary).prod
        ((snd encIn encUnary).comp (fst (encPair encIn encUnary) encUnary))))

private theorem computableInPolyTime_gilboaZemelCode :
    ComputableInPolyTime gilboaZemelCode encCNF encBimatrix := by
  have hN := computableInPolyTime_paddedNumVars
  have hψ := computableInPolyTime_paddedCNF
  have hM : ComputableInPolyTime (fun φ : CNF ℕ => (paddedCNF φ).length) encCNF encUnary :=
    SAT.computableInPolyTime_length hψ
  have hd : ComputableInPolyTime (fun φ : CNF ℕ => 1 + 3 * paddedNumVars φ + (paddedCNF φ).length)
      encCNF encUnary :=
    unary_add' (unary_add' (const 1) (unary_mul' (const 3) hN)) hM
  unfold gilboaZemelCode
  exact encBimatrix_mk_polyTime
    (computableInPolyTime_gzMatA hN hψ hd)
    (computableInPolyTime_gzMatB hN hψ hd)

end PolyTimeCode

/-! #### Polynomial-time reductions and NP-hardness headlines (Theorem 2.3, p. 33) -/

/-- Polynomial-time many-one reduction `SAT ≤ₚ SymGameHasTwoNash`. -/
theorem polyTimeReducible_SAT_SymGameHasTwoNash :
    PolyTimeReducible encCNF encBimatrix SAT SymGameHasTwoNash :=
  ⟨gilboaZemelCode, computableInPolyTime_gilboaZemelCode,
    gilboaZemelCode_mem_SymGameHasTwoNash_iff⟩

/-- **Deciding whether a symmetric rational two-player game has at least two distinct mixed Nash
equilibria is `NP`-hard** ([Papadimitriou2007], Theorem 2.3, bullet 1, p. 33; `NP` membership
remains open under #7789). -/
theorem SymGameHasTwoNash_npHard : NPHard encBimatrix SymGameHasTwoNash :=
  CookLevin.SAT_npHard.trans polyTimeReducible_SAT_SymGameHasTwoNash

/-- Polynomial-time many-one reduction `SAT ≤ₚ SymGameHasNashPayoffGe`. -/
theorem polyTimeReducible_SAT_SymGameHasNashPayoffGe :
    PolyTimeReducible encCNF encBimatrixThresholdInstance SAT SymGameHasNashPayoffGe :=
  ⟨fun φ => ⟨gilboaZemelCode φ, 2⟩,
    encBimatrixThresholdInstance_mk_polyTime computableInPolyTime_gilboaZemelCode (const (2 : ℚ)),
    gilboaZemelCode_mem_SymGameHasNashPayoffGe_iff⟩

/-- **Deciding whether a symmetric rational two-player game has a mixed Nash equilibrium with
player-1 payoff at least a given rational threshold is `NP`-hard** ([Papadimitriou2007],
Theorem 2.3, bullet 2, p. 33; `NP` membership remains open under #7789). -/
theorem SymGameHasNashPayoffGe_npHard :
    NPHard encBimatrixThresholdInstance SymGameHasNashPayoffGe :=
  CookLevin.SAT_npHard.trans polyTimeReducible_SAT_SymGameHasNashPayoffGe

/-- Polynomial-time many-one reduction `SAT ≤ₚ SymGameHasNashTotalPayoffGe`. -/
theorem polyTimeReducible_SAT_SymGameHasNashTotalPayoffGe :
    PolyTimeReducible encCNF encBimatrixThresholdInstance SAT SymGameHasNashTotalPayoffGe :=
  ⟨fun φ => ⟨gilboaZemelCode φ, 4⟩,
    encBimatrixThresholdInstance_mk_polyTime computableInPolyTime_gilboaZemelCode (const (4 : ℚ)),
    gilboaZemelCode_mem_SymGameHasNashTotalPayoffGe_iff⟩

/-- **Deciding whether a symmetric rational two-player game has a mixed Nash equilibrium with
total payoff at least a given rational threshold is `NP`-hard** ([Papadimitriou2007],
Theorem 2.3, bullet 3, p. 33; `NP` membership remains open under #7789). -/
theorem SymGameHasNashTotalPayoffGe_npHard :
    NPHard encBimatrixThresholdInstance SymGameHasNashTotalPayoffGe :=
  CookLevin.SAT_npHard.trans polyTimeReducible_SAT_SymGameHasNashTotalPayoffGe

/-- Polynomial-time many-one reduction `SAT ≤ₚ SymGameHasNashSupportGt`. -/
theorem polyTimeReducible_SAT_SymGameHasNashSupportGt :
    PolyTimeReducible encCNF encBimatrixSupportBoundInstance SAT SymGameHasNashSupportGt :=
  ⟨fun φ => ⟨gilboaZemelCode φ, 1⟩,
    encBimatrixSupportBoundInstance_mk_polyTime computableInPolyTime_gilboaZemelCode
      (const (1 : ℕ)),
    gilboaZemelCode_mem_SymGameHasNashSupportGt_iff⟩

/-- **Deciding whether a symmetric rational two-player game has a mixed Nash equilibrium with
support size strictly greater than a given number is `NP`-hard** ([Papadimitriou2007],
Theorem 2.3, bullet 4, p. 33; `NP` membership remains open under #7789). -/
theorem SymGameHasNashSupportGt_npHard :
    NPHard encBimatrixSupportBoundInstance SymGameHasNashSupportGt :=
  CookLevin.SAT_npHard.trans polyTimeReducible_SAT_SymGameHasNashSupportGt

/-- Polynomial-time many-one reduction `SAT ≤ₚ SymGameHasNashSupportContains`. -/
theorem polyTimeReducible_SAT_SymGameHasNashSupportContains :
    PolyTimeReducible encCNF encBimatrixStrategyIndexInstance SAT SymGameHasNashSupportContains :=
  ⟨fun φ => ⟨gilboaZemelCode φ, 1⟩,
    encBimatrixStrategyIndexInstance_mk_polyTime computableInPolyTime_gilboaZemelCode
      (const (1 : ℕ)),
    gilboaZemelCode_mem_SymGameHasNashSupportContains_iff⟩

/-- **Deciding whether a symmetric rational two-player game has a mixed Nash equilibrium whose
support contains a given pure strategy is `NP`-hard** ([Papadimitriou2007], Theorem 2.3,
bullet 5, p. 33; `NP` membership remains open under #7789). -/
theorem SymGameHasNashSupportContains_npHard :
    NPHard encBimatrixStrategyIndexInstance SymGameHasNashSupportContains :=
  CookLevin.SAT_npHard.trans polyTimeReducible_SAT_SymGameHasNashSupportContains

/-- Polynomial-time many-one reduction `SAT ≤ₚ SymGameHasNashSupportOmits`. -/
theorem polyTimeReducible_SAT_SymGameHasNashSupportOmits :
    PolyTimeReducible encCNF encBimatrixStrategyIndexInstance SAT SymGameHasNashSupportOmits :=
  ⟨fun φ => ⟨gilboaZemelCode φ, 0⟩,
    encBimatrixStrategyIndexInstance_mk_polyTime computableInPolyTime_gilboaZemelCode
      (const (0 : ℕ)),
    gilboaZemelCode_mem_SymGameHasNashSupportOmits_iff⟩

/-- **Deciding whether a symmetric rational two-player game has a mixed Nash equilibrium whose
support omits a given pure strategy is `NP`-hard** ([Papadimitriou2007], Theorem 2.3,
bullet 6, p. 33; `NP` membership remains open under #7789). -/
theorem SymGameHasNashSupportOmits_npHard :
    NPHard encBimatrixStrategyIndexInstance SymGameHasNashSupportOmits :=
  CookLevin.SAT_npHard.trans polyTimeReducible_SAT_SymGameHasNashSupportOmits

end BimatrixCode

end Cslib.GameTheory
