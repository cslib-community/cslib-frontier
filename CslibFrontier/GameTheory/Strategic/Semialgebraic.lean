/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.AlgebraicGeometry.Semialgebraic
public import CslibFrontier.GameTheory.Strategic.Nash
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Nash equilibrium sets are semialgebraic

A mixed profile of a finite game `G : CostGame ι S` is a point `x : (Σ i, S i) → ℝ`, read as the
mixed strategies `Sigma.curry x`. Its expected costs are polynomials in the coordinates of `x`, so
the mixed Nash equilibria and the totally mixed Nash equilibria form semialgebraic sets
([Datta2003], §1).

## Main definitions

* `CostGame.expectedCostPoly G i`: the polynomial `∑ s, cost i s · ∏ⱼ x⟨j, s j⟩`.
* `CostGame.deviationCostPoly G i a`: the polynomial
  `∑_{s, s i = a} cost i s · ∏_{j ≠ i} x⟨j, s j⟩`, which does not involve player `i`'s
  coordinates (`CostGame.vars_deviationCostPoly`).

## Main results

* `CostGame.eval_expectedCostPoly`, `CostGame.eval_deviationCostPoly`: the polynomials evaluate to
  `expectedCost` and, on profiles where player `i`'s weights sum to `1`, to `deviationCost`.
* `CostGame.exists_finset_setOf_isMixedNash_eq`: the mixed Nash equilibria are a basic closed
  semialgebraic set, the common nonnegativity set of finitely many polynomials.
* `CostGame.setOf_isTotallyMixedNash_eq`: by equation (1) of [Datta2003]
  (`CostGame.isTotallyMixedNash_iff`), the totally mixed Nash equilibria are the positive profiles,
  with each player's weights summing to `1`, on which each player's `deviationCostPoly`s agree.
* `CostGame.isSemialgebraic_setOf_isMixedNash`,
  `CostGame.isSemialgebraic_setOf_isTotallyMixedNash`.

## References

* [Datta2003]
-/

public section

namespace Cslib.GameTheory.CostGame

open MvPolynomial Finset Function

variable {ι : Type*} {S : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)] (G : CostGame ι S)

/-- The monomial `∏ i, x⟨i, s i⟩`, whose value is the product weight of the pure profile `s`. -/
private noncomputable def weightPoly (s : ∀ i, S i) : MvPolynomial (Σ i, S i) ℝ :=
  ∏ i, X ⟨i, s i⟩

omit [DecidableEq ι] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
private theorem eval_weightPoly (x : (Σ i, S i) → ℝ) (s : ∀ i, S i) :
    eval x (weightPoly s) = productWeight (Sigma.curry x) s := by
  simp [weightPoly, productWeight_def, Sigma.curry]

/-- The expected cost of player `i` as a polynomial in the coordinates of the profile. -/
noncomputable def expectedCostPoly (i : ι) : MvPolynomial (Σ i, S i) ℝ :=
  ∑ s, C (G.cost i s) * weightPoly s

omit [∀ i, DecidableEq (S i)] in
theorem eval_expectedCostPoly (x : (Σ i, S i) → ℝ) (i : ι) :
    eval x (G.expectedCostPoly i) = G.expectedCost (Sigma.curry x) i := by
  simp [expectedCostPoly, eval_weightPoly, expectedCost_def, mul_comm]

/-- The expected cost of the pure strategy `a` of player `i`, as a polynomial in the coordinates of
the other players: `∑_{s, s i = a} cost i s · ∏_{j ≠ i} x⟨j, s j⟩`. -/
noncomputable def deviationCostPoly (i : ι) (a : S i) : MvPolynomial (Σ i, S i) ℝ :=
  ∑ s ∈ univ.filter (· i = a), C (G.cost i s) * ∏ j ∈ univ.erase i, X ⟨j, s j⟩

/-- On profiles where player `i`'s weights sum to `1`, `deviationCostPoly` evaluates to the
expected cost of the pure strategy `a`. -/
theorem eval_deviationCostPoly {x : (Σ i, S i) → ℝ} {i : ι} (hx : ∑ b, x ⟨i, b⟩ = 1) (a : S i) :
    eval x (G.deviationCostPoly i a) = G.deviationCost (Sigma.curry x) i a := by
  set p : ∀ i, S i → ℝ := Sigma.curry x
  have hq : ∑ b, (Pi.single a 1 : S i → ℝ) b = ∑ b, p i b := by
    simpa [p, Sigma.curry] using hx.symm
  rw [← G.deviationCost_update_self p hq a, deviationCost_def, deviationCostPoly, map_sum,
    sum_filter]
  refine sum_congr rfl fun s _ => ?_
  rw [productWeight_def, ← mul_prod_erase univ _ (mem_univ i)]
  simp only [update_self]
  by_cases hs : s i = a
  · subst hs
    have : ∏ j ∈ univ.erase i, update p i (Pi.single (s i) 1) j (s j) =
        ∏ j ∈ univ.erase i, x ⟨j, s j⟩ :=
      prod_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]; rfl
    simp [this, mul_comm]
  · simp [hs]

/-- `deviationCostPoly G i a` does not involve the coordinates of player `i`. -/
theorem vars_deviationCostPoly {i : ι} {a : S i} {v : Σ i, S i}
    (hv : v ∈ (G.deviationCostPoly i a).vars) : v.1 ≠ i := by
  classical
  unfold deviationCostPoly at hv
  obtain ⟨s, -, hs⟩ := Finset.mem_biUnion.1 (vars_sum_subset _ _ hv)
  have hs' := vars_mul _ _ hs
  rw [vars_C, Finset.empty_union] at hs'
  obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.1 (vars_prod _ hs')
  rw [vars_X, Finset.mem_singleton] at hvj
  subst hvj
  exact ne_of_mem_erase hj

omit [Fintype ι] [∀ i, DecidableEq (S i)] in
private theorem blockSum_sum_single (T : Finset ι) (s : ∀ i, S i) (j : ι) :
    ∑ b, (∑ i ∈ T, Finsupp.single (⟨i, s i⟩ : Σ i, S i) 1) ⟨j, b⟩ = if j ∈ T then 1 else 0 := by
  classical
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Sigma.mk.inj_iff]
  rw [Finset.sum_comm]
  have h : ∀ i ∈ T, ∑ b : S j, (if i = j ∧ s i ≍ b then 1 else 0 : ℕ) = if i = j then 1 else 0 := by
    intro i _
    split_ifs with hij
    · subst hij
      simp
    · simp [hij]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
private theorem support_C_mul_prod_X {T : Finset ι} {s : ∀ i, S i} {c : ℝ}
    {m : (Σ i, S i) →₀ ℕ} (hm : m ∈ (C c * ∏ i ∈ T, X (⟨i, s i⟩ : Σ i, S i)).support) :
    m = ∑ i ∈ T, Finsupp.single ⟨i, s i⟩ 1 := by
  classical
  have : C c * ∏ i ∈ T, X (⟨i, s i⟩ : Σ i, S i) =
      monomial (∑ i ∈ T, Finsupp.single (⟨i, s i⟩ : Σ i, S i) 1) c := by
    rw [monomial_sum_index]
    simp [X, C_mul']
  rw [this] at hm
  exact Finset.mem_singleton.1 (support_monomial_subset hm)

omit [∀ i, DecidableEq (S i)] in
/-- `expectedCostPoly G i` is **multilinear in the players' blocks**: each of its monomials has
degree exactly one in the coordinates `x⟨j, ·⟩` of every player `j`. -/
theorem blockDegree_of_mem_support_expectedCostPoly {i : ι} {m : (Σ i, S i) →₀ ℕ}
    (hm : m ∈ (G.expectedCostPoly i).support) (j : ι) : ∑ b, m ⟨j, b⟩ = 1 := by
  classical
  obtain ⟨s, -, hs⟩ := Finset.mem_biUnion.1 (support_sum hm)
  rw [support_C_mul_prod_X hs, blockSum_sum_single]
  simp

/-- Each monomial of `deviationCostPoly G i a` has degree exactly one in the coordinates of every
player `j ≠ i`, and degree zero in those of player `i`. -/
theorem blockDegree_of_mem_support_deviationCostPoly {i : ι} {a : S i} {m : (Σ i, S i) →₀ ℕ}
    (hm : m ∈ (G.deviationCostPoly i a).support) (j : ι) :
    ∑ b, m ⟨j, b⟩ = if j = i then 0 else 1 := by
  classical
  obtain ⟨s, -, hs⟩ := Finset.mem_biUnion.1 (support_sum hm)
  rw [support_C_mul_prod_X hs, blockSum_sum_single]
  by_cases hj : j = i <;> simp [hj]

/-- The total weight `∑ a, x⟨i, a⟩` of player `i`, as a polynomial. -/
private noncomputable def massPoly (i : ι) : MvPolynomial (Σ i, S i) ℝ :=
  ∑ a, X ⟨i, a⟩

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (S i)] in
private theorem eval_massPoly (x : (Σ i, S i) → ℝ) (i : ι) : eval x (massPoly (S := S) i) =
    ∑ a, x ⟨i, a⟩ := by
  simp [massPoly]

/-- The polynomials whose nonnegativity cuts out the mixed Nash equilibria: the coordinates, the
two inequalities `∑ a, x⟨i, a⟩ ≥ 1` and `≤ 1`, and `deviationCostPoly - expectedCostPoly`. -/
private noncomputable def nashPoly : (Σ i, S i) ⊕ ι ⊕ ι ⊕ (Σ i, S i) → MvPolynomial (Σ i, S i) ℝ
  | .inl v => X v
  | .inr (.inl i) => massPoly i - 1
  | .inr (.inr (.inl i)) => 1 - massPoly i
  | .inr (.inr (.inr v)) => G.deviationCostPoly v.1 v.2 - G.expectedCostPoly v.1

private theorem setOf_isMixedNash_eq_nashPoly :
    {x : (Σ i, S i) → ℝ | G.IsMixedNash (Sigma.curry x)} =
      {x | ∀ k, 0 ≤ eval x (G.nashPoly k)} := by
  ext x
  simp only [Set.mem_ofPred_eq, Sum.forall, nashPoly, eval_X, map_sub, map_one, eval_massPoly,
    sub_nonneg, eval_expectedCostPoly, Sigma.forall]
  constructor
  · rintro ⟨hmix, hnash⟩
    have hsum i : ∑ a, x ⟨i, a⟩ = 1 := (hmix i).sum_eq_one
    refine ⟨fun i a => (hmix i).nonneg a, fun i => (hsum i).ge, fun i => (hsum i).le,
      fun i a => ?_⟩
    rw [G.eval_deviationCostPoly (hsum i)]
    exact hnash i a
  · rintro ⟨hnn, hge, hle, hdev⟩
    have hsum i : ∑ a, x ⟨i, a⟩ = 1 := le_antisymm (hle i) (hge i)
    refine ⟨fun i => isMixedStrategy_iff.2 ⟨fun a => hnn i a, hsum i⟩, fun i a => ?_⟩
    rw [← G.eval_deviationCostPoly (hsum i)]
    exact hdev i a

omit [∀ i, DecidableEq (S i)] in
/-- The mixed Nash equilibria form a **basic closed semialgebraic set**: the common nonnegativity
set of finitely many polynomials. These are the coordinates `x⟨i, a⟩`, the polynomials
`∑ a, x⟨i, a⟩ - 1` and `1 - ∑ a, x⟨i, a⟩`, and `deviationCostPoly G i a - expectedCostPoly G i`. -/
theorem exists_finset_setOf_isMixedNash_eq :
    ∃ F : Finset (MvPolynomial (Σ i, S i) ℝ),
      {x : (Σ i, S i) → ℝ | G.IsMixedNash (Sigma.curry x)} = {x | ∀ f ∈ F, 0 ≤ eval x f} := by
  classical
  refine ⟨univ.image G.nashPoly, ?_⟩
  rw [setOf_isMixedNash_eq_nashPoly]
  ext x
  simp only [Set.mem_ofPred_eq, mem_image, mem_univ, true_and, forall_exists_index,
    forall_apply_eq_imp_iff]

omit [∀ i, DecidableEq (S i)] in
theorem isSemialgebraic_setOf_isMixedNash :
    IsSemialgebraic {x : (Σ i, S i) → ℝ | G.IsMixedNash (Sigma.curry x)} := by
  classical
  rw [setOf_isMixedNash_eq_nashPoly, Set.ofPred_forall]
  exact IsSemialgebraic.iInter fun k => IsSemialgebraic.setOf_nonneg _

/-- The totally mixed Nash equilibria are the positive profiles at which each player's weights sum
to `1` and each player's `deviationCostPoly`s agree. -/
theorem setOf_isTotallyMixedNash_eq :
    {x : (Σ i, S i) → ℝ | G.IsTotallyMixedNash (Sigma.curry x)} =
      (⋂ v, {x | 0 < x v}) ∩ (⋂ i, {x | ∑ a, x ⟨i, a⟩ = 1}) ∩
        ⋂ i, ⋂ a, ⋂ b, {x | MvPolynomial.eval x (G.deviationCostPoly i a) =
          MvPolynomial.eval x (G.deviationCostPoly i b)} := by
  ext x
  simp only [Set.mem_ofPred_eq, isTotallyMixedNash_iff, Set.mem_inter_iff, Set.mem_iInter,
    Sigma.forall]
  constructor
  · rintro ⟨hpos, hsum, heq⟩
    refine ⟨⟨fun i a => hpos i a, hsum⟩, fun i a b => ?_⟩
    rw [G.eval_deviationCostPoly (hsum i), G.eval_deviationCostPoly (hsum i)]
    exact heq i a b
  · rintro ⟨⟨hpos, hsum⟩, heq⟩
    refine ⟨hpos, hsum, fun i a b => ?_⟩
    rw [← G.eval_deviationCostPoly (hsum i), ← G.eval_deviationCostPoly (hsum i)]
    exact heq i a b

omit [∀ i, DecidableEq (S i)] in
theorem isSemialgebraic_setOf_isTotallyMixedNash :
    IsSemialgebraic {x : (Σ i, S i) → ℝ | G.IsTotallyMixedNash (Sigma.curry x)} := by
  classical
  rw [setOf_isTotallyMixedNash_eq]
  refine ((IsSemialgebraic.iInter fun v => ?_).inter (IsSemialgebraic.iInter fun i => ?_)).inter
    (IsSemialgebraic.iInter fun i => IsSemialgebraic.iInter fun a =>
      IsSemialgebraic.iInter fun b => IsSemialgebraic.setOf_eq _ _)
  · simpa using IsSemialgebraic.setOf_pos (X v)
  · simpa [eval_massPoly] using IsSemialgebraic.setOf_eq (massPoly (S := S) i) 1

end Cslib.GameTheory.CostGame
