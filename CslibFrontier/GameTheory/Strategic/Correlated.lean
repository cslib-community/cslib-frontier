/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Nash
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Geometry.Convex.Set
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Correlated equilibria

A *correlated equilibrium* of a cost-minimization game is a distribution `σ` on profiles under
which no player can lower its expected cost by applying a switching function `δ : S i → S i` to
its own strategy while the others keep theirs ([Roughgarden2013CS364A], Lecture 18, §1). A
trusted party samples `s ∼ σ` and privately recommends `s i` to each player `i`; the condition
says that following the recommendation is optimal given what the recommendation reveals about
the others'. Equivalently (`isCorrelatedEquilibrium_iff`), for every recommendation `a` and
deviation `b`, the expected cost of `i` on the event `s i = a` does not exceed its expected cost
there after switching to `b`. This is Definition 3.3 of [Roughgarden2013CS364A], Lecture 13, with
both sides multiplied by the probability of the event, so that the condition is meaningful when
that probability vanishes.

Distributions are finitely supported, as for coarse correlated equilibria, so expectations are
finite sums. The equilibrium concepts are nested ([Roughgarden2013CS364A], Lecture 13, §3):
a pure Nash equilibrium is a correlated equilibrium as a point mass, the product distribution of a
mixed Nash equilibrium is a correlated equilibrium, and a correlated equilibrium is a coarse
correlated equilibrium, because a constant switching function is a fixed deviation. By Nash's
theorem, every finite game has a correlated equilibrium. The set of correlated equilibria is
convex, both in `Convexity.StdSimplex ℝ (∀ i, S i)` (`isConvexSet_isCorrelatedEquilibrium`) and
as a polytope in `((∀ i, S i) → ℝ)` (`convex_correlatedEquilibriumPolytope`), so every convex
combination of mixed Nash product distributions is a correlated equilibrium
(`isCorrelatedEquilibrium_iConvexComb_mixedNash`; [TardosVazirani2007], Section 1.3.6, pp. 14–15;
[Papadimitriou2007], Section 2.7, pp. 45–47).

## Main definitions

* `Cslib.GameTheory.CostGame.IsCorrelatedEquilibrium`: correlated equilibria, by switching
  functions.

## Main results

* `Cslib.GameTheory.CostGame.isCorrelatedEquilibrium_iff`: the conditional form.
* `Cslib.GameTheory.CostGame.IsCorrelatedEquilibrium.isCoarseCorrelatedEquilibrium`: a correlated
  equilibrium is a coarse correlated equilibrium.
* `Cslib.GameTheory.CostGame.IsPureNash.isCorrelatedEquilibrium`: a pure Nash equilibrium is a
  correlated equilibrium as a point mass.
* `Cslib.GameTheory.CostGame.IsMixedNash.isCorrelatedEquilibrium`: the product distribution of a
  mixed Nash equilibrium is a correlated equilibrium.
* `Cslib.GameTheory.CostGame.exists_isCorrelatedEquilibrium`: every finite game has a correlated
  equilibrium.
* `Cslib.GameTheory.CostGame.IsCorrelatedEquilibrium.convexCombPair`,
  `Cslib.GameTheory.CostGame.IsPureNash.isCorrelatedEquilibrium_duple`,
  `Cslib.GameTheory.CostGame.isConvexSet_isCorrelatedEquilibrium`,
  `Cslib.GameTheory.CostGame.isCorrelatedEquilibrium_iConvexComb_mixedNash`,
  `Cslib.GameTheory.CostGame.convex_correlatedEquilibriumPolytope`: convexity of correlated
  equilibria (including two-point public-signal mixtures of pure Nash equilibria) and of the
  correlated-equilibrium polytope.

## References

* [C. H. Papadimitriou, *The Complexity of Finding Nash Equilibria*][Papadimitriou2007]
* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
* [É. Tardos and V. V. Vazirani, *Basic Solution Concepts and Computational
  Issues*][TardosVazirani2007]
-/

public section

namespace Cslib.GameTheory.CostGame

open Finset Function

variable {ι : Type*} {S : ι → Type*} [DecidableEq ι] (G : CostGame ι S)

/-- A finitely supported distribution `σ` on profiles is a **correlated equilibrium**
([Roughgarden2013CS364A], Lecture 18, §1): for every player `i` and switching function
`δ : S i → S i`, the expected cost of `i` under `σ` is at most its expected cost when it replaces
its recommended strategy `s i` by `δ (s i)` while the others play according to `σ`. -/
@[expose] def IsCorrelatedEquilibrium (σ : Convexity.StdSimplex ℝ (∀ i, S i)) : Prop :=
  ∀ i (δ : S i → S i), σ.weights.sum (fun s w => w * G.cost i s)
    ≤ σ.weights.sum (fun s w => w * G.cost i (update s i (δ (s i))))

/-- A finitely supported distribution `σ` on profiles is an **approximate correlated equilibrium**
([Roughgarden2013CS364A], Lecture 18, Proposition 1.3): for every player `i` and switching function
`δ : S i → S i`, the expected cost of `i` under `σ` exceeds its expected cost under the deviation
`δ` by at most the additive slack `ε i`. -/
@[expose] def IsApproxCorrelatedEquilibrium (ε : ι → ℝ)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) : Prop :=
  ∀ i (δ : S i → S i), σ.weights.sum (fun s w => w * G.cost i s)
    ≤ σ.weights.sum (fun s w => w * G.cost i (update s i (δ (s i)))) + ε i


omit [DecidableEq ι] in
/-- Grouping a sum over the support of `σ` by the recommendation `s i`. -/
private theorem sum_eq_sum_image_sum_ite (σ : Convexity.StdSimplex ℝ (∀ i, S i)) (i : ι)
    [DecidableEq (S i)] (f : (∀ j, S j) → S i → ℝ) :
    σ.weights.sum (fun s w => w * f s (s i)) = ∑ a ∈ σ.weights.support.image (fun s => s i),
      σ.weights.sum (fun s w => w * if s i = a then f s a else 0) := by
  simp only [Finsupp.sum]
  rw [sum_comm]
  refine sum_congr rfl fun s hs => ?_
  simp only [mul_ite, mul_zero]
  rw [sum_ite_eq (σ.weights.support.image fun s => s i) (s i) fun a => σ.weights s * f s a,
    ite_eq_left (mem_image_of_mem _ hs)]

omit [DecidableEq ι] in
private theorem sum_eq_sum_univ_sum_ite (σ : Convexity.StdSimplex ℝ (∀ i, S i)) (i : ι)
    [Fintype (S i)] [DecidableEq (S i)] (f : (∀ j, S j) → S i → ℝ) :
    σ.weights.sum (fun s w => w * f s (s i)) = ∑ a,
      σ.weights.sum (fun s w => w * if s i = a then f s a else 0) := by
  rw [sum_eq_sum_image_sum_ite σ i f]
  refine Finset.sum_subset (Finset.subset_univ _) fun a _ ha => Finset.sum_eq_zero fun s hs => ?_
  dsimp only
  rw [ite_eq_right fun h : s i = a => ha (h ▸ Finset.mem_image_of_mem _ hs), mul_zero]

variable {G}

/-- An approximate correlated equilibrium with zero slack is a correlated equilibrium. -/
theorem isApproxCorrelatedEquilibrium_zero_iff {σ : Convexity.StdSimplex ℝ (∀ i, S i)} :
    G.IsApproxCorrelatedEquilibrium 0 σ ↔ G.IsCorrelatedEquilibrium σ := by
  dsimp [IsApproxCorrelatedEquilibrium, IsCorrelatedEquilibrium]
  simp only [add_zero]


/-- The conditional form of approximate correlated equilibria. -/
theorem isApproxCorrelatedEquilibrium_iff [∀ i, DecidableEq (S i)] [∀ i, Fintype (S i)]
    {ε : ι → ℝ} {σ : Convexity.StdSimplex ℝ (∀ i, S i)} :
    G.IsApproxCorrelatedEquilibrium ε σ ↔ ∀ i (δ : S i → S i),
      (∑ a, σ.weights.sum (fun s w => w * if s i = a then G.cost i s else 0))
        ≤ (∑ a, σ.weights.sum (fun s w =>
            w * if s i = a then G.cost i (update s i (δ a)) else 0)) + ε i := by
  have H (i : ι) (δ : S i → S i) :=
    sum_eq_sum_univ_sum_ite σ i fun s a => G.cost i (update s i (δ a))
  have H0 (i : ι) := sum_eq_sum_univ_sum_ite σ i fun s _ => G.cost i s
  simp_rw [IsApproxCorrelatedEquilibrium, H0, H]


/-- The **conditional form** of correlated equilibria ([Roughgarden2013CS364A], Lecture 13,
Definition 3.3): for every player `i`, recommendation `a` and deviation `b`, the expected cost of
`i` on the event `s i = a` is at most its expected cost there when it plays `b` instead. Both sides
carry the probability of the event, so no division is needed. -/
theorem isCorrelatedEquilibrium_iff [∀ i, DecidableEq (S i)]
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)} :
    G.IsCorrelatedEquilibrium σ ↔ ∀ i (a b : S i),
      σ.weights.sum (fun s w => w * if s i = a then G.cost i s else 0)
        ≤ σ.weights.sum (fun s w => w * if s i = a then G.cost i (update s i b) else 0) := by
  refine ⟨fun h i a b => ?_, fun h i δ => ?_⟩
  · have key := h i fun c => if c = a then b else c
    have hL : σ.weights.sum (fun s w => w * G.cost i s) =
        σ.weights.sum (fun s w => w * if s i = a then G.cost i s else 0) +
          σ.weights.sum (fun s w => w * if s i = a then 0 else G.cost i s) := by
      rw [← Finsupp.sum_add]
      exact Finsupp.sum_congr fun _ _ => by split_ifs <;> ring
    have hR : σ.weights.sum (fun s w => w * G.cost i (update s i (if s i = a then b else s i))) =
        σ.weights.sum (fun s w => w * if s i = a then G.cost i (update s i b) else 0) +
          σ.weights.sum (fun s w => w * if s i = a then 0 else G.cost i s) := by
      rw [← Finsupp.sum_add]
      refine Finsupp.sum_congr fun s _ => ?_
      split_ifs
      · ring
      · rw [update_eq_self]; ring
    linarith
  · rw [sum_eq_sum_image_sum_ite σ i fun s _ => G.cost i s,
      sum_eq_sum_image_sum_ite σ i fun s c => G.cost i (update s i (δ c))]
    exact sum_le_sum fun a _ => h i a (δ a)

/-- A correlated equilibrium is a coarse correlated equilibrium: a fixed deviation `a` is the
constant switching function. -/
theorem IsCorrelatedEquilibrium.isCoarseCorrelatedEquilibrium
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)} (h : G.IsCorrelatedEquilibrium σ) :
    G.IsCoarseCorrelatedEquilibrium σ :=
  fun i a => h i fun _ => a

/-- A pure Nash equilibrium, viewed as a point mass, is a correlated equilibrium. -/
theorem IsPureNash.isCorrelatedEquilibrium {s : ∀ i, S i} (hs : G.IsPureNash s) :
    G.IsCorrelatedEquilibrium (Convexity.StdSimplex.single s) := by
  intro i δ
  simp only [Convexity.StdSimplex.weights_single, Finsupp.sum_single_index, zero_mul, one_mul]
  exact hs i (δ (s i))

section Mixed

variable [Fintype ι] [∀ i, Fintype (S i)]

/-- Under the product distribution of `p`, the expected cost of `i` after switching to `b`, on the
event that `i` is recommended `a`, is `p i a` times the expected cost of playing `b` against the
others' mixed strategies. -/
theorem sum_ite_productWeight [∀ i, DecidableEq (S i)] (G : CostGame ι S)
    (p : ∀ i, S i → ℝ) {i : ι} (hp : ∑ c, p i c = 1) (a b : S i) :
    ∑ s, productWeight p s * (if s i = a then G.cost i (update s i b) else 0)
      = p i a * G.deviationCost p i b := by
  have hsum : ∑ c, (Pi.single a 1 : S i → ℝ) c = ∑ c, p i c := by simp [hp]
  rw [← G.deviationCost_update_self p hsum b, deviationCost_def, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  have herase : ∏ j ∈ univ.erase i, update p i (Pi.single a 1) j (s j) =
      ∏ j ∈ univ.erase i, p j (s j) :=
    prod_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
  rw [productWeight_def, productWeight_def,
    ← mul_prod_erase univ (fun j => p j (s j)) (mem_univ i),
    ← mul_prod_erase univ (fun j => update p i (Pi.single a 1) j (s j)) (mem_univ i),
    herase, update_self]
  split_ifs with hs
  · subst hs
    rw [Pi.single_eq_same]; ring
  · rw [Pi.single_eq_of_ne hs]; ring

/-- The product distribution of a mixed Nash equilibrium is a correlated equilibrium: conditioned
on its own recommendation, a player still faces the others' independent mixed strategies. -/
theorem IsMixedNash.isCorrelatedEquilibrium {p : ∀ i, S i → ℝ} (h : G.IsMixedNash p) :
    G.IsCorrelatedEquilibrium
      (productDist (fun i => (h.1 i).nonneg) (fun i => (h.1 i).sum_eq_one)) := by
  classical
  refine isCorrelatedEquilibrium_iff.2 fun i a b => ?_
  have hp := (h.1 i).sum_eq_one
  have hL : ∑ s, productWeight p s * (if s i = a then G.cost i s else 0)
      = p i a * G.deviationCost p i a := by
    rw [← sum_ite_productWeight G p hp a a]
    refine sum_congr rfl fun s _ => ?_
    split_ifs with hs
    · rw [← hs, update_eq_self]
    · rfl
  rw [productDist_sum, productDist_sum, hL, sum_ite_productWeight G p hp a b]
  rcases ((h.1 i).nonneg a).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul, zero_mul]
  · rw [h.deviationCost_eq_of_pos i hpos]
    exact mul_le_mul_of_nonneg_left (h.2 i b) hpos.le

end Mixed

/-- Every finite game with nonempty strategy sets has a correlated equilibrium: the product
distribution of a mixed Nash equilibrium. -/
theorem exists_isCorrelatedEquilibrium [Finite ι] [∀ i, Finite (S i)] [∀ i, Nonempty (S i)]
    (G : CostGame ι S) : ∃ σ, G.IsCorrelatedEquilibrium σ := by
  have := Fintype.ofFinite ι
  have := fun i => Fintype.ofFinite (S i)
  obtain ⟨_, h⟩ := G.exists_isMixedNash
  exact ⟨_, h.isCorrelatedEquilibrium⟩

/-! ### Convexity of correlated equilibria -/

section ConvexCE

variable (G)

/-- Linearity of expectation against a binary convex combination of standard-simplex
distributions. -/
theorem sum_convexCombPair_weights {X : Type*} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (σ₁ σ₂ : Convexity.StdSimplex ℝ X) (f : X → ℝ) :
    (Convexity.convexCombPair a b ha hb hab σ₁ σ₂).weights.sum (fun s w => w * f s) =
      a * σ₁.weights.sum (fun s w => w * f s) + b * σ₂.weights.sum (fun s w => w * f s) := by
  rw [Convexity.StdSimplex.weights_convexCombPair,
    Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
    Finsupp.sum_smul_index' (fun _ => zero_mul _),
    Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum, Finsupp.mul_sum]
  congr 1 <;> exact Finsupp.sum_congr fun _ _ => by rw [smul_eq_mul, mul_assoc]

/-- Binary convex combinations preserve correlated equilibria ([Papadimitriou2007], Section 2.7,
p. 47). -/
theorem IsCorrelatedEquilibrium.convexCombPair {G : CostGame ι S}
    {σ₁ σ₂ : Convexity.StdSimplex ℝ (∀ i, S i)}
    (h₁ : G.IsCorrelatedEquilibrium σ₁) (h₂ : G.IsCorrelatedEquilibrium σ₂)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    G.IsCorrelatedEquilibrium (Convexity.convexCombPair a b ha hb hab σ₁ σ₂) := by
  intro i δ
  rw [sum_convexCombPair_weights, sum_convexCombPair_weights]
  linarith [mul_le_mul_of_nonneg_left (h₁ i δ) ha, mul_le_mul_of_nonneg_left (h₂ i δ) hb]

/-- A two-point convex combination (public-signal mixture) of two pure Nash equilibria is a
correlated equilibrium. -/
theorem IsPureNash.isCorrelatedEquilibrium_duple {G : CostGame ι S} {s₁ s₂ : ∀ i, S i}
    (h₁ : G.IsPureNash s₁) (h₂ : G.IsPureNash s₂)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    G.IsCorrelatedEquilibrium (Convexity.StdSimplex.duple s₁ s₂ ha hb hab) := by
  have heq : Convexity.StdSimplex.duple s₁ s₂ ha hb hab =
      Convexity.convexCombPair a b ha hb hab (.single s₁) (.single s₂) := by
    ext s
    simp [Convexity.StdSimplex.weights_duple, Convexity.StdSimplex.weights_convexCombPair]
  rw [heq]
  exact h₁.isCorrelatedEquilibrium.convexCombPair h₂.isCorrelatedEquilibrium ha hb hab

/-- **The set of correlated equilibria is convex** ([TardosVazirani2007], Section 1.3.6, pp. 14–15;
[Papadimitriou2007], Section 2.7, pp. 45–47): `{σ | G.IsCorrelatedEquilibrium σ}` is a convex set
in `Convexity.StdSimplex ℝ (∀ i, S i)`. -/
theorem isConvexSet_isCorrelatedEquilibrium :
    Convexity.IsConvexSet ℝ {σ : Convexity.StdSimplex ℝ (∀ i, S i) | G.IsCorrelatedEquilibrium σ} :=
  Convexity.IsConvexSet.of_convexCombPair_mem fun _ _ ha hb hab _ h₁ _ h₂ =>
    h₁.convexCombPair h₂ ha hb hab

/-- Every convex combination of the product distributions of mixed Nash equilibria is a correlated
equilibrium ([Papadimitriou2007], Section 2.7, pp. 46–47). -/
theorem isCorrelatedEquilibrium_iConvexComb_mixedNash [Fintype ι] [∀ i, Fintype (S i)]
    {J : Type*} {G : CostGame ι S} (w : Convexity.StdSimplex ℝ J)
    {p : J → ∀ i, S i → ℝ} (hp : ∀ j, G.IsMixedNash (p j)) :
    G.IsCorrelatedEquilibrium
      (w.iConvexComb fun j =>
        productDist (fun i => ((hp j).1 i).nonneg) (fun i => ((hp j).1 i).sum_eq_one)) :=
  G.isConvexSet_isCorrelatedEquilibrium.iConvexComb_mem fun j _ => (hp j).isCorrelatedEquilibrium

/-- On a finite game, the correlated-equilibrium polytope in `((∀ i, S i) → ℝ)` is convex in the
usual vector-space sense `Convex ℝ` ([Papadimitriou2007], Section 2.7, p. 47). -/
theorem convex_correlatedEquilibriumPolytope [Fintype ι] [∀ i, Fintype (S i)] :
    Convex ℝ {w : (∀ i, S i) → ℝ | IsMixedStrategy w ∧
      ∀ i (δ : S i → S i), ∑ s, w s * G.cost i s ≤ ∑ s, w s * G.cost i (update s i (δ (s i)))} := by
  rintro w₁ ⟨hw₁, hce₁⟩ w₂ ⟨hw₂, hce₂⟩ a b ha hb hab
  refine ⟨isMixedStrategy_iff.2 ⟨fun s => ?_, ?_⟩, fun i δ => ?_⟩
  · exact add_nonneg (mul_nonneg ha (hw₁.nonneg s)) (mul_nonneg hb (hw₂.nonneg s))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum,
      hw₁.sum_eq_one, hw₂.sum_eq_one, mul_one, hab]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc, sum_add_distrib,
      ← mul_sum]
    linarith [mul_le_mul_of_nonneg_left (hce₁ i δ) ha, mul_le_mul_of_nonneg_left (hce₂ i δ) hb]

end ConvexCE

end Cslib.GameTheory.CostGame
