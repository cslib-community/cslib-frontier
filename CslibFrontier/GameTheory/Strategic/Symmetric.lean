/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Nash
public import Mathlib.GroupTheory.Perm.Basic
import CslibFrontier.Foundations.Analysis.Brouwer.Simplex
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Symmetric strategic games and Nash's symmetric equilibrium theorem

A strategic game `G : CostGame ι (fun _ => A)` in which all players share a common strategy set `A`
is **symmetric** (`CostGame.IsSymmetric`) if permuting the players permutes their costs:
`G.cost i (s ∘ π) = G.cost (π i) s` for every permutation `π : Equiv.Perm ι`, pure profile
`s : ι → A`, and player `i : ι`. A **symmetric mixed Nash equilibrium**
(`CostGame.IsSymmetricMixedNash`) is a mixed strategy `x : A → ℝ` such that the constant profile
`fun _ => x` is a mixed Nash equilibrium.

Nash proved in his 1951 paper ([Nash1951]; cited in [Papadimitriou2007], Example 2.2, pp. 30–31,
and Section 2.3.1, p. 34) that every finite symmetric game with a nonempty strategy set has a
symmetric mixed Nash equilibrium. Unlike general Nash existence on the product of `|ι|` simplices,
the proof restricts Nash's continuous map to the diagonal `(x, …, x)` — equivalently, applies
Brouwer's fixed-point theorem (`Cslib.Brouwer.exists_isFixedPt_pi_simplex`) on a single simplex
`A → ℝ` — using symmetry to equate all players' expected and deviation costs at constant profiles.

## Main definitions

* `Cslib.GameTheory.CostGame.IsSymmetric`: permutation invariance of costs on a shared strategy
  type `A`.
* `Cslib.GameTheory.CostGame.IsSymmetricPureNash`: a pure strategy `a : A` such that `fun _ => a`
  is a pure Nash equilibrium.
* `Cslib.GameTheory.CostGame.IsSymmetricMixedNash`: a mixed strategy `x : A → ℝ` such that
  `fun _ => x` is a mixed Nash equilibrium.

## Main results

* `Cslib.GameTheory.CostGame.IsSymmetric.expectedCost_comp_perm`,
  `Cslib.GameTheory.CostGame.IsSymmetric.deviationCost_comp_perm`: equivariance of expected and
  deviation costs under player permutations.
* `Cslib.GameTheory.CostGame.IsSymmetric.expectedCost_const_eq`,
  `Cslib.GameTheory.CostGame.IsSymmetric.deviationCost_const_eq`: at a symmetric profile
  `fun _ => x`, all players have identical expected cost and deviation-cost vector.
* `Cslib.GameTheory.CostGame.IsSymmetric.isSymmetricMixedNash_iff_at`: checking optimality for a
  single representative player `i₀` suffices for `IsSymmetricMixedNash`.
* `Cslib.GameTheory.CostGame.IsSymmetric.exists_isSymmetricMixedNash`: **Nash's symmetric
  equilibrium theorem** ([Nash1951]; [Papadimitriou2007], Example 2.2, pp. 30–31, and
  Section 2.3.1, p. 34).

## References

* [J. Nash, *Non-Cooperative Games*][Nash1951]
* [N. Nisan, T. Roughgarden, É. Tardos, and V. V. Vazirani (eds.),
  *Algorithmic Game Theory*][NisanRoughgardenTardosVazirani2007]
* [C. H. Papadimitriou, *The Complexity of Finding Nash Equilibria*][Papadimitriou2007]
-/

public section

namespace Cslib.GameTheory.CostGame

open Finset Function

section Definitions

variable {ι A : Type*} (G : CostGame ι (fun _ => A))

/-- A game `G : CostGame ι (fun _ => A)` with common strategy set `A` is **symmetric**
([Nash1951]; [Papadimitriou2007], Example 2.2, pp. 30–31, and Section 2.3.1, p. 34) if permuting the
players' strategies by `π : Equiv.Perm ι` permutes their costs accordingly:
`G.cost i (s ∘ π) = G.cost (π i) s`. -/
@[expose] def IsSymmetric : Prop :=
  ∀ (π : Equiv.Perm ι) (s : ι → A) (i : ι), G.cost i (s ∘ π) = G.cost (π i) s

/-- `a : A` is a **symmetric pure Nash equilibrium** if the constant profile `fun _ => a` is a pure
Nash equilibrium. -/
@[expose] def IsSymmetricPureNash [DecidableEq ι] (a : A) : Prop :=
  G.IsPureNash fun _ => a

/-- `x : A → ℝ` is a **symmetric mixed Nash equilibrium** ([Nash1951];
[Papadimitriou2007], Example 2.2, pp. 30–31, and Section 2.3.1, p. 34) if the constant profile
`fun _ => x` is a mixed Nash equilibrium. -/
@[expose] def IsSymmetricMixedNash [Fintype ι] [DecidableEq ι] [Fintype A] (x : A → ℝ) : Prop :=
  G.IsMixedNash fun _ => x

end Definitions

section Equivariance

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] {G : CostGame ι (fun _ => A)}

private def permArrowEquiv (π : Equiv.Perm ι) : (ι → A) ≃ (ι → A) where
  toFun s := s ∘ π
  invFun s := s ∘ π.symm
  left_inv s := by
    funext k
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  right_inv s := by
    funext k
    simp only [Function.comp_apply, Equiv.symm_apply_apply]

omit [DecidableEq ι] [Fintype A] in
private theorem productWeight_comp_perm (π : Equiv.Perm ι) (p : ι → A → ℝ) (s : ι → A) :
    productWeight (p ∘ π) (s ∘ π) = productWeight p s := by
  rw [productWeight_def, productWeight_def]
  exact Equiv.prod_comp π fun k => p k (s k)

omit [Fintype ι] [Fintype A] in
private theorem update_comp_perm (π : Equiv.Perm ι) (s : ι → A) (i : ι) (a : A) :
    update (s ∘ π) i a = (update s (π i) a) ∘ π := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [Function.comp_apply, update_self]
  · have hπk : π k ≠ π i := π.injective.ne hk
    simp only [Function.comp_apply, update_of_ne hk, update_of_ne hπk]

/-- Equivariance of `expectedCost` under player permutations in a symmetric game. -/
theorem IsSymmetric.expectedCost_comp_perm (hG : G.IsSymmetric) (π : Equiv.Perm ι)
    (p : ι → A → ℝ) (i : ι) :
    G.expectedCost (p ∘ π) i = G.expectedCost p (π i) := by
  rw [expectedCost_def, expectedCost_def, ← Equiv.sum_comp (permArrowEquiv π)]
  refine sum_congr rfl fun s _ => ?_
  dsimp only [permArrowEquiv, Equiv.coe_fn_mk]
  rw [productWeight_comp_perm, hG π s i]

/-- Equivariance of `deviationCost` under player permutations in a symmetric game. -/
theorem IsSymmetric.deviationCost_comp_perm (hG : G.IsSymmetric)
    (π : Equiv.Perm ι) (p : ι → A → ℝ) (i : ι) (a : A) :
    G.deviationCost (p ∘ π) i a = G.deviationCost p (π i) a := by
  rw [deviationCost_def, deviationCost_def, ← Equiv.sum_comp (permArrowEquiv π)]
  refine sum_congr rfl fun s _ => ?_
  dsimp only [permArrowEquiv, Equiv.coe_fn_mk]
  rw [productWeight_comp_perm, update_comp_perm, hG π (update s (π i) a) i]

/-- Permuting players in a mixed Nash equilibrium of a symmetric game yields another mixed Nash
equilibrium. -/
theorem IsSymmetric.isMixedNash_comp_perm (hG : G.IsSymmetric)
    {p : ι → A → ℝ} (hp : G.IsMixedNash p) (π : Equiv.Perm ι) :
    G.IsMixedNash (p ∘ π) := by
  refine ⟨fun i => hp.1 (π i), fun i a => ?_⟩
  rw [hG.expectedCost_comp_perm, hG.deviationCost_comp_perm]
  exact hp.2 (π i) a

/-- At a symmetric mixed profile `fun _ => x`, every player has the same expected cost. -/
theorem IsSymmetric.expectedCost_const_eq (hG : G.IsSymmetric) (x : A → ℝ) (i j : ι) :
    G.expectedCost (fun _ => x) i = G.expectedCost (fun _ => x) j := by
  have h := hG.expectedCost_comp_perm (Equiv.swap i j) (fun _ => x) i
  rwa [Equiv.swap_apply_left] at h

/-- At a symmetric mixed profile `fun _ => x`, every player faces the same deviation-cost vector. -/
theorem IsSymmetric.deviationCost_const_eq (hG : G.IsSymmetric)
    (x : A → ℝ) (i j : ι) (a : A) :
    G.deviationCost (fun _ => x) i a = G.deviationCost (fun _ => x) j a := by
  have h := hG.deviationCost_comp_perm (Equiv.swap i j) (fun _ => x) i a
  rwa [Equiv.swap_apply_left] at h

/-- In a symmetric game with a representative player `i₀`, `x` is a symmetric mixed Nash equilibrium
iff `x` is a mixed strategy and `i₀` has no profitable pure deviation from `fun _ => x`. -/
theorem IsSymmetric.isSymmetricMixedNash_iff_at (hG : G.IsSymmetric) (i₀ : ι)
    {x : A → ℝ} :
    G.IsSymmetricMixedNash x ↔
      IsMixedStrategy x ∧
        ∀ a : A, G.expectedCost (fun _ => x) i₀ ≤ G.deviationCost (fun _ => x) i₀ a := by
  constructor
  · intro h
    exact ⟨h.1 i₀, fun a => h.2 i₀ a⟩
  · rintro ⟨hx, hle⟩
    refine ⟨fun _ => hx, fun i a => ?_⟩
    rw [hG.expectedCost_const_eq x i i₀, hG.deviationCost_const_eq x i i₀ a]
    exact hle a

/-- A symmetric pure Nash equilibrium induces a point-mass symmetric mixed Nash equilibrium. -/
theorem IsSymmetricPureNash.isSymmetricMixedNash [DecidableEq A] {a : A}
    (h : G.IsSymmetricPureNash a) : G.IsSymmetricMixedNash (Pi.single a 1) :=
  CostGame.IsPureNash.isMixedNash h

end Equivariance

/-! ### Nash's symmetric equilibrium theorem via single-simplex Brouwer -/

section Existence

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] {G : CostGame ι (fun _ => A)}

private def diagGain (G : CostGame ι (fun _ => A)) (i₀ : ι) (x : A → ℝ) (a : A) : ℝ :=
  max 0 (G.expectedCost (fun _ => x) i₀ - G.deviationCost (fun _ => x) i₀ a)

private noncomputable def diagStep (G : CostGame ι (fun _ => A)) (i₀ : ι)
    (q : Unit → A → ℝ) : Unit → A → ℝ :=
  fun _ a =>
    (q () a + diagGain G i₀ (q ()) a) / (1 + ∑ b : A, diagGain G i₀ (q ()) b)

omit [DecidableEq ι] [Fintype A] in
private theorem continuous_productWeight_diag (s : ι → A) :
    Continuous fun x : A → ℝ => productWeight (fun _ : ι => x) s := by
  simp only [productWeight_def]
  exact continuous_finsetProd _ fun i _ => continuous_apply (s i)

private theorem continuous_diagGain (G : CostGame ι (fun _ => A)) (i₀ : ι) (a : A) :
    Continuous fun x : A → ℝ => diagGain G i₀ x a := by
  have hexp : Continuous fun x : A → ℝ => G.expectedCost (fun _ => x) i₀ := by
    simp only [expectedCost_def]
    exact continuous_finsetSum _ fun s _ => (continuous_productWeight_diag s).mul continuous_const
  have hdev : Continuous fun x : A → ℝ => G.deviationCost (fun _ => x) i₀ a := by
    simp only [deviationCost_def]
    exact continuous_finsetSum _ fun s _ => (continuous_productWeight_diag s).mul continuous_const
  exact continuous_const.max (hexp.sub hdev)

private theorem diagDenom_pos (G : CostGame ι (fun _ => A)) (i₀ : ι) (x : A → ℝ) :
    0 < 1 + ∑ b : A, diagGain G i₀ x b := by
  have hnn : 0 ≤ ∑ b : A, diagGain G i₀ x b := sum_nonneg fun b _ => le_max_left 0 _
  linarith

private theorem continuous_diagStep (G : CostGame ι (fun _ => A)) (i₀ : ι) :
    Continuous (diagStep G i₀) := by
  refine continuous_pi fun _ => continuous_pi fun a => ?_
  dsimp only [diagStep]
  have hval : Continuous fun q : Unit → A → ℝ => q () := continuous_apply ()
  have hgain : ∀ b : A, Continuous fun q : Unit → A → ℝ => diagGain G i₀ (q ()) b :=
    fun b => (continuous_diagGain G i₀ b).comp hval
  exact (((continuous_apply a).comp hval).add (hgain a)).div₀
    (continuous_const.add (continuous_finsetSum _ fun b _ => hgain b))
    fun q => (diagDenom_pos G i₀ (q ())).ne'

private theorem mapsTo_diagStep (G : CostGame ι (fun _ => A)) (i₀ : ι) :
    Set.MapsTo (diagStep G i₀)
      {q : Unit → A → ℝ | ∀ u, (∀ a, 0 ≤ q u a) ∧ ∑ a, q u a = 1}
      {q : Unit → A → ℝ | ∀ u, (∀ a, 0 ≤ q u a) ∧ ∑ a, q u a = 1} := by
  intro q hq _
  obtain ⟨hnn, hsum⟩ := hq ()
  have hden := diagDenom_pos G i₀ (q ())
  refine ⟨fun a => div_nonneg (add_nonneg (hnn a) (le_max_left 0 _)) hden.le, ?_⟩
  dsimp only [diagStep]
  rw [← sum_div, sum_add_distrib, hsum, div_self hden.ne']

private theorem expectedCost_le_of_fixed_diagStep (G : CostGame ι (fun _ => A)) (i₀ : ι)
    {x : A → ℝ} (hx : IsMixedStrategy x)
    (hfix : Function.IsFixedPt (diagStep G i₀) (fun _ => x)) :
    ∀ a : A, G.expectedCost (fun _ => x) i₀ ≤ G.deviationCost (fun _ => x) i₀ a := by
  set S : ℝ := ∑ b : A, diagGain G i₀ x b
  have hrel : ∀ a : A, diagGain G i₀ x a = x a * S := fun a => by
    have ha : diagStep G i₀ (fun _ => x) () a = x a := congrFun (congrFun hfix ()) a
    dsimp only [diagStep] at ha
    rw [div_eq_iff (diagDenom_pos G i₀ x).ne'] at ha
    linarith
  have hS_nonpos : S ≤ 0 := by
    by_contra hS_pos
    push Not at hS_pos
    have hlt_on_supp : ∀ b : A, 0 < x b →
        G.deviationCost (fun _ => x) i₀ b < G.expectedCost (fun _ => x) i₀ := by
      intro b hb
      have hpos_gain : 0 < diagGain G i₀ x b := by
        rw [hrel b]
        exact mul_pos hb hS_pos
      dsimp only [diagGain] at hpos_gain
      by_contra hge
      push Not at hge
      rw [max_eq_left (sub_nonpos.2 hge)] at hpos_gain
      exact lt_irrefl 0 hpos_gain
    obtain ⟨a₀, ha₀⟩ := hx.exists_pos
    have hstrict : ∑ b : A, x b * G.deviationCost (fun _ => x) i₀ b <
        ∑ b : A, x b * G.expectedCost (fun _ => x) i₀ := by
      refine sum_lt_sum (fun b _ => ?_) ⟨a₀, mem_univ a₀,
        mul_lt_mul_of_pos_left (hlt_on_supp a₀ ha₀) ha₀⟩
      rcases (hx.nonneg b).eq_or_lt with h0 | hpos
      · rw [← h0, zero_mul, zero_mul]
      · exact (mul_lt_mul_of_pos_left (hlt_on_supp b hpos) hpos).le
    rw [G.sum_mul_deviationCost_eq_expectedCost (fun _ => x) hx.sum_eq_one, ← sum_mul,
      hx.sum_eq_one, one_mul] at hstrict
    exact lt_irrefl _ hstrict
  have hS_zero : S = 0 := le_antisymm hS_nonpos (sum_nonneg fun b _ => le_max_left 0 _)
  intro a
  have ha0 : diagGain G i₀ x a = 0 := by rw [hrel a, hS_zero, mul_zero]
  have hsub : G.expectedCost (fun _ => x) i₀ - G.deviationCost (fun _ => x) i₀ a ≤ 0 := by
    calc G.expectedCost (fun _ => x) i₀ - G.deviationCost (fun _ => x) i₀ a
        ≤ diagGain G i₀ x a := le_max_right 0 _
      _ = 0 := ha0
  linarith

/-- **Nash's symmetric equilibrium theorem** ([Nash1951]; [Papadimitriou2007],
Example 2.2, pp. 30–31, and Section 2.3.1, p. 34): every finite symmetric strategic game with a
nonempty strategy set admits a symmetric mixed Nash equilibrium. -/
theorem IsSymmetric.exists_isSymmetricMixedNash [Nonempty A] (hG : G.IsSymmetric) :
    ∃ x : A → ℝ, G.IsSymmetricMixedNash x := by
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    obtain ⟨q, hq, hfix⟩ := Cslib.Brouwer.exists_isFixedPt_pi_simplex
      (mapsTo_diagStep G i₀) (continuous_diagStep G i₀).continuousOn
    have hx : IsMixedStrategy (q ()) := isMixedStrategy_iff.2 (hq ())
    have hfix' : Function.IsFixedPt (diagStep G i₀) (fun _ => q ()) := by
      have hq_eq : (fun _ : Unit => q ()) = q := funext fun u => by cases u; rfl
      rwa [hq_eq]
    exact ⟨q (), (hG.isSymmetricMixedNash_iff_at i₀).2
      ⟨hx, expectedCost_le_of_fixed_diagStep G i₀ hx hfix'⟩⟩
  · classical
    rw [not_nonempty_iff] at hι
    let a₀ : A := Classical.arbitrary A
    exact ⟨Pi.single a₀ 1, ⟨fun i => isEmptyElim i, fun i => isEmptyElim i⟩⟩

end Existence

end Cslib.GameTheory.CostGame
