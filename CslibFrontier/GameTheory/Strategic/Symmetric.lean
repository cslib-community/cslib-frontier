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

/-!
# Symmetric strategic games and Nash's symmetric equilibrium theorem

A strategic game `G : CostGame ι (fun _ => A)` in which all players share a common strategy set `A`
is **symmetric** (`CostGame.IsSymmetric`) if permuting the players permutes their costs:
`G.cost i (s ∘ π) = G.cost (π i) s` for every permutation `π : Equiv.Perm ι`, pure profile
`s : ι → A`, and player `i : ι`. A **symmetric mixed Nash equilibrium**
(`CostGame.IsSymmetricMixedNash`) is a mixed strategy `x : A → ℝ` such that the constant profile
`fun _ => x` is a mixed Nash equilibrium.

Every finite symmetric game with a nonempty strategy set has a symmetric mixed Nash equilibrium
([Papadimitriou2007], Example 2.2, pp. 30–31, and Section 2.3.1, p. 34). This specializes the
automorphism-invariance theorem of [Nash1951], Theorem 2, p. 289 (which establishes an equilibrium
invariant under the full automorphism group of any finite game) to interchangeable players sharing
a common nonempty action type `A`. Rather than building a separate fixed-point map, the proof
restricts `CostGame.nashMap` from `Strategic.Nash` to the diagonal `(x, …, x)` — applying Brouwer's
fixed-point theorem (`Cslib.Brouwer.exists_isFixedPt_pi_simplex`) on a single simplex `A → ℝ` — and
uses symmetry (`IsSymmetric.nashMap_const_eq`) together with `CostGame.isFixedPt_nashMap_iff`.

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
  `Cslib.GameTheory.CostGame.IsSymmetric.deviationCost_const_eq`,
  `Cslib.GameTheory.CostGame.IsSymmetric.nashMap_const_eq`: at a symmetric profile `fun _ => x`,
  all players have identical expected cost, deviation-cost vector, and Nash-map image.
* `Cslib.GameTheory.CostGame.IsSymmetric.isSymmetricMixedNash_iff_at`: checking optimality for a
  single representative player `i₀` suffices for `IsSymmetricMixedNash`.
* `Cslib.GameTheory.CostGame.IsSymmetric.exists_isSymmetricMixedNash`: symmetric mixed Nash
  equilibrium existence for player-symmetric games ([Papadimitriou2007], Example 2.2, pp. 30–31,
  and Section 2.3.1, p. 34; specialization of [Nash1951], Theorem 2, p. 289).

## References

* [C. H. Papadimitriou, *The Complexity of Finding Nash Equilibria*][Papadimitriou2007]
* [J. Nash, *Non-Cooperative Games*][Nash1951]
* [N. Nisan, T. Roughgarden, É. Tardos, and V. V. Vazirani (eds.),
  *Algorithmic Game Theory*][NisanRoughgardenTardosVazirani2007]
-/

public section

namespace Cslib.GameTheory.CostGame

open Finset Function

section Definitions

variable {ι A : Type*} (G : CostGame ι (fun _ => A))

/-- A game `G : CostGame ι (fun _ => A)` with common strategy set `A` is **symmetric**
([Papadimitriou2007], Example 2.2, pp. 30–31, and Section 2.3.1, p. 34; [Nash1951]) if permuting
the players' strategies by `π : Equiv.Perm ι` permutes their costs accordingly:
`G.cost i (s ∘ π) = G.cost (π i) s`. -/
@[expose] def IsSymmetric : Prop :=
  ∀ (π : Equiv.Perm ι) (s : ι → A) (i : ι), G.cost i (s ∘ π) = G.cost (π i) s

/-- `a : A` is a **symmetric pure Nash equilibrium** if the constant profile `fun _ => a` is a pure
Nash equilibrium. -/
@[expose] def IsSymmetricPureNash [DecidableEq ι] (a : A) : Prop :=
  G.IsPureNash fun _ => a

/-- `x : A → ℝ` is a **symmetric mixed Nash equilibrium** ([Papadimitriou2007], Example 2.2,
pp. 30–31, and Section 2.3.1, p. 34; [Nash1951]) if `x` is a mixed strategy and the constant
profile `fun _ => x` is a mixed Nash equilibrium. -/
@[expose] def IsSymmetricMixedNash [Fintype ι] [DecidableEq ι] [Fintype A] (x : A → ℝ) : Prop :=
  IsMixedStrategy x ∧ G.IsMixedNash fun _ => x

/-- When there is at least one player, `IsSymmetricMixedNash x` reduces to
`G.IsMixedNash (fun _ => x)`. -/
@[simp]
theorem isSymmetricMixedNash_iff_isMixedNash [Fintype ι] [DecidableEq ι] [Fintype A] [Nonempty ι]
    {G : CostGame ι (fun _ => A)} {x : A → ℝ} :
    G.IsSymmetricMixedNash x ↔ G.IsMixedNash fun _ => x :=
  ⟨fun h => h.2, fun h => ⟨h.1 (Classical.arbitrary ι), h⟩⟩

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
    update (s ∘ π) i a = (update s (π i) a) ∘ π := funext fun k => by
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk, π.injective.ne hk]

/-- Equivariance of `expectedCost` under player permutations in a symmetric game. -/
theorem IsSymmetric.expectedCost_comp_perm (hG : G.IsSymmetric) (π : Equiv.Perm ι)
    (p : ι → A → ℝ) (i : ι) :
    G.expectedCost (p ∘ π) i = G.expectedCost p (π i) := by
  rw [expectedCost_def, expectedCost_def, ← Equiv.sum_comp (permArrowEquiv π)]
  exact sum_congr rfl fun s _ => by
    dsimp only [permArrowEquiv, Equiv.coe_fn_mk]
    rw [productWeight_comp_perm, hG π s i]

/-- Equivariance of `deviationCost` under player permutations in a symmetric game. -/
theorem IsSymmetric.deviationCost_comp_perm (hG : G.IsSymmetric)
    (π : Equiv.Perm ι) (p : ι → A → ℝ) (i : ι) (a : A) :
    G.deviationCost (p ∘ π) i a = G.deviationCost p (π i) a := by
  rw [deviationCost_def, deviationCost_def, ← Equiv.sum_comp (permArrowEquiv π)]
  exact sum_congr rfl fun s _ => by
    dsimp only [permArrowEquiv, Equiv.coe_fn_mk]
    rw [productWeight_comp_perm, update_comp_perm, hG π (update s (π i) a) i]

/-- Permuting players in a mixed Nash equilibrium of a symmetric game yields another mixed Nash
equilibrium. -/
theorem IsSymmetric.isMixedNash_comp_perm (hG : G.IsSymmetric)
    {p : ι → A → ℝ} (hp : G.IsMixedNash p) (π : Equiv.Perm ι) :
    G.IsMixedNash (p ∘ π) :=
  ⟨fun i => hp.1 (π i), fun i a => by
    rw [hG.expectedCost_comp_perm, hG.deviationCost_comp_perm]
    exact hp.2 (π i) a⟩

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

/-- In a symmetric game, Nash's map assigns every player the same updated mixed strategy at a
constant profile `fun _ => x`. -/
theorem IsSymmetric.nashMap_const_eq (hG : G.IsSymmetric) (x : A → ℝ) (i j : ι) :
    G.nashMap (fun _ => x) i = G.nashMap (fun _ => x) j := funext fun a => by
  rw [nashMap_apply, nashMap_apply, hG.expectedCost_const_eq x i j]
  simp_rw [hG.deviationCost_const_eq x i j]

/-- In a symmetric game with a representative player `i₀`, `x` is a symmetric mixed Nash equilibrium
iff `x` is a mixed strategy and `i₀` has no profitable pure deviation from `fun _ => x`. -/
theorem IsSymmetric.isSymmetricMixedNash_iff_at (hG : G.IsSymmetric) (i₀ : ι)
    {x : A → ℝ} :
    G.IsSymmetricMixedNash x ↔
      IsMixedStrategy x ∧
        ∀ a : A, G.expectedCost (fun _ => x) i₀ ≤ G.deviationCost (fun _ => x) i₀ a :=
  ⟨fun h => ⟨h.1, h.2.2 i₀⟩, fun ⟨hx, hle⟩ => ⟨hx, fun _ => hx, fun i a => by
    rw [hG.expectedCost_const_eq x i i₀, hG.deviationCost_const_eq x i i₀ a]
    exact hle a⟩⟩

/-- A symmetric pure Nash equilibrium induces a point-mass symmetric mixed Nash equilibrium. -/
theorem IsSymmetricPureNash.isSymmetricMixedNash [DecidableEq A] {a : A}
    (h : G.IsSymmetricPureNash a) : G.IsSymmetricMixedNash (Pi.single a 1) :=
  ⟨isMixedStrategy_single a, CostGame.IsPureNash.isMixedNash h⟩

end Equivariance

/-! ### Nash's symmetric equilibrium theorem via `CostGame.nashMap` -/

section Existence

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] {G : CostGame ι (fun _ => A)}

/-- **Symmetric mixed Nash equilibrium existence** ([Papadimitriou2007], Example 2.2, pp. 30–31,
and Section 2.3.1, p. 34; specializes [Nash1951], Theorem 2, p. 289, which establishes invariance
under the full game automorphism group, to interchangeable players on a common nonempty action
type): every finite player-symmetric strategic game with a nonempty strategy set admits a symmetric
mixed Nash equilibrium. -/
theorem IsSymmetric.exists_isSymmetricMixedNash [Nonempty A] (hG : G.IsSymmetric) :
    ∃ x : A → ℝ, G.IsSymmetricMixedNash x := by
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    let f : (Unit → A → ℝ) → (Unit → A → ℝ) := fun q _ => G.nashMap (fun _ => q ()) i₀
    have hf_cont : Continuous f := continuous_pi fun _ => (continuous_apply i₀).comp
      (G.continuous_nashMap.comp (continuous_pi fun _ => continuous_apply ()))
    obtain ⟨q, hq, hfix⟩ := Cslib.Brouwer.exists_isFixedPt_pi_simplex
      (fun q hq _ => isMixedStrategy_iff.1
        (G.isMixedStrategy_nashMap (fun _ => isMixedStrategy_iff.2 (hq ())) i₀))
      hf_cont.continuousOn
    have hx : IsMixedStrategy (q ()) := isMixedStrategy_iff.2 (hq ())
    exact ⟨q (), hx, (G.isFixedPt_nashMap_iff (fun _ => hx)).1 <| funext fun i =>
      (hG.nashMap_const_eq (q ()) i i₀).trans (congrFun hfix ())⟩
  · classical
    rw [not_nonempty_iff] at hι
    exact ⟨Pi.single (Classical.arbitrary A) 1, isMixedStrategy_single _,
      isEmptyElim, isEmptyElim⟩

end Existence

end Cslib.GameTheory.CostGame
