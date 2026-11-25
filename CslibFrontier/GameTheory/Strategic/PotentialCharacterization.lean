/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Nash
public import CslibFrontier.GameTheory.Strategic.Potential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Characterizations of potential games

This module completes the structural characterizations of Section 2 of Monderer and Shapley
[MondererShapley1996] for strategic games in cost-minimization form (extending
`CslibFrontier.GameTheory.Strategic.Potential`):

1. **Weighted potentials and tie-free FIP** ([MondererShapley1996], equation (2.2), p. 127, and
   Corollary 2.6, p. 130): a `w`-potential with positive weights `w i > 0` induces an ordinal
   potential (hence the finite improvement property and pure Nash equilibrium existence on finite
   games), two `w`-potentials for nonzero weights differ by a constant, and a finite game with the
   FIP and no unilateral cost ties admits an ordinal potential.
2. **Coordination–dummy decomposition**: a strategic game admits an exact potential if and only if
   it decomposes additively into a coordination (common-cost) game and a dummy game in which no
   player's choice affects its own cost.
3. **Path-integral and four-cycle characterizations** ([MondererShapley1996], Theorem 2.8 and
   Corollary 2.9, pp. 130–131, and Appendix A, pp. 138–139): for a game with finitely many players,
   admitting an exact potential is equivalent to the vanishing of the unilateral deviation path
   integral `I(γ, G)` on all closed unilateral paths, on all simple closed unilateral paths, on all
   simple closed unilateral paths of length `4`, and to the explicit pairwise `2 × 2` rectangle
   curl-zero criterion (`CostGame.FourCycleZero`). Given a base profile `z`, `potentialOfBase`
   gives the explicit coordinate-sweep potential `H(y)` of [MondererShapley1996], Lemma 2.7, p. 130.
4. **Mixed-extension characterization** ([MondererShapley1996], Lemma 2.10, pp. 131–132): a finite
   game is a `w`-potential (or exact potential) game if and only if its mixed extension is, with
   multilinear potential `mixedPotential Φ p = ∑ s, productWeight p s * Φ s` (equation (2.4),
   p. 132).

## Main definitions

* `Cslib.GameTheory.CostGame.IsWeightedPotential`: `w`-potential function ([MondererShapley1996],
  equation (2.2), p. 127).
* `Cslib.GameTheory.CostGame.IsCoordination`, `Cslib.GameTheory.CostGame.IsDummy`: common-cost
  coordination games and unilateral-independent dummy games.
* `Cslib.GameTheory.CostGame.IsUnilateralStep`, `Cslib.GameTheory.CostGame.PathStep`,
  `Cslib.GameTheory.CostGame.UnilateralPath`: finite unilateral deviation paths in strategy space.
* `Cslib.GameTheory.CostGame.pathIntegral`: path sum `I(γ, G)` of unilateral cost changes along `γ`
  ([MondererShapley1996], p. 130).
* `Cslib.GameTheory.CostGame.FourCycleZero`: Monderer–Shapley pairwise `2 × 2` rectangle curl-zero
  condition ([MondererShapley1996], Corollary 2.9, p. 131).
* `Cslib.GameTheory.CostGame.potentialOfBase`: explicit coordinate-sweep potential anchored at a
  base profile `z` ([MondererShapley1996], p. 130).
* `Cslib.GameTheory.CostGame.mixedPotential`, `Cslib.GameTheory.CostGame.mixedExtension`:
  multilinear extension of a potential and the mixed-strategy cost game ([MondererShapley1996],
  equation (2.4), p. 132).

## Main results

* `Cslib.GameTheory.CostGame.exists_isOrdinalPotential_of_hasFIP`: **Corollary 2.6** of
  [MondererShapley1996] (p. 130).
* `Cslib.GameTheory.CostGame.exists_isExactPotential_iff_coordination_add_dummy`: exact potential
  games are precisely sums of coordination games and dummy games.
* `Cslib.GameTheory.CostGame.exists_isExactPotential_iff_closedPath`,
  `Cslib.GameTheory.CostGame.exists_isExactPotential_iff_simpleClosedPath`,
  `Cslib.GameTheory.CostGame.exists_isExactPotential_iff_simpleClosedPath_four`: **Theorem 2.8** of
  [MondererShapley1996] (p. 131).
* `Cslib.GameTheory.CostGame.exists_isExactPotential_iff_fourCycleZero`: **Corollary 2.9** of
  [MondererShapley1996] (p. 131).
* `Cslib.GameTheory.CostGame.exists_isWeightedPotential_mixedExtension_iff`,
  `Cslib.GameTheory.CostGame.exists_isExactPotential_mixedExtension_iff`: **Lemma 2.10** of
  [MondererShapley1996] (pp. 131–132).

## References

* [D. Monderer and L. S. Shapley, *Potential Games*][MondererShapley1996]
-/

public section

namespace Cslib.GameTheory.CostGame

open Finset Function

section WeightedAndDecomposition

variable {ι : Type*} {S : ι → Type*} [DecidableEq ι] (G : CostGame ι S)

/-- `Φ` is a **`w`-potential** (weighted potential) for `G` with player weights `w : ι → ℝ`
([MondererShapley1996], equation (2.2), p. 127, written for costs): every unilateral deviation by
player `i` changes player `i`'s cost by `w i` times the change in `Φ`. (Unlike equation (2.2),
positivity `0 < w i` is omitted from this predicate so that
`exists_isWeightedPotential_mixedExtension_iff` holds for arbitrary `w : ι → ℝ`, and is supplied as
an explicit hypothesis where needed.) -/
@[expose] def IsWeightedPotential (w : ι → ℝ) (Φ : (∀ i, S i) → ℝ) : Prop :=
  ∀ s i (a : S i), G.cost i (update s i a) - G.cost i s = w i * (Φ (update s i a) - Φ s)

/-- `G` is a **coordination (common-cost) game** if all players share the same cost function. -/
@[expose] def IsCoordination : Prop :=
  ∃ Φ : (∀ i, S i) → ℝ, ∀ i s, G.cost i s = Φ s

/-- `G` is a **dummy game** if no player's unilateral deviation changes its own cost. -/
@[expose] def IsDummy : Prop :=
  ∀ i s (a : S i), G.cost i (update s i a) = G.cost i s

variable {G}

@[simp]
theorem isWeightedPotential_one_iff {Φ : (∀ i, S i) → ℝ} :
    G.IsWeightedPotential (fun _ => 1) Φ ↔ G.IsExactPotential Φ := by
  simp only [IsWeightedPotential, IsExactPotential, one_mul]

/-- A `w`-potential with positive weights `0 < w i` is an ordinal potential
([MondererShapley1996], Section 2, pp. 127–128). -/
theorem IsWeightedPotential.isOrdinalPotential {w : ι → ℝ} {Φ : (∀ i, S i) → ℝ}
    (hw : ∀ i, 0 < w i) (h : G.IsWeightedPotential w Φ) : G.IsOrdinalPotential Φ :=
  fun s i a =>
    ⟨fun hlt => by_contra fun hge => by
        linarith [h s i a, mul_nonneg (hw i).le (sub_nonneg.2 (not_lt.1 hge))],
     fun hlt => by linarith [h s i a, mul_neg_of_pos_of_neg (hw i) (sub_neg.2 hlt)]⟩

/-- A finite game with a positive-weight `w`-potential has the finite improvement property. -/
theorem IsWeightedPotential.hasFIP [Finite (∀ i, S i)] {w : ι → ℝ} {Φ : (∀ i, S i) → ℝ}
    (hw : ∀ i, 0 < w i) (h : G.IsWeightedPotential w Φ) : G.HasFIP :=
  (h.isOrdinalPotential hw).isGeneralizedOrdinalPotential.hasFIP

/-- A finite nonempty game with a positive-weight `w`-potential has a pure Nash equilibrium. -/
theorem IsWeightedPotential.exists_isPureNash [Finite (∀ i, S i)] [Nonempty (∀ i, S i)]
    {w : ι → ℝ} {Φ : (∀ i, S i) → ℝ} (hw : ∀ i, 0 < w i) (h : G.IsWeightedPotential w Φ) :
    ∃ s, G.IsPureNash s :=
  (h.hasFIP hw).exists_isPureNash

/-- Rescaling each player's cost by `1 / w i` turns a `w`-potential with nonzero weights into an
exact potential. -/
theorem IsWeightedPotential.isExactPotential_div {w : ι → ℝ} {Φ : (∀ i, S i) → ℝ}
    (hw : ∀ i, w i ≠ 0) (h : G.IsWeightedPotential w Φ) :
    (⟨fun i s => G.cost i s / w i⟩ : CostGame ι S).IsExactPotential Φ := by
  intro s i a
  dsimp only
  rw [← sub_div, h s i a, mul_div_cancel_left₀ _ (hw i)]

/-- With finitely many players, two `w`-potentials for the same nonzero weights differ by an
additive constant (weighted extension of [MondererShapley1996], Lemma 2.7, p. 130). -/
theorem IsWeightedPotential.sub_eq_sub [Finite ι] {w : ι → ℝ} {Φ Ψ : (∀ i, S i) → ℝ}
    (hw : ∀ i, w i ≠ 0) (hΦ : G.IsWeightedPotential w Φ) (hΨ : G.IsWeightedPotential w Ψ)
    (s t : ∀ i, S i) : Φ s - Ψ s = Φ t - Ψ t :=
  (hΦ.isExactPotential_div hw).sub_eq_sub (hΨ.isExactPotential_div hw) s t

/-- When no player is indifferent between distinct unilateral actions, every generalized ordinal
potential is an ordinal potential ([MondererShapley1996], proof of Corollary 2.6, p. 130). -/
theorem IsGeneralizedOrdinalPotential.isOrdinalPotential_of_ne {Φ : (∀ i, S i) → ℝ}
    (hΦ : G.IsGeneralizedOrdinalPotential Φ)
    (hne : ∀ i s (a b : S i), a ≠ b → G.cost i (update s i a) ≠ G.cost i (update s i b)) :
    G.IsOrdinalPotential Φ := fun s i a =>
  ⟨hΦ s i a, fun hlt => by
    have ha : a ≠ s i := fun h => lt_irrefl _ (by rwa [h, update_eq_self] at hlt)
    refine (lt_or_gt_of_ne (by simpa only [update_eq_self] using hne i s a (s i) ha)).resolve_right
      fun hgt => lt_asymm hlt ?_
    simpa only [update_idem, update_eq_self] using
      hΦ (update s i a) i (s i) (by simpa only [update_idem, update_eq_self] using hgt)⟩

variable (G) in
/-- **[MondererShapley1996], Corollary 2.6 (p. 130)**: a finite game with the finite improvement
property in which distinct unilateral deviations never yield equal costs admits an ordinal
potential. -/
theorem exists_isOrdinalPotential_of_hasFIP [Finite (∀ i, S i)] (hFIP : G.HasFIP)
    (hne : ∀ i s (a b : S i), a ≠ b → G.cost i (update s i a) ≠ G.cost i (update s i b)) :
    ∃ Φ, G.IsOrdinalPotential Φ :=
  let ⟨Φ, hΦ⟩ := G.hasFIP_iff_exists_isGeneralizedOrdinalPotential.1 hFIP
  ⟨Φ, hΦ.isOrdinalPotential_of_ne hne⟩

variable (G) in
/-- **Coordination–dummy decomposition of exact potential games**: `G` admits an exact potential if
and only if `G` decomposes as the pointwise sum of a coordination game `C` and a dummy game `D`. -/
theorem exists_isExactPotential_iff_coordination_add_dummy :
    (∃ Φ, G.IsExactPotential Φ) ↔
      ∃ C D : CostGame ι S, C.IsCoordination ∧ D.IsDummy ∧
        ∀ i s, G.cost i s = C.cost i s + D.cost i s :=
  ⟨fun ⟨Φ, hΦ⟩ => ⟨⟨fun _ => Φ⟩, ⟨fun i s => G.cost i s - Φ s⟩, ⟨Φ, fun _ _ => rfl⟩,
    fun i s a => by dsimp only; linarith [hΦ s i a],
    fun _ _ => by dsimp only; ring⟩,
   fun ⟨_, _, ⟨Φ, hC⟩, hD, hsum⟩ => ⟨Φ, fun s i a => by
    rw [hsum i (update s i a), hsum i s, hC i (update s i a), hC i s, hD i s a]; ring⟩⟩

end WeightedAndDecomposition

/-! ### Unilateral deviation paths, Theorem 2.8, and Corollary 2.9 -/

section CycleCharacterization

variable {ι : Type*} {S : ι → Type*} [DecidableEq ι]

/-- `IsUnilateralStep i s t` holds when `t` is obtained from `s` by a nontrivial unilateral
deviation of player `i` (`t = update s i (t i)` and `s i ≠ t i`), so `i` is the unique deviating
player ([MondererShapley1996], Section 2, p. 128). -/
@[expose] def IsUnilateralStep (i : ι) (s t : ∀ k, S k) : Prop :=
  t = update s i (t i) ∧ s i ≠ t i

/-- The deviating player of a unilateral step is uniquely determined by its endpoints. -/
theorem IsUnilateralStep.eq_of_isUnilateralStep {i j : ι} {s t : ∀ k, S k}
    (hi : IsUnilateralStep i s t) (hj : IsUnilateralStep j s t) : i = j := by
  by_contra hij
  exact hi.2 (by rw [hj.1, update_of_ne hij])

/-- One transition `(player, profile)` along a finite unilateral deviation path. -/
structure PathStep (ι : Type*) (S : ι → Type*) where
  /-- The unique player deviating at this transition. -/
  player : ι
  /-- The strategy profile reached after the deviation. -/
  profile : ∀ i, S i

/-- Recursive step-chain validity predicate from an initial profile `s`. -/
@[expose] def IsStepChain : (∀ i, S i) → List (PathStep ι S) → Prop
  | _, [] => True
  | s, step :: rest => IsUnilateralStep step.player s step.profile ∧ IsStepChain step.profile rest

/-- Terminal profile reached from `s` after following a list of steps. -/
@[expose] def stepLast : (∀ i, S i) → List (PathStep ι S) → ∀ i, S i
  | s, [] => s
  | _, step :: rest => stepLast step.profile rest

/-- Initial vertices `[y₀, y₁, …, y_{N - 1}]` traversed before each step; for a closed path of
length `N ≥ 1`, distinctness of these `N` profiles defines a simple closed path
([MondererShapley1996], p. 131). -/
@[expose] def stepInitialVertices : (∀ i, S i) → List (PathStep ι S) → List (∀ i, S i)
  | _, [] => []
  | s, step :: rest => s :: stepInitialVertices step.profile rest

/-- A finite **unilateral deviation path** `γ = (y₀, y₁, …, y_N)` in strategy space
([MondererShapley1996], Section 2, pp. 128, 130–131). -/
structure UnilateralPath (ι : Type*) (S : ι → Type*) [DecidableEq ι] where
  /-- Initial strategy profile `y₀`. -/
  start : ∀ i, S i
  /-- Finite list of unilateral transitions `(i₁, y₁), …, (i_N, y_N)`. -/
  steps : List (PathStep ι S)
  /-- Every transition is a nontrivial unilateral deviation from the previous profile. -/
  valid : IsStepChain start steps

namespace UnilateralPath

/-- Number of transitions `N` in `γ` ([MondererShapley1996], p. 131). -/
@[expose] def length (γ : UnilateralPath ι S) : ℕ :=
  γ.steps.length

/-- Terminal strategy profile `y_N` of `γ`. -/
@[expose] def last (γ : UnilateralPath ι S) : ∀ i, S i :=
  stepLast γ.start γ.steps

/-- Initial vertex list `[y₀, y₁, …, y_{N - 1}]` of length `γ.length`. -/
@[expose] def initialVertices (γ : UnilateralPath ι S) : List (∀ i, S i) :=
  stepInitialVertices γ.start γ.steps

/-- `γ` is **closed** if its terminal profile equals its initial profile (`y_N = y₀`,
[MondererShapley1996], p. 131). -/
@[expose] def IsClosed (γ : UnilateralPath ι S) : Prop :=
  γ.last = γ.start

/-- `γ` is a **simple closed path** if it is closed and its `N` initial profiles
`y₀, …, y_{N - 1}` are pairwise distinct ([MondererShapley1996], p. 131). -/
@[expose] def IsSimpleClosed (γ : UnilateralPath ι S) : Prop :=
  γ.IsClosed ∧ γ.initialVertices.Nodup

theorem IsSimpleClosed.isClosed {γ : UnilateralPath ι S} (h : γ.IsSimpleClosed) : γ.IsClosed :=
  h.1

end UnilateralPath

/-- Recursive unilateral cost sum along a step list from `s`. -/
@[expose] def stepIntegral (G : CostGame ι S) : (∀ i, S i) → List (PathStep ι S) → ℝ
  | _, [] => 0
  | s, step :: rest =>
      (G.cost step.player step.profile - G.cost step.player s) + stepIntegral G step.profile rest

/-- **Path integral `I(γ, G)`** of unilateral cost changes along `γ` ([MondererShapley1996],
Section 2, p. 130, written for costs): `∑_{k = 1}^N (cost i_k y_k - cost i_k y_{k - 1})`. -/
@[expose] def pathIntegral (G : CostGame ι S) (γ : UnilateralPath ι S) : ℝ :=
  stepIntegral G γ.start γ.steps

/-- **Monderer–Shapley four-cycle curl-zero condition** ([MondererShapley1996], Corollary 2.9,
p. 131): for any two distinct players `i ≠ j`, fixed opponent profile `s`, and strategies
`xᵢ, yᵢ : S i`, `xⱼ, yⱼ : S j`, the sum of unilateral cost changes around the `2 × 2` rectangle
`A → B → C → D → A` vanishes. (Monderer and Shapley write `A = (xᵢ, xⱼ, a)` for `a ∈ Y^{-{i,j}}`,
implicitly taking `i ≠ j`.) -/
@[expose] def FourCycleZero (G : CostGame ι S) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → ∀ (s : ∀ k, S k) (xᵢ yᵢ : S i) (xⱼ yⱼ : S j),
    let A := update (update s i xᵢ) j xⱼ
    let B := update (update s i yᵢ) j xⱼ
    let C := update (update s i yᵢ) j yⱼ
    let D := update (update s i xᵢ) j yⱼ
    (G.cost i B - G.cost i A) + (G.cost j C - G.cost j B) +
      (G.cost i D - G.cost i C) + (G.cost j A - G.cost j D) = 0

private theorem stepIntegral_eq_potential_sub {G : CostGame ι S} {Φ : (∀ i, S i) → ℝ}
    (hΦ : G.IsExactPotential Φ) :
    ∀ (s : ∀ i, S i) (steps : List (PathStep ι S)),
      IsStepChain s steps → stepIntegral G s steps = Φ (stepLast s steps) - Φ s
  | s, [], _ => (sub_self (Φ s)).symm
  | s, ⟨i, t⟩ :: rest, ⟨ht, hrest⟩ => by
      have ht_eq : t = update s i (t i) := ht.1
      have hstep : G.cost i t - G.cost i s = Φ t - Φ s := by
        conv_lhs => rw [ht_eq]
        rw [hΦ s i (t i), ← ht_eq]
      simp only [stepIntegral, stepLast, hstep, stepIntegral_eq_potential_sub hΦ t rest hrest]
      ring

/-- Along any unilateral path `γ`, an exact potential `Φ` telescopes `G.pathIntegral γ` to
`Φ γ.last - Φ γ.start` ([MondererShapley1996], Appendix A, p. 138). -/
theorem IsExactPotential.pathIntegral_eq {G : CostGame ι S} {Φ : (∀ i, S i) → ℝ}
    (hΦ : G.IsExactPotential Φ) (γ : UnilateralPath ι S) :
    G.pathIntegral γ = Φ γ.last - Φ γ.start :=
  stepIntegral_eq_potential_sub hΦ γ.start γ.steps γ.valid

/-- In an exact potential game, `G.pathIntegral γ = 0` on every closed unilateral path `γ`. -/
theorem IsExactPotential.pathIntegral_eq_zero_of_isClosed {G : CostGame ι S} {Φ : (∀ i, S i) → ℝ}
    (hΦ : G.IsExactPotential Φ) {γ : UnilateralPath ι S} (hγ : γ.IsClosed) :
    G.pathIntegral γ = 0 := by
  rw [hΦ.pathIntegral_eq, hγ, sub_self]

/-- Vanishing on all simple closed unilateral paths of length `4` implies `FourCycleZero`. -/
private theorem fourCycleZero_of_simpleClosed_four {G : CostGame ι S}
    (h4 : ∀ γ : UnilateralPath ι S, γ.IsSimpleClosed → γ.length = 4 → G.pathIntegral γ = 0) :
    G.FourCycleZero := by
  intro i j hij s xᵢ yᵢ xⱼ yⱼ
  dsimp only
  set A := update (update s i xᵢ) j xⱼ
  set B := update (update s i yᵢ) j xⱼ
  set C := update (update s i yᵢ) j yⱼ
  set D := update (update s i xᵢ) j yⱼ
  by_cases hxi : xᵢ = yᵢ
  · subst hxi
    ring
  by_cases hxj : xⱼ = yⱼ
  · subst hxj
    ring
  have hne_of : ∀ (u v : ∀ k, S k) (k : ι), u k ≠ v k → u ≠ v :=
    fun _ _ k h e => h (congrFun e k)
  let γ : UnilateralPath ι S :=
    { start := A
      steps := [⟨i, B⟩, ⟨j, C⟩, ⟨i, D⟩, ⟨j, A⟩]
      valid :=
        ⟨⟨by simp [A, B, hij, update_comm hij.symm], by simp [A, B, hij, hxi]⟩,
         ⟨by simp [B, C], by simp [B, C, hxj]⟩,
         ⟨by simp [C, D, hij, update_comm hij.symm], by simp [C, D, hij, Ne.symm hxi]⟩,
         ⟨by simp [D, A], by simp [D, A, Ne.symm hxj]⟩, trivial⟩ }
  have hsimple : γ.IsSimpleClosed :=
    ⟨rfl, by simp [γ, UnilateralPath.initialVertices, stepInitialVertices,
      hne_of A B i (by simp [A, B, hij, hxi]), hne_of A C i (by simp [A, C, hij, hxi]),
      hne_of A D j (by simp [A, D, hxj]), hne_of B C j (by simp [B, C, hxj]),
      hne_of B D i (by simp [B, D, hij, Ne.symm hxi]),
      hne_of C D i (by simp [C, D, hij, Ne.symm hxi])]⟩
  have hzero := h4 γ hsimple rfl
  simp only [γ, pathIntegral, stepIntegral] at hzero
  linarith

/-- Intermediate profile obtained by replacing coordinates in `L` of `cur` with `target`. -/
private def sweepProfile : List ι → (∀ i, S i) → (∀ i, S i) → ∀ i, S i
  | [], cur, _ => cur
  | i :: L, cur, target => sweepProfile L (update cur i (target i)) target

/-- Unilateral cost sum accumulated when sweeping coordinates in `L` from `cur` to `target`. -/
private def sweepCost (G : CostGame ι S) : List ι → (∀ i, S i) → (∀ i, S i) → ℝ
  | [], _, _ => 0
  | i :: L, cur, target =>
      (G.cost i (update cur i (target i)) - G.cost i cur) +
        sweepCost G L (update cur i (target i)) target

private theorem sweepProfile_apply (L : List ι) (cur target : ∀ i, S i) (k : ι) :
    sweepProfile L cur target k = if k ∈ L then target k else cur k := by
  induction L generalizing cur with
  | nil => simp only [sweepProfile, List.not_mem_nil, ↓reduceIte]
  | cons i L ih =>
      rw [sweepProfile, ih]
      by_cases hki : k = i
      · subst hki
        simp
      · simp [hki]

private theorem sweepCost_append (G : CostGame ι S) (L₁ L₂ : List ι) (cur target : ∀ i, S i) :
    sweepCost G (L₁ ++ L₂) cur target =
      sweepCost G L₁ cur target + sweepCost G L₂ (sweepProfile L₁ cur target) target := by
  induction L₁ generalizing cur with
  | nil => simp only [List.nil_append, sweepCost, sweepProfile, zero_add]
  | cons i L₁ ih => simp only [List.cons_append, sweepCost, sweepProfile, ih]; ring

private theorem sweepCost_congr_of_notMem (G : CostGame ι S) {i : ι} :
    ∀ {L : List ι}, i ∉ L → ∀ (cur s : ∀ k, S k) (a : S i),
      sweepCost G L cur (update s i a) = sweepCost G L cur s
  | [], _, _, _, _ => rfl
  | j :: L, hi, cur, s, a => by
      simp only [sweepCost, update_of_ne (fun h => hi (List.mem_cons.2 (.inl h.symm))),
        sweepCost_congr_of_notMem G (fun h => hi (List.mem_cons.2 (.inr h)))]

private theorem sweepCost_swap_head {G : CostGame ι S} (h : G.FourCycleZero) {i j : ι}
    (hij : i ≠ j) (L : List ι) (cur target : ∀ k, S k) :
    sweepCost G (i :: j :: L) cur target = sweepCost G (j :: i :: L) cur target := by
  have hrect := h hij cur (cur i) (target i) (cur j) (target j)
  dsimp only at hrect
  have hB : update (update cur i (target i)) j (cur j) = update cur i (target i) := by
    ext k
    by_cases hk : k = j
    · subst hk
      simp [hij.symm]
    · simp [hk]
  simp only [update_eq_self, hB] at hrect
  simp only [sweepCost, update_comm hij.symm (target j) (target i) cur]
  linarith

private theorem sweepCost_perm {G : CostGame ι S} (h : G.FourCycleZero) :
    ∀ {L₁ L₂ : List ι}, L₁.Perm L₂ → L₁.Nodup → ∀ cur target,
      sweepCost G L₁ cur target = sweepCost G L₂ cur target
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons i hp, hnd, cur, target => by
      simp only [sweepCost]
      rw [sweepCost_perm h hp (List.nodup_cons.1 hnd).2]
  | _, _, .swap x y l, hnd, cur, target => by
      have hyx : y ≠ x := fun heq =>
        (List.nodup_cons.1 hnd).1 (by simp only [heq, List.mem_cons, true_or])
      exact sweepCost_swap_head h hyx l cur target
  | _, _, .trans hp₁ hp₂, hnd, cur, target =>
      (sweepCost_perm h hp₁ hnd cur target).trans
        (sweepCost_perm h hp₂ (hp₁.nodup_iff.1 hnd) cur target)

/-- Explicit **coordinate-sweep potential** `H(s)` anchored at a base profile `z`
([MondererShapley1996], proof of Lemma 2.7, p. 130): sums the unilateral cost changes as `z`'s
coordinates are replaced one player at a time by `s`'s. Under `FourCycleZero`, the sum is
independent of the player ordering and defines an exact potential. -/
noncomputable def potentialOfBase [Fintype ι] (G : CostGame ι S) (z s : ∀ i, S i) : ℝ :=
  sweepCost G (Finset.univ : Finset ι).toList z s

/-- Under `G.FourCycleZero`, `G.potentialOfBase z` is an exact potential of `G` with value `0` at
`z`. -/
theorem FourCycleZero.isExactPotential_potentialOfBase [Fintype ι] {G : CostGame ι S}
    (h : G.FourCycleZero) (z : ∀ i, S i) : G.IsExactPotential (G.potentialOfBase z) := by
  intro s i a
  let L_all := (Finset.univ : Finset ι).toList
  let L_rem := (Finset.univ.erase i).toList
  have hnd_all : L_all.Nodup := Finset.nodup_toList _
  have hi_notMem : i ∉ L_rem := by simp [L_rem]
  have hnd_split : (L_rem ++ [i]).Nodup := List.nodup_append.2
    ⟨Finset.nodup_toList _, List.nodup_singleton i, fun x hx y hy => by
      rintro rfl
      exact hi_notMem (List.mem_singleton.1 hy ▸ hx)⟩
  have hperm : L_all.Perm (L_rem ++ [i]) :=
    (List.perm_ext_iff_of_nodup hnd_all hnd_split).2 fun x => by
      simp only [L_all, L_rem, List.mem_append, Finset.mem_toList, Finset.mem_univ,
        Finset.mem_erase, List.mem_singleton, and_true]
      exact ⟨fun _ => (em (x = i)).symm, fun _ => trivial⟩
  have hw_rem : ∀ t : ∀ k, S k, sweepProfile L_rem z t = update t i (z i) := fun t => by
    funext k
    rw [sweepProfile_apply]
    by_cases hki : k = i
    · subst hki
      simp [L_rem]
    · simp [L_rem, hki]
  unfold potentialOfBase
  rw [sweepCost_perm h hperm hnd_all z (update s i a),
    sweepCost_perm h hperm hnd_all z s,
    sweepCost_append, sweepCost_append,
    sweepCost_congr_of_notMem G hi_notMem z s a, hw_rem s, hw_rem (update s i a), update_idem]
  simp only [sweepCost, update_idem, update_self, update_eq_self]
  ring

@[simp]
theorem potentialOfBase_self [Fintype ι] (G : CostGame ι S) (z : ∀ i, S i) :
    G.potentialOfBase z z = 0 := by
  unfold potentialOfBase
  suffices ∀ L : List ι, sweepCost G L z z = 0 from this _
  intro L
  induction L with
  | nil => rfl
  | cons i L ih => simp only [sweepCost, update_eq_self, sub_self, zero_add, ih]

/-- **[MondererShapley1996], Corollary 2.9 (p. 131)**: a strategic game with finitely many players
admits an exact potential if and only if its four-cycle curl `FourCycleZero` vanishes on every
two-player `2 × 2` strategy rectangle. -/
theorem exists_isExactPotential_iff_fourCycleZero [Finite ι] {G : CostGame ι S} :
    (∃ Φ, G.IsExactPotential Φ) ↔ G.FourCycleZero := by
  constructor
  · rintro ⟨Φ, hΦ⟩
    refine fourCycleZero_of_simpleClosed_four fun γ hγ _ =>
      hΦ.pathIntegral_eq_zero_of_isClosed hγ.isClosed
  · intro h
    by_cases hne : Nonempty (∀ i, S i)
    · obtain ⟨z⟩ := hne
      have : Fintype ι := Fintype.ofFinite ι
      exact ⟨G.potentialOfBase z, h.isExactPotential_potentialOfBase z⟩
    · have : IsEmpty (∀ i, S i) := not_nonempty_iff.1 hne
      exact ⟨fun s => isEmptyElim s, fun s => isEmptyElim s⟩

/-- **[MondererShapley1996], Theorem 2.8, `(1) ↔ (2)` (p. 131)**: a game with finitely many players
is an exact potential game if and only if `G.pathIntegral γ = 0` for every finite closed unilateral
path `γ`. -/
theorem exists_isExactPotential_iff_closedPath [Finite ι] {G : CostGame ι S} :
    (∃ Φ, G.IsExactPotential Φ) ↔
      ∀ γ : UnilateralPath ι S, γ.IsClosed → G.pathIntegral γ = 0 := by
  refine ⟨fun ⟨Φ, hΦ⟩ γ hγ => hΦ.pathIntegral_eq_zero_of_isClosed hγ, fun h => ?_⟩
  exact exists_isExactPotential_iff_fourCycleZero.2
    (fourCycleZero_of_simpleClosed_four fun γ hγ _ => h γ hγ.isClosed)

/-- **[MondererShapley1996], Theorem 2.8, `(1) ↔ (3)` (p. 131)**: a game with finitely many players
is an exact potential game if and only if `G.pathIntegral γ = 0` for every finite simple closed
unilateral path `γ`. -/
theorem exists_isExactPotential_iff_simpleClosedPath [Finite ι] {G : CostGame ι S} :
    (∃ Φ, G.IsExactPotential Φ) ↔
      ∀ γ : UnilateralPath ι S, γ.IsSimpleClosed → G.pathIntegral γ = 0 := by
  refine ⟨fun ⟨Φ, hΦ⟩ γ hγ => hΦ.pathIntegral_eq_zero_of_isClosed hγ.isClosed, fun h => ?_⟩
  exact exists_isExactPotential_iff_fourCycleZero.2
    (fourCycleZero_of_simpleClosed_four fun γ hγ _ => h γ hγ)

/-- **[MondererShapley1996], Theorem 2.8, `(1) ↔ (4)` (p. 131)**: a game with finitely many players
is an exact potential game if and only if `G.pathIntegral γ = 0` for every finite simple closed
unilateral path `γ` of length `4`. -/
theorem exists_isExactPotential_iff_simpleClosedPath_four [Finite ι] {G : CostGame ι S} :
    (∃ Φ, G.IsExactPotential Φ) ↔
      ∀ γ : UnilateralPath ι S, γ.IsSimpleClosed → γ.length = 4 → G.pathIntegral γ = 0 := by
  refine ⟨fun ⟨Φ, hΦ⟩ γ hγ _ => hΦ.pathIntegral_eq_zero_of_isClosed hγ.isClosed, fun h => ?_⟩
  exact exists_isExactPotential_iff_fourCycleZero.2 (fourCycleZero_of_simpleClosed_four h)

end CycleCharacterization

/-! ### Mixed extension of weighted and exact potential games (Lemma 2.10) -/

section MixedExtension

variable {ι : Type*} {S : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)]

/-- Multilinear **mixed potential** `Φ̄(p) = ∑ s, productWeight p s * Φ s` extending `Φ` to mixed
strategy profiles ([MondererShapley1996], equation (2.4), p. 132). -/
def mixedPotential (Φ : (∀ i, S i) → ℝ) (p : ∀ i, S i → ℝ) : ℝ :=
  ∑ s, productWeight p s * Φ s

theorem mixedPotential_def (Φ : (∀ i, S i) → ℝ) (p : ∀ i, S i → ℝ) :
    mixedPotential Φ p = ∑ s, productWeight p s * Φ s := by
  rw [mixedPotential]

/-- The **mixed extension** of a finite cost game `G`: player `i`'s strategy set is the simplex
`{ q : S i → ℝ // IsMixedStrategy q }` of mixed strategies, with expected cost `G.expectedCost`. -/
@[expose] def mixedExtension (G : CostGame ι S) :
    CostGame ι (fun i => { q : S i → ℝ // IsMixedStrategy q }) where
  cost i p := G.expectedCost (fun j => (p j).1) i

private theorem expectedCost_update_sub_eq (H : CostGame ι S) {p : ∀ i, S i → ℝ}
    (hp : ∀ j, ∑ a, p j a = 1) (i : ι) {q : S i → ℝ} (hq : ∑ a, q a = 1) :
    H.expectedCost (update p i q) i - H.expectedCost p i =
      ∑ a, q a * (H.deviationCost p i a - H.expectedCost p i) := by
  have hq_upd : ∑ a, update p i q i a = 1 := by rw [update_self]; exact hq
  have h_upd : H.expectedCost (update p i q) i = ∑ a, q a * H.deviationCost p i a := by
    rw [← H.sum_mul_deviationCost_eq_expectedCost (update p i q) hq_upd]
    refine sum_congr rfl fun a _ => ?_
    rw [update_self, H.deviationCost_update_self p (by rw [hq, hp i])]
  rw [h_upd]
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, hq, one_mul]

/-- If `Φ` is a `w`-potential for `G`, then unilateral mixed deviations change player `i`'s
expected cost by `w i` times the change in `mixedPotential Φ`. -/
theorem IsWeightedPotential.expectedCost_update_sub {G : CostGame ι S} {w : ι → ℝ}
    {Φ : (∀ i, S i) → ℝ} (hΦ : G.IsWeightedPotential w Φ) {p : ∀ i, S i → ℝ}
    (hp : ∀ j, ∑ a, p j a = 1) (i : ι) {q : S i → ℝ} (hq : ∑ a, q a = 1) :
    G.expectedCost (update p i q) i - G.expectedCost p i =
      w i * (mixedPotential Φ (update p i q) - mixedPotential Φ p) := by
  let C : CostGame ι S := ⟨fun _ s => Φ s⟩
  have hdev : ∀ a : S i, G.deviationCost p i a - G.expectedCost p i =
      w i * (C.deviationCost p i a - C.expectedCost p i) := by
    intro a
    rw [deviationCost_def, expectedCost_def, deviationCost_def, expectedCost_def,
      ← sum_sub_distrib, ← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun s _ => ?_
    simp only [C, ← mul_sub, hΦ s i a]
    ring
  have hC_eq : ∀ r : ∀ j, S j → ℝ, C.expectedCost r i = mixedPotential Φ r := fun r => by
    rw [expectedCost_def, mixedPotential_def]
  rw [← hC_eq (update p i q), ← hC_eq p, expectedCost_update_sub_eq G hp i hq,
    expectedCost_update_sub_eq C hp i hq, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [hdev a]
  ring

/-- If `Φ` is a `w`-potential for `G`, then `fun p => mixedPotential Φ (fun j => (p j).1)` is a
`w`-potential for `G.mixedExtension` ([MondererShapley1996], equation (2.4), p. 132). -/
theorem IsWeightedPotential.mixedExtension {G : CostGame ι S} {w : ι → ℝ} {Φ : (∀ i, S i) → ℝ}
    (hΦ : G.IsWeightedPotential w Φ) :
    G.mixedExtension.IsWeightedPotential w (fun p => mixedPotential Φ (fun j => (p j).1)) := by
  intro p i q
  have hmap : (fun j => (update p i q j).1) = update (fun j => (p j).1) i q.1 := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  simp only [CostGame.mixedExtension, hmap]
  exact hΦ.expectedCost_update_sub (fun j => (p j).2.sum_eq_one) i q.2.sum_eq_one

/-- **[MondererShapley1996], Lemma 2.10 (pp. 131–132)**: a finite game `G` is a `w`-potential game
if and only if its mixed extension `G.mixedExtension` is a `w`-potential game. -/
theorem exists_isWeightedPotential_mixedExtension_iff {G : CostGame ι S} {w : ι → ℝ} :
    (∃ Ψ, G.mixedExtension.IsWeightedPotential w Ψ) ↔ ∃ Φ, G.IsWeightedPotential w Φ := by
  classical
  refine ⟨fun ⟨Ψ, hΨ⟩ => ?_, fun ⟨Φ, hΦ⟩ => ⟨_, hΦ.mixedExtension⟩⟩
  let pureProf : (∀ j, S j) → ∀ j, { q : S j → ℝ // IsMixedStrategy q } :=
    fun s j => ⟨Pi.single (s j) 1, isMixedStrategy_single (s j)⟩
  refine ⟨fun s => Ψ (pureProf s), fun s i a => ?_⟩
  have hupd : pureProf (update s i a) =
      update (pureProf s) i ⟨Pi.single a 1, isMixedStrategy_single a⟩ := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [pureProf]
    · simp [pureProf, hj]
  have hstep := hΨ (pureProf s) i ⟨Pi.single a 1, isMixedStrategy_single a⟩
  rw [← hupd] at hstep
  simpa only [mixedExtension, pureProf, G.expectedCost_single] using hstep

/-- Exact-potential (`w = 1`) specialization of [MondererShapley1996], Lemma 2.10 (pp. 131–132): a
finite game admits an exact potential if and only if its mixed extension does. -/
theorem exists_isExactPotential_mixedExtension_iff {G : CostGame ι S} :
    (∃ Ψ, G.mixedExtension.IsExactPotential Ψ) ↔ ∃ Φ, G.IsExactPotential Φ := by
  simp only [← isWeightedPotential_one_iff, exists_isWeightedPotential_mixedExtension_iff]

end MixedExtension

end Cslib.GameTheory.CostGame
