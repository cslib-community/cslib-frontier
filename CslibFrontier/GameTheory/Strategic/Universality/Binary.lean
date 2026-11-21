/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Universality.SimplexGame
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Binary games with prescribed indifference equations

In a game where every player `v` has two pure strategies, `false` and `true`, a mixed profile is a
vector `q : P → ℝ` of probabilities of `true`. By Lemma 4 of [Datta2003]
(`CostGame.deviationCost_realize`), for any multilinear polynomials `E v` in which `v` does not
occur, some binary game makes `E v (q)` the difference of player `v`'s expected costs. Its totally
mixed Nash equilibria are then exactly the points of the open cube `(0, 1)ᴾ` at which every `E v`
vanishes (`CostGame.isTotallyMixedNash_binaryGame_iff`). The game is the case of one
non-reference strategy per player of the reference-strategy bridge
`CostGame.referenceGame`, with `false` the reference strategy. This is the engine of the binary
construction in the proof of Datta's Theorem 6.

## Main definitions

* `Cslib.GameTheory.IsMultilinear f`: every monomial of `f` has degree at most one in each variable.
* `Cslib.GameTheory.binaryProfile q`: the mixed profile in which player `v` plays `true` with
  probability `q v`.
* `Cslib.GameTheory.CostGame.binaryGame E`: the binary game whose indifference equations are
  `E v = 0`.

## Main results

* `Cslib.GameTheory.CostGame.isTotallyMixedNash_binaryGame_iff`: the totally mixed equilibria of
  `binaryGame E` are the zeros of the `E v` in the open cube.
* `Cslib.GameTheory.CostGame.IsTotallyMixedNash.eq_binaryProfile`: every totally mixed profile of
  a binary game is `binaryProfile q` for `q v = p v true`.

## References

* [Datta2003]
-/

public section

namespace Cslib.GameTheory

open MvPolynomial Finset Function

variable {σ : Type*}

/-- A polynomial is **multilinear** if each of its monomials has degree at most one in every
variable. -/
@[expose] def IsMultilinear (f : MvPolynomial σ ℝ) : Prop :=
  ∀ m ∈ f.support, ∀ v, m v ≤ 1

namespace IsMultilinear

theorem zero : IsMultilinear (0 : MvPolynomial σ ℝ) := by
  simp [IsMultilinear]

theorem C (c : ℝ) : IsMultilinear (MvPolynomial.C c : MvPolynomial σ ℝ) := by
  classical
  intro m hm v
  rw [C_apply] at hm
  rw [Finset.mem_singleton.1 (support_monomial_subset hm)]
  simp

theorem X (v : σ) : IsMultilinear (MvPolynomial.X v : MvPolynomial σ ℝ) := by
  classical
  intro m hm w
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  rw [Finsupp.single_apply]
  split_ifs <;> omega

theorem add {f g : MvPolynomial σ ℝ} (hf : IsMultilinear f) (hg : IsMultilinear g) :
    IsMultilinear (f + g) := by
  classical
  intro m hm
  rcases Finset.mem_union.1 (support_add hm) with h | h
  exacts [hf m h, hg m h]

theorem neg {f : MvPolynomial σ ℝ} (hf : IsMultilinear f) : IsMultilinear (-f) := by
  intro m hm
  rw [mem_support_iff, coeff_neg, neg_ne_zero, ← mem_support_iff] at hm
  exact hf m hm

theorem sub {f g : MvPolynomial σ ℝ} (hf : IsMultilinear f) (hg : IsMultilinear g) :
    IsMultilinear (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem sum {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial σ ℝ}
    (h : ∀ i ∈ s, IsMultilinear (f i)) : IsMultilinear (∑ i ∈ s, f i) := by
  classical
  intro m hm
  obtain ⟨i, hi, hm⟩ := Finset.mem_biUnion.1 (support_sum hm)
  exact h i hi m hm

/-- A product of multilinear polynomials in disjoint sets of variables is multilinear. -/
theorem mul {f g : MvPolynomial σ ℝ} (hf : IsMultilinear f) (hg : IsMultilinear g)
    (hfg : Disjoint f.vars g.vars) : IsMultilinear (f * g) := by
  classical
  intro m hm v
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul f g hm)
  rw [Finsupp.add_apply]
  by_cases hav : a v = 0
  · rw [hav, zero_add]
    exact hg b hb v
  · have hvf : v ∈ f.vars := (mem_vars_iff_mem_support v).2 ⟨a, ha, Finsupp.mem_support_iff.2 hav⟩
    have hbv : b v = 0 := by
      by_contra hbv
      exact Finset.disjoint_left.1 hfg hvf
        ((mem_vars_iff_mem_support v).2 ⟨b, hb, Finsupp.mem_support_iff.2 hbv⟩)
    rw [hbv, add_zero]
    exact hf a ha v

/-- A product of multilinear polynomials in pairwise disjoint sets of variables is multilinear. -/
theorem prod {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial σ ℝ}
    (h : ∀ i ∈ s, IsMultilinear (f i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i).vars (f j).vars) :
    IsMultilinear (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using C (σ := σ) 1
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    refine (h i (mem_insert_self i s)).mul
      (ih (fun j hj => h j (mem_insert_of_mem hj)) fun j hj k hk => hd j (mem_insert_of_mem hj)
        k (mem_insert_of_mem hk)) ?_
    refine Finset.disjoint_left.2 fun v hvi hvs => ?_
    obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.1 (vars_prod _ hvs)
    exact Finset.disjoint_left.1 (hd i (mem_insert_self i s) j (mem_insert_of_mem hj)
      (fun hij => hi (hij ▸ hj))) hvi hvj

end IsMultilinear

variable {P : Type*}

/-- The binary mixed profile in which player `v` plays `true` with probability `q v`. -/
@[expose] def binaryProfile (q : P → ℝ) : P → Bool → ℝ :=
  fun v b => if b then q v else 1 - q v

/-- The embedding of the variables `P` as the `true` coordinates of the binary profile space. -/
@[expose] def trueCoord (v : P) : Σ _ : P, Bool := ⟨v, true⟩

private theorem trueCoord_injective : Injective (trueCoord (P := P)) := by
  intro v w h
  simpa [trueCoord] using congrArg Sigma.fst h

/-- The rename of a multilinear polynomial to the `true` coordinates is block-affine. -/
private theorem IsMultilinear.isBlockAffine_rename {f : MvPolynomial P ℝ} (hf : IsMultilinear f) :
    IsBlockAffine (rename trueCoord f) := by
  classical
  intro m hm v
  rw [support_rename_of_injective trueCoord_injective, Finset.mem_image] at hm
  obtain ⟨a, ha, rfl⟩ := hm
  rw [Fintype.sum_bool, show (⟨v, true⟩ : Σ _ : P, Bool) = trueCoord v from rfl,
    Finsupp.mapDomain_apply_of_injective trueCoord_injective a v, Finsupp.mapDomain_of_notMem_range]
  · simpa using hf a ha v
  · rintro ⟨w, hw⟩
    simp [trueCoord] at hw

namespace CostGame

variable [Fintype P] [DecidableEq P]

/-- The **binary game** with indifference equations `E v = 0`: player `v`'s cost for `true` is
`E v` at the vertex of the pure profile, and its cost for `false` is `0` (Lemma 4 of
[Datta2003], through `CostGame.referenceGame`). -/
noncomputable def binaryGame (E : P → MvPolynomial P ℝ) : CostGame P (fun _ => Bool) :=
  referenceGame trueCoord fun v b => if b then E v else 0

/-- Every totally mixed profile of a binary game is a `binaryProfile`. -/
theorem IsTotallyMixedNash.eq_binaryProfile {G : CostGame P (fun _ => Bool)}
    {p : P → Bool → ℝ} (h : G.IsTotallyMixedNash p) : p = binaryProfile (fun v => p v true) := by
  funext v b
  have hs := (G.isTotallyMixedNash_iff.1 h).2.1 v
  rw [Fintype.sum_bool] at hs
  cases b
  · simp [binaryProfile]
    linarith
  · simp [binaryProfile]

/-- **Binary games realize multilinear systems.** If each `E v` is multilinear and does not involve
`v`, the totally mixed Nash equilibria of `binaryGame E` are the profiles `binaryProfile q` with `q`
in the open cube `(0, 1)ᴾ` and `E v (q) = 0` for every `v`. -/
theorem isTotallyMixedNash_binaryGame_iff {E : P → MvPolynomial P ℝ}
    (hE : ∀ v, IsMultilinear (E v)) (hEv : ∀ v, v ∉ (E v).vars) (q : P → ℝ) :
    (binaryGame E).IsTotallyMixedNash (binaryProfile q) ↔
      (∀ v, 0 < q v ∧ q v < 1) ∧ ∀ v, eval q (E v) = 0 := by
  classical
  have hsum : ∀ v, ∑ b, binaryProfile q v b = 1 := fun v => by
    simp [binaryProfile]
  have hg : ∀ v (b : Bool), IsBlockAffine (rename trueCoord (if b then E v else 0)) := by
    intro v b
    cases b
    · simpa using IsMultilinear.zero.isBlockAffine_rename (P := P)
    · simpa using (hE v).isBlockAffine_rename
  have hgv : ∀ v (b : Bool), ∀ w ∈ (if b then E v else 0).vars, (trueCoord w).1 ≠ v := by
    intro v b w hw
    cases b
    · simp at hw
    · simp only [↓reduceIte] at hw
      rintro rfl
      exact hEv _ hw
  have heval : Sigma.uncurry (binaryProfile q) ∘ trueCoord = q := by
    funext v
    simp [binaryProfile, trueCoord, Sigma.uncurry]
  rw [binaryGame, isTotallyMixedNash_referenceGame_iff hg hgv (fun _ => false) (fun _ => rfl) hsum,
    heval]
  constructor
  · rintro ⟨hpos, hE0⟩
    refine ⟨fun v => ⟨by simpa [binaryProfile] using hpos v true, ?_⟩, fun v => by
      simpa using hE0 v true⟩
    have := hpos v false
    simp only [binaryProfile, Bool.false_eq_true, ite_false] at this
    linarith
  · rintro ⟨hq, hE0⟩
    refine ⟨fun v b => ?_, fun v b => ?_⟩
    · cases b <;> simp [binaryProfile] <;> linarith [hq v]
    · cases b <;> simp [hE0]

end CostGame

end Cslib.GameTheory
