/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Universality.Realize
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Tactic.Linarith

/-!
# Games with a reference strategy per player

The bridge `CostGame.referenceGame emb E` gives each player `p` a reference strategy of cost `0`.
Every strategy `s` gets cost `E p s`, a polynomial in some coordinates `σ`, renamed into the
profile coordinates along `emb`. Through Lemma 4 of [Datta2003] (`CostGame.realize`), its totally
mixed Nash equilibria among the profiles with weights summing to `1` are the positive profiles at
which every `E p s` vanishes (`CostGame.isTotallyMixedNash_referenceGame_iff`). Both
`CostGame.simplexGame` below and the binary games `CostGame.binaryGame` are built on it.

In `simplexGame`, each player `p` has the reference strategy `none` and further pure strategies
`some t`, `t : T p`. A totally mixed profile is then determined by the weights `q ⟨p, t⟩` of the
non-reference strategies (`simplexProfile q`): the reference strategy gets `1 - ∑ t, q ⟨p, t⟩`.
The game `simplexGame E` gives the reference strategy cost `0` and the strategy `t` the cost
`E p t`. Its totally mixed Nash equilibria are the points of the product of open simplices at
which every `E p t` vanishes (`CostGame.isTotallyMixedNash_simplexGame_iff`). This is the setting
of the three-player construction in the proof of Theorem 5 of [Datta2003].

## Main definitions

* `Cslib.GameTheory.CostGame.referenceGame emb E`: the game with costs `E p s` renamed along
  `emb`.
* `Cslib.GameTheory.simplexProfile q`: the mixed profile with non-reference weights `q`.
* `Cslib.GameTheory.CostGame.simplexGame E`: the game whose indifference equations are
  `E p t = 0`.

## Main results

* `Cslib.GameTheory.CostGame.isTotallyMixedNash_referenceGame_iff`: the shared bridge from
  Lemma 4 to the reference-strategy games.
* `Cslib.GameTheory.CostGame.isTotallyMixedNash_simplexGame_iff`: the totally mixed equilibria of
  `simplexGame E` are the zeros of the `E p t` in the product of open simplices.
* `Cslib.GameTheory.CostGame.IsTotallyMixedNash.eq_simplexProfile`: every totally mixed profile of
  a game with strategy sets `Option (T p)` is a `simplexProfile`.

## References

* [Datta2003]
-/

public section

namespace Cslib.GameTheory

open MvPolynomial Finset Function

variable {P : Type*} {T : P → Type*}

namespace IsBlockAffine

variable [∀ p, Fintype (T p)]

theorem zero : IsBlockAffine (0 : MvPolynomial (Σ p, T p) ℝ) := by
  simp [IsBlockAffine]

theorem C (c : ℝ) : IsBlockAffine (MvPolynomial.C c : MvPolynomial (Σ p, T p) ℝ) := by
  classical
  intro m hm p
  rw [C_apply] at hm
  rw [Finset.mem_singleton.1 (support_monomial_subset hm)]
  simp

theorem X (v : Σ p, T p) : IsBlockAffine (MvPolynomial.X v : MvPolynomial (Σ p, T p) ℝ) := by
  classical
  intro m hm p
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  calc ∑ b, (Finsupp.single v 1 : (Σ p, T p) →₀ ℕ) ⟨p, b⟩
      ≤ ∑ b, if (⟨p, b⟩ : Σ p, T p) = v then 1 else 0 := by
        refine sum_le_sum fun b _ => ?_
        rw [Finsupp.single_apply]
        split_ifs <;> simp_all
    _ ≤ 1 := by
        rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_one]
        refine card_le_one.2 fun a ha b hb => ?_
        simp only [mem_filter] at ha hb
        have := ha.2.trans hb.2.symm
        simpa using this

theorem add {f g : MvPolynomial (Σ p, T p) ℝ} (hf : IsBlockAffine f) (hg : IsBlockAffine g) :
    IsBlockAffine (f + g) := by
  classical
  intro m hm
  rcases Finset.mem_union.1 (support_add hm) with h | h
  exacts [hf m h, hg m h]

theorem neg {f : MvPolynomial (Σ p, T p) ℝ} (hf : IsBlockAffine f) : IsBlockAffine (-f) := by
  intro m hm
  rw [mem_support_iff, coeff_neg, neg_ne_zero, ← mem_support_iff] at hm
  exact hf m hm

theorem sub {f g : MvPolynomial (Σ p, T p) ℝ} (hf : IsBlockAffine f) (hg : IsBlockAffine g) :
    IsBlockAffine (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem sum {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial (Σ p, T p) ℝ}
    (h : ∀ i ∈ s, IsBlockAffine (f i)) : IsBlockAffine (∑ i ∈ s, f i) := by
  classical
  intro m hm
  obtain ⟨i, hi, hm⟩ := Finset.mem_biUnion.1 (support_sum hm)
  exact h i hi m hm

/-- A product of block-affine polynomials whose variables lie in different blocks is
block-affine. -/
theorem mul {f g : MvPolynomial (Σ p, T p) ℝ} (hf : IsBlockAffine f) (hg : IsBlockAffine g)
    (hfg : ∀ v ∈ f.vars, ∀ w ∈ g.vars, v.1 ≠ w.1) : IsBlockAffine (f * g) := by
  classical
  intro m hm p
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul f g hm)
  simp only [Finsupp.add_apply, sum_add_distrib]
  by_cases hap : ∀ x : T p, a ⟨p, x⟩ = 0
  · simp only [hap, sum_const_zero, zero_add]
    exact hg b hb p
  · simp only [not_forall] at hap
    obtain ⟨x, hx⟩ := hap
    have hbp : ∀ y : T p, b ⟨p, y⟩ = 0 := by
      intro y
      by_contra hy
      exact hfg _ ((mem_vars_iff_mem_support _).2 ⟨a, ha, Finsupp.mem_support_iff.2 hx⟩) _
        ((mem_vars_iff_mem_support _).2 ⟨b, hb, Finsupp.mem_support_iff.2 hy⟩) rfl
    simp only [hbp, sum_const_zero, add_zero]
    exact hf a ha p

end IsBlockAffine

/-- The mixed profile in which player `p` plays the non-reference strategy `t` with probability
`q ⟨p, t⟩` and the reference strategy `none` with the remaining probability. -/
@[expose] def simplexProfile [∀ p, Fintype (T p)] (q : (Σ p, T p) → ℝ) :
    ∀ p, Option (T p) → ℝ
  | p, none => 1 - ∑ t, q ⟨p, t⟩
  | p, some t => q ⟨p, t⟩

/-- The embedding of the non-reference coordinates into the coordinates of `Option (T p)`. -/
@[expose] def someCoord (v : Σ p, T p) : Σ p, Option (T p) := ⟨v.1, some v.2⟩

private theorem someCoord_injective : Injective (someCoord (T := T)) := by
  rintro ⟨p, t⟩ ⟨p', t'⟩ h
  simp only [someCoord, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq, Option.some.injEq] at h
  rw [h]

/-- The rename of a block-affine polynomial to the non-reference coordinates is block-affine. -/
private theorem IsBlockAffine.rename_someCoord [∀ p, Fintype (T p)] {f : MvPolynomial (Σ p, T p) ℝ}
    (hf : IsBlockAffine f) : IsBlockAffine (rename someCoord f) := by
  classical
  intro m hm p
  rw [support_rename_of_injective someCoord_injective, Finset.mem_image] at hm
  obtain ⟨a, ha, rfl⟩ := hm
  rw [Fintype.sum_option, Finsupp.mapDomain_of_notMem_range]
  · simp only [zero_add]
    refine le_of_eq_of_le (sum_congr rfl fun t _ => ?_) (hf a ha p)
    exact Finsupp.mapDomain_apply_of_injective someCoord_injective a (⟨p, t⟩ : Σ p, T p)
  · rintro ⟨w, hw⟩
    simp only [someCoord, Sigma.mk.injEq] at hw
    obtain ⟨rfl, h⟩ := hw
    exact Option.some_ne_none _ (eq_of_heq h)

namespace CostGame

section Reference

variable {S : P → Type*} [Fintype P] [DecidableEq P] [∀ p, Fintype (S p)]
  [∀ p, DecidableEq (S p)] {σ : Type*}

/-- The game with costs `E p s` on the coordinates `σ`, renamed into the profile coordinates along
`emb`: player `p`'s cost for `s` is `E p s` at the vertex of the pure profile (Lemma 4 of
[Datta2003], `CostGame.realize`). With `E p (ref p) = 0`, the strategy `ref p` is a reference
strategy of cost `0`. -/
noncomputable def referenceGame (emb : σ → Σ p, S p) (E : ∀ p, S p → MvPolynomial σ ℝ) :
    CostGame P S :=
  realize fun p s => rename emb (E p s)

/-- **The reference-strategy bridge.** Suppose the renamed costs are block-affine, the cost of
player `p` involves no coordinate of `p`'s block, and each player has a reference strategy of cost
`0`. Then a profile whose weights sum to `1` for every player is a totally mixed Nash equilibrium of
`referenceGame emb E` iff it is positive and every `E p s` vanishes at it. -/
theorem isTotallyMixedNash_referenceGame_iff {emb : σ → Σ p, S p}
    {E : ∀ p, S p → MvPolynomial σ ℝ} (hE : ∀ p s, IsBlockAffine (rename emb (E p s)))
    (hEp : ∀ p s, ∀ v ∈ (E p s).vars, (emb v).1 ≠ p) (ref : ∀ p, S p)
    (href : ∀ p, E p (ref p) = 0) {x : ∀ p, S p → ℝ} (hx : ∀ p, ∑ s, x p s = 1) :
    (referenceGame emb E).IsTotallyMixedNash x ↔
      (∀ p s, 0 < x p s) ∧ ∀ p s, eval (Sigma.uncurry x ∘ emb) (E p s) = 0 := by
  classical
  have hgp : ∀ p s, ∀ w ∈ (rename emb (E p s)).vars, w.1 ≠ p := by
    intro p s w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 (vars_rename emb (E p s) hw)
    exact hEp p s u hu
  rw [referenceGame,
    isTotallyMixedNash_realize_iff hE hgp ref fun p => by rw [href, map_zero]]
  simp only [eval_rename]
  exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, hx, h3⟩⟩

end Reference

variable [Fintype P] [DecidableEq P] [∀ p, Fintype (T p)] [∀ p, DecidableEq (T p)]

/-- The game with indifference equations `E p t = 0`: player `p`'s cost for the non-reference
strategy `t` is `E p t` at the vertex of the pure profile, and its cost for the reference strategy
`none` is `0` (`CostGame.referenceGame`). -/
noncomputable def simplexGame (E : ∀ p, T p → MvPolynomial (Σ p, T p) ℝ) :
    CostGame P (fun p => Option (T p)) :=
  referenceGame someCoord fun p a => a.elim 0 (E p)

omit [∀ p, DecidableEq (T p)] in
/-- Every totally mixed profile of a game with strategy sets `Option (T p)` is a
`simplexProfile`. -/
theorem IsTotallyMixedNash.eq_simplexProfile {G : CostGame P (fun p => Option (T p))}
    {x : ∀ p, Option (T p) → ℝ} (h : G.IsTotallyMixedNash x) :
    x = simplexProfile (fun v => x v.1 (some v.2)) := by
  funext p a
  have hs := (G.isTotallyMixedNash_iff.1 h).2.1 p
  rw [Fintype.sum_option] at hs
  cases a
  · simp only [simplexProfile]
    linarith
  · rfl

/-- **Games with reference strategies realize block-affine systems.** If each `E p t` is
block-affine and does not involve player `p`'s block, the totally mixed Nash equilibria of
`simplexGame E` are the profiles `simplexProfile q` with every `q v` positive, every player's
non-reference weights summing to less than `1`, and `E p t (q) = 0` for all `p` and `t`. -/
theorem isTotallyMixedNash_simplexGame_iff {E : ∀ p, T p → MvPolynomial (Σ p, T p) ℝ}
    (hE : ∀ p t, IsBlockAffine (E p t)) (hEp : ∀ p t, ∀ v ∈ (E p t).vars, v.1 ≠ p)
    (q : (Σ p, T p) → ℝ) :
    (simplexGame E).IsTotallyMixedNash (simplexProfile q) ↔
      (∀ v, 0 < q v) ∧ (∀ p, ∑ t, q ⟨p, t⟩ < 1) ∧ ∀ p t, eval q (E p t) = 0 := by
  classical
  have hsum : ∀ p, ∑ a, simplexProfile q p a = 1 := fun p => by
    simp [Fintype.sum_option, simplexProfile]
  have hg : ∀ p (a : Option (T p)), IsBlockAffine (rename someCoord (a.elim 0 (E p))) := by
    rintro p (_ | t)
    · simpa using IsBlockAffine.zero
    · exact (hE p t).rename_someCoord
  have hgp : ∀ p (a : Option (T p)), ∀ v ∈ (a.elim 0 (E p)).vars, (someCoord v).1 ≠ p := by
    rintro p (_ | t) v hv
    · simp at hv
    · exact hEp p t v hv
  rw [simplexGame, isTotallyMixedNash_referenceGame_iff hg hgp (fun _ => none) (fun _ => rfl) hsum,
    show Sigma.uncurry (simplexProfile q) ∘ someCoord = q from rfl]
  constructor
  · rintro ⟨hpos, hE0⟩
    refine ⟨fun v => hpos v.1 (some v.2), fun p => ?_, fun p t => hE0 p (some t)⟩
    have := hpos p none
    simp only [simplexProfile] at this
    linarith
  · rintro ⟨hq, hlt, hE0⟩
    refine ⟨fun p a => ?_, fun p a => ?_⟩
    · cases a
      · simp only [simplexProfile]
        linarith [hlt p]
      · exact hq _
    · cases a
      · simp
      · exact hE0 p _

end CostGame

end Cslib.GameTheory
