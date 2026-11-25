/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.Multilinearity
public import CslibFrontier.Foundations.Data.Hamming.Expansion
import CslibFrontier.Foundations.Data.Fin.Counting
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Polynomial soundness of the multilinearity test

This module proves the soundness theorem of Babai, Fortnow and Lund for the multilinearity test,
both in the general `δ`-approximate form and at `δ = 0`:
if in every direction fewer than an `ε` fraction of the axis-parallel lines fail to be
`δ`-approximately affine, then `f` agrees with a multilinear function outside a
`3 n ^ 2 (ε + δ + 1 / |F|)` fraction of the points, when `|F| ≥ 40 n ^ 2`, `0 ≤ δ ≤ 1 / (400 n ^ 2)`
and `ε ≤ 1 / (800 n ^ 3)` (`Cslib.Code.exists_isMultilinear_hammingDist_lt_of_approx`)
[Babai, Fortnow, Lund, Theorem 5.13][BabaiFortnowLund1991].

A line is `δ`-approximately affine (`Cslib.Code.IsApproxAffine`) when some affine function agrees
with it outside at most `δ |F|` points. At `δ = 0` this coincides with
`Cslib.Code.IsAffineFun`, yielding `Cslib.Code.exists_isMultilinear_hammingDist_lt`
without the `δ` term. For `δ > 0`, BFL's Definition 3.4 / Definition 5.3 uses strict inequality
(`< δ |F|` disagreements), which implies `IsApproxAffine δ`, so their set of `δ`-wrong points
contains `Cslib.Code.wrongPointsApprox f δ i`. Via Markov's inequality on a line-vs-point oracle
(`Cslib.Code.exists_isMultilinear_hammingDist_lt_of_lineOracle`), this bounds the distance from
multilinear when an affine line oracle agrees with `f` with error `< ε * δ / n`.

*Note on citations*: the primary PDF for [BabaiFortnowLund1991] was not re-verified on disk here;
the section/definition/lemma/theorem numbers above follow `Cslib.Code.Multilinearity` (locator not
re-verified against primary PDF).

The proof follows theirs.

* **Self-improvement** (`Cslib.Code.IsMultilinear.hammingDist_le_of_two_mul_le_approx`,
  [Babai, Fortnow, Lund, Lemma 5.10][BabaiFortnowLund1991]): a multilinear function `g` that agrees
  with `f` on at least half of the points agrees with it outside at most
  `(2 n + 1) (∑ᵢ |Wᵢ| + n δ |F| ^ n) + 2 n ^ 2 |F| ^ (n - 1)` points, where `Wᵢ` is the set of
  points whose line in direction `i` is `δ`-wrong. Each non-`δ`-wrong line admits a witnessing
  affine fit differing on at most `δ |F|` corrupt points `Cᵢ`; removing `W ∪ C` from `B = {f ≠ g}`
  leaves `S`, whose line closure boundary lies in `W ∪ C ∪ I`, where `I` collects the unique
  agreement points on non-wrong lines. The Expansion Lemma
  (`Cslib.card_le_two_mul_card_lineClosure_sdiff`) bounds `S` by `2 n` times that boundary.
* **Induction on the dimension**, replacing their tree coloring
  [Babai, Fortnow, Lund, Lemma 5.12][BabaiFortnowLund1991]: using thresholds decaying by
  `1 - 1 / (2 n)` per dimension on `wrongPointsApprox` and an independent `1 / 40` Markov budget on
  `corruptPoints` in direction `0`, at least two slices are simultaneously good. Interpolating
  multilinear approximations of those two slices gives a multilinear function within half of the
  points, and self-improvement brings it within a fifth.

## Main definitions

* `Cslib.Code.IsApproxAffine`: `δ`-approximate affineness on a line (`≤ δ |F|` disagreements).
* `Cslib.Code.wrongPointsApprox`: points whose axis-parallel line is not `δ`-approximately affine.

## Main results

* `Cslib.Code.IsMultilinear.hammingDist_le_of_two_mul_le_approx`,
  `Cslib.Code.IsMultilinear.hammingDist_le_of_two_mul_le`: the self-improvement lemma.
* `Cslib.Code.exists_isMultilinear_hammingDist_lt_of_approx`,
  `Cslib.Code.exists_isMultilinear_hammingDist_lt`: polynomial soundness of the multilinearity test.
* `Cslib.Code.exists_isMultilinear_hammingDist_lt_of_lineOracle`: two-prover `Test0` soundness
  against an affine line oracle and point oracle.

## References

* [L. Babai, L. Fortnow, C. Lund, *Non-deterministic exponential time has two-prover interactive
  protocols*][BabaiFortnowLund1991], Section 5
-/

@[expose] public section

namespace Cslib.Code

open Finset Function
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- A function of one variable is *`δ`-approximately affine* when some affine function agrees with
it outside at most `δ * |F|` points. At `δ = 0` this coincides with `Cslib.Code.IsAffineFun`; for
`δ > 0`, any function satisfying the strict `< δ * |F|` condition of
[Babai, Fortnow, Lund, Definition 3.4][BabaiFortnowLund1991] satisfies `IsApproxAffine δ`. -/
def IsApproxAffine (δ : ℝ) (g : F → F) : Prop :=
  ∃ ℓ : F → F, IsAffineFun ℓ ∧ (#(univ.filter fun t => g t ≠ ℓ t) : ℝ) ≤ δ * Fintype.card F

/-- `0`-approximate affineness is exact affineness. -/
@[simp] theorem isApproxAffine_zero {g : F → F} : IsApproxAffine (0 : ℝ) g ↔ IsAffineFun g := by
  constructor
  · rintro ⟨ℓ, hℓ, hle⟩
    have h0 : #(univ.filter fun t => g t ≠ ℓ t) = 0 := by
      have : (#(univ.filter fun t => g t ≠ ℓ t) : ℝ) ≤ 0 := by simpa using hle
      exact_mod_cast le_antisymm this (by positivity)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
    have hge : g = ℓ := funext fun t => not_not.mp (h0 (mem_univ t))
    rwa [hge]
  · intro hg
    exact ⟨g, hg, by simp⟩

open Classical in
/-- The points whose axis-parallel line in direction `i` is not `δ`-approximately affine under
`f`. Each `δ`-wrong line contributes all of its `|F|` points
[Babai, Fortnow, Lund, Definition 5.3][BabaiFortnowLund1991]. -/
noncomputable def wrongPointsApprox (f : (Fin n → F) → F) (δ : ℝ) (i : Fin n) :
    Finset (Fin n → F) :=
  {x | ¬IsApproxAffine δ (lineRestrict f x i)}

/-- At `δ = 0`, `wrongPointsApprox f 0 i` coincides with `wrongPoints f i`. -/
@[simp] theorem wrongPointsApprox_zero (f : (Fin n → F) → F) (i : Fin n) :
    wrongPointsApprox f 0 i = wrongPoints f i := by
  ext x
  simp [wrongPointsApprox, wrongPoints]

omit [Field F] [Fintype F] [DecidableEq F] in
private theorem lineRestrict_update (f : (Fin n → F) → F) (x : Fin n → F) (i : Fin n) (t : F) :
    lineRestrict f (update x i t) i = lineRestrict f x i := by
  funext s
  simp [lineRestrict]

open Classical in
private theorem mem_wrongPointsApprox_update (f : (Fin n → F) → F) (δ : ℝ) (x : Fin n → F)
    (i : Fin n) (t : F) :
    update x i t ∈ wrongPointsApprox f δ i ↔ x ∈ wrongPointsApprox f δ i := by
  simp [wrongPointsApprox, lineRestrict_update]

open Classical in
/-- Canonical affine fit on a non-`δ`-wrong line in direction `i`, selected on `update x i 0` so
that all points of a line share the same affine function. -/
private noncomputable def lineApprox (f : (Fin n → F) → F) (δ : ℝ) (i : Fin n)
    (x : Fin n → F) : F → F :=
  if h : IsApproxAffine δ (lineRestrict f (update x i 0) i) then h.choose else fun _ => 0

open Classical in
private theorem lineApprox_update (f : (Fin n → F) → F) (δ : ℝ) (i : Fin n) (x : Fin n → F)
    (t : F) : lineApprox f δ i (update x i t) = lineApprox f δ i x := by
  simp [lineApprox]

open Classical in
private theorem isAffineFun_lineApprox {f : (Fin n → F) → F} {δ : ℝ} {i : Fin n} {x : Fin n → F}
    (hx : x ∉ wrongPointsApprox f δ i) : IsAffineFun (lineApprox f δ i x) := by
  simp only [wrongPointsApprox, mem_filter, mem_univ, true_and, not_not] at hx
  have hx' : IsApproxAffine δ (lineRestrict f (update x i 0) i) := by
    rwa [lineRestrict_update]
  simpa [lineApprox, hx'] using hx'.choose_spec.1

open Classical in
private theorem card_lineApprox_disagree_le {f : (Fin n → F) → F} {δ : ℝ} {i : Fin n}
    {x : Fin n → F} (hx : x ∉ wrongPointsApprox f δ i) :
    (#(univ.filter fun t => lineRestrict f x i t ≠ lineApprox f δ i x t) : ℝ) ≤
      δ * Fintype.card F := by
  simp only [wrongPointsApprox, mem_filter, mem_univ, true_and, not_not] at hx
  have hx' : IsApproxAffine δ (lineRestrict f (update x i 0) i) := by
    rwa [lineRestrict_update]
  have hline : lineApprox f δ i x = hx'.choose := by
    unfold lineApprox
    split_ifs
    rfl
  rw [hline, ← lineRestrict_update f x i 0]
  exact hx'.choose_spec.2

open Classical in
/-- Points lying on a non-`δ`-wrong line in direction `i` where `f` disagrees with the chosen
affine fit on that line. -/
private noncomputable def corruptPoints (f : (Fin n → F) → F) (δ : ℝ) (i : Fin n) :
    Finset (Fin n → F) :=
  {x | x ∉ wrongPointsApprox f δ i ∧ f x ≠ lineApprox f δ i x (x i)}

open Classical in
private theorem card_corruptPoints_le (f : (Fin n → F) → F) {δ : ℝ} (hδ : 0 ≤ δ) (i : Fin n) :
    (#(corruptPoints f δ i) : ℝ) ≤ δ * (Fintype.card F : ℝ) ^ n := by
  have hn : 0 < n := Fin.pos i
  let bases : Finset (Fin n → F) := {u | u i = 0}
  have hfib : #bases = Fintype.card F ^ (n - 1) := by
    have := Fintype.card_filter_piFinset_const_eq_of_mem (univ : Finset F) i (mem_univ 0)
    simpa [bases, Fintype.piFinset_univ] using this
  let target : Finset ((_: Fin n → F) × F) :=
    bases.sigma fun u =>
      if u ∈ wrongPointsApprox f δ i then ∅
      else univ.filter fun t => lineRestrict f u i t ≠ lineApprox f δ i u t
  have hinj : #(corruptPoints f δ i) ≤ #target := by
    refine card_le_card_of_injOn (fun x => ⟨update x i 0, x i⟩) ?_ ?_
    · intro x hx
      simp only [corruptPoints, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
      have hu : update x i 0 ∉ wrongPointsApprox f δ i := by
        simpa [mem_wrongPointsApprox_update] using hx.1
      simp only [target, mem_coe, mem_sigma, bases, mem_filter, mem_univ, true_and, update_self,
        hu, ↓reduceIte, true_and]
      simpa [lineRestrict, lineApprox_update] using hx.2
    · intro x _ x' _ hxx'
      have h1 : update x i 0 = update x' i 0 := congrArg Sigma.fst hxx'
      have h2 : x i = x' i := by
        have := congrArg (fun p : (_ : Fin n → F) × F => p.2) hxx'
        simpa using this
      calc x = update (update x i 0) i (x i) := by simp
        _ = update (update x' i 0) i (x' i) := by rw [h1, h2]
        _ = x' := by simp
  have hcardTarget : (#target : ℝ) ≤ (Fintype.card F : ℝ) ^ (n - 1) * (δ * Fintype.card F) := by
    simp only [target, card_sigma, Nat.cast_sum]
    calc (∑ u ∈ bases, (if u ∈ wrongPointsApprox f δ i then (∅ : Finset F)
            else univ.filter fun t => lineRestrict f u i t ≠ lineApprox f δ i u t).card : ℝ)
        ≤ ∑ _u ∈ bases, (δ * Fintype.card F) := by
          refine sum_le_sum fun u _ => ?_
          split_ifs with hu
          · simp only [card_empty, CharP.cast_eq_zero]
            positivity
          · exact card_lineApprox_disagree_le hu
      _ = #bases * (δ * Fintype.card F) := by rw [sum_const, nsmul_eq_mul]
      _ = (Fintype.card F : ℝ) ^ (n - 1) * (δ * Fintype.card F) := by rw [hfib]; push_cast; rfl
  have hq : (Fintype.card F : ℝ) ^ (n - 1) * (Fintype.card F : ℝ) = (Fintype.card F : ℝ) ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  calc (#(corruptPoints f δ i) : ℝ) ≤ (#target : ℝ) := by exact_mod_cast hinj
    _ ≤ (Fintype.card F : ℝ) ^ (n - 1) * (δ * Fintype.card F) := hcardTarget
    _ = δ * (Fintype.card F : ℝ) ^ n := by rw [mul_left_comm, hq]

open Classical in
/-- Points where the canonical affine fit on the line in direction `i` and `lineRestrict g` are
distinct affine functions that agree, and `g` equals that fit: at most one on each line. -/
private noncomputable def agreePointsApprox (f g : (Fin n → F) → F) (δ : ℝ) (i : Fin n) :
    Finset (Fin n → F) :=
  {x | x ∉ wrongPointsApprox f δ i ∧ lineApprox f δ i x ≠ lineRestrict g x i ∧
    lineApprox f δ i x (x i) = g x}

open Classical in
/-- Each line in direction `i` has at most one point where the canonical affine fit and a distinct
affine restriction of `g` agree, so there are at most `|F| ^ (n - 1)` such points. -/
private theorem card_agreePointsApprox_le {f g : (Fin n → F) → F} (hg : IsMultilinear g)
    (δ : ℝ) (i : Fin n) :
    #(agreePointsApprox f g δ i) ≤ Fintype.card F ^ (n - 1) := by
  have hfib : #{y : Fin n → F | y i = 0} = Fintype.card F ^ (n - 1) := by
    have := Fintype.card_filter_piFinset_const_eq_of_mem (univ : Finset F) i (mem_univ 0)
    simpa [Fintype.piFinset_univ] using this
  rw [← hfib]
  refine card_le_card_of_injOn (fun x => update x i 0) (fun x _ => by simp) ?_
  intro x hx x' hx' hxx'
  simp only [agreePointsApprox, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx hx'
  have hf : lineApprox f δ i x = lineApprox f δ i x' := by
    rw [← lineApprox_update f δ i x 0, ← lineApprox_update f δ i x' 0]
    exact congrArg (lineApprox f δ i) hxx'
  have hg' : lineRestrict g x i = lineRestrict g x' i := by
    rw [← lineRestrict_update g x i 0, ← lineRestrict_update g x' i 0]
    exact congrArg (lineRestrict g · i) hxx'
  have hxi : x i = x' i := by
    by_contra hne
    refine hx.2.1 ((isAffineFun_lineApprox hx.1).eq_of_eq_of_eq (hg x i) hne ?_ ?_)
    · simpa [lineRestrict] using hx.2.2
    · rw [hf, hg']
      simpa [lineRestrict] using hx'.2.2
  calc x = update (update x i 0) i (x i) := by simp
    _ = update (update x' i 0) i (x' i) := by
      rw [show update x i 0 = update x' i 0 from hxx', hxi]
    _ = x' := by simp

/-- **The self-improvement lemma for `δ`-approximate affineness**: a multilinear function `g`
that agrees with `f` on at least half of the points agrees with it outside at most
`(2 n + 1) (∑ᵢ |Wᵢ| + n δ |F| ^ n) + 2 n ^ 2 |F| ^ (n - 1)` points, where
`Wᵢ = wrongPointsApprox f δ i` [Babai, Fortnow, Lund, Lemma 5.10][BabaiFortnowLund1991]. -/
theorem IsMultilinear.hammingDist_le_of_two_mul_le_approx {f g : (Fin n → F) → F}
    (hg : IsMultilinear g) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : 2 * hammingDist f g ≤ Fintype.card F ^ n) :
    (hammingDist f g : ℝ) ≤ (2 * (n : ℝ) + 1) * (∑ i, (#(wrongPointsApprox f δ i) : ℝ) +
        n * δ * (Fintype.card F : ℝ) ^ n) +
      2 * (n : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ (n - 1) := by
  classical
  let B : Finset (Fin n → F) := {x | f x ≠ g x}
  let W : Finset (Fin n → F) := univ.biUnion (wrongPointsApprox f δ)
  let C : Finset (Fin n → F) := univ.biUnion (corruptPoints f δ)
  let I : Finset (Fin n → F) := univ.biUnion (agreePointsApprox f g δ)
  let S : Finset (Fin n → F) := B \ (W ∪ C)
  have hB : #B = hammingDist f g := rfl
  -- A point outside `S` on a line through a point of `S` is wrong, corrupt, or an agreement point.
  have hcl : lineClosure S \ S ⊆ (W ∪ C) ∪ I := by
    intro y hy
    simp only [mem_sdiff, mem_lineClosure] at hy
    obtain ⟨⟨i, t, hs⟩, hyS⟩ := hy
    simp only [S, B, W, C, mem_sdiff, mem_filter, mem_univ, true_and, mem_union, mem_biUnion,
      not_or, not_exists] at hs hyS
    simp only [W, C, I, mem_union, mem_biUnion, mem_univ, true_and]
    by_cases hyW : ∃ j, y ∈ wrongPointsApprox f δ j
    · exact Or.inl (Or.inl hyW)
    by_cases hyC : ∃ j, y ∈ corruptPoints f δ j
    · exact Or.inl (Or.inr hyC)
    right
    push Not at hyW hyC
    have hfy : f y = g y := by
      by_contra hne
      exact hyS ⟨hne, hyW, hyC⟩
    have hxC : f (update y i t) = lineApprox f δ i (update y i t) ((update y i t) i) := by
      have := hs.2.2 i
      simp only [corruptPoints, mem_filter, mem_univ, true_and, not_and, not_not] at this
      exact this (hs.2.1 i)
    have hyC' : f y = lineApprox f δ i y (y i) := by
      have := hyC i
      simp only [corruptPoints, mem_filter, mem_univ, true_and, not_and, not_not] at this
      exact this (hyW i)
    refine ⟨i, ?_⟩
    simp only [agreePointsApprox, mem_filter, mem_univ, true_and]
    refine ⟨hyW i, fun heq => hs.1 ?_, hyC'.symm.trans hfy⟩
    have hval := congrFun heq t
    rw [lineApprox_update, update_self] at hxC
    exact hxC.trans hval
  have hexp : #S ≤ 2 * n * #(lineClosure S \ S) := by
    refine card_le_two_mul_card_lineClosure_sdiff ?_
    exact (Nat.mul_le_mul_left 2 (card_le_card sdiff_subset)).trans (hB ▸ h)
  have hW : (#W : ℝ) ≤ ∑ i, (#(wrongPointsApprox f δ i) : ℝ) := by
    exact_mod_cast (card_biUnion_le : #W ≤ ∑ i, #(wrongPointsApprox f δ i))
  have hC : (#C : ℝ) ≤ n * δ * (Fintype.card F : ℝ) ^ n := by
    calc (#C : ℝ) ≤ ∑ i, (#(corruptPoints f δ i) : ℝ) := by
          exact_mod_cast (card_biUnion_le : #C ≤ ∑ i, #(corruptPoints f δ i))
      _ ≤ ∑ _i : Fin n, δ * (Fintype.card F : ℝ) ^ n :=
          sum_le_sum fun i _ => card_corruptPoints_le f hδ i
      _ = n * δ * (Fintype.card F : ℝ) ^ n := by simp [mul_assoc]
  have hWC : (#(W ∪ C) : ℝ) ≤ ∑ i, (#(wrongPointsApprox f δ i) : ℝ) +
      n * δ * (Fintype.card F : ℝ) ^ n := by
    have h1 : (#(W ∪ C) : ℝ) ≤ (#W : ℝ) + (#C : ℝ) := by exact_mod_cast card_union_le W C
    linarith only [h1, hW, hC]
  have hI : #I ≤ n * Fintype.card F ^ (n - 1) := by
    refine card_biUnion_le.trans ?_
    calc ∑ i, #(agreePointsApprox f g δ i) ≤ ∑ _i : Fin n, Fintype.card F ^ (n - 1) :=
          sum_le_sum fun i _ => card_agreePointsApprox_le hg δ i
      _ = n * Fintype.card F ^ (n - 1) := by simp
  have hBS : #B ≤ #S + #(W ∪ C) := by
    refine (card_le_card ?_).trans (card_union_le S (W ∪ C))
    intro x hx
    by_cases hxWC : x ∈ W ∪ C
    · exact mem_union_right _ hxWC
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hx, hxWC⟩)
  have hcl' := (card_le_card hcl).trans (card_union_le (W ∪ C) I)
  have hnat : #B ≤ (2 * n + 1) * #(W ∪ C) + 2 * n * #I := by
    calc #B ≤ 2 * n * (#(W ∪ C) + #I) + #(W ∪ C) :=
          hBS.trans (Nat.add_le_add_right (hexp.trans (Nat.mul_le_mul_left _ hcl')) _)
      _ = (2 * n + 1) * #(W ∪ C) + 2 * n * #I := by ring
  have hreal : (#B : ℝ) ≤ (2 * (n : ℝ) + 1) * #(W ∪ C) + 2 * (n : ℝ) * #I := by
    exact_mod_cast hnat
  have hIr : (#I : ℝ) ≤ (n : ℝ) * (Fintype.card F : ℝ) ^ (n - 1) := by exact_mod_cast hI
  rw [← hB]
  calc (#B : ℝ) ≤ (2 * (n : ℝ) + 1) * #(W ∪ C) + 2 * (n : ℝ) * #I := hreal
    _ ≤ (2 * (n : ℝ) + 1) * (∑ i, (#(wrongPointsApprox f δ i) : ℝ) +
          n * δ * (Fintype.card F : ℝ) ^ n) +
        2 * (n : ℝ) * ((n : ℝ) * (Fintype.card F : ℝ) ^ (n - 1)) := by gcongr
    _ = _ := by ring

/-- **The self-improvement lemma**: a multilinear function `g` that agrees with `f` on at least half
of the points agrees with it outside at most `(2 n + 1) ∑ᵢ |Wᵢ| + 2 n ^ 2 |F| ^ (n - 1)` points,
where `Wᵢ = wrongPoints f i` [Babai, Fortnow, Lund, Lemma 5.10][BabaiFortnowLund1991]. -/
theorem IsMultilinear.hammingDist_le_of_two_mul_le {f g : (Fin n → F) → F} (hg : IsMultilinear g)
    (h : 2 * hammingDist f g ≤ Fintype.card F ^ n) :
    hammingDist f g ≤
      (2 * n + 1) * ∑ i, #(wrongPoints f i) + 2 * n ^ 2 * Fintype.card F ^ (n - 1) := by
  have hr := hg.hammingDist_le_of_two_mul_le_approx (δ := 0) le_rfl h
  simp only [wrongPointsApprox_zero, mul_zero, zero_mul, add_zero] at hr
  exact_mod_cast hr

/-- **Self-improvement over the reals** for `δ`-approximate affineness: a multilinear `g` within
a fraction `c ≤ 1 / 2` of `f` satisfies the `δ`-approximate Lemma 5.10 bound. -/
private theorem IsMultilinear.hammingDist_le_of_le_mul_approx {k : ℕ} {f g : (Fin k → F) → F}
    (hg : IsMultilinear g) {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 2 * c ≤ 1)
    (h : (hammingDist f g : ℝ) ≤ c * (Fintype.card F : ℝ) ^ k) :
    (hammingDist f g : ℝ) ≤ (2 * (k : ℝ) + 1) * (∑ i, (#(wrongPointsApprox f δ i) : ℝ) +
        k * δ * (Fintype.card F : ℝ) ^ k) +
      2 * (k : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ (k - 1) := by
  have h2 : ((2 * hammingDist f g : ℕ) : ℝ) ≤ ((Fintype.card F ^ k : ℕ) : ℝ) := by
    push_cast
    linarith only [h, mul_assoc (2 : ℝ) c ((Fintype.card F : ℝ) ^ k),
      mul_le_of_le_one_left (by positivity : (0 : ℝ) ≤ (Fintype.card F : ℝ) ^ k) hc]
  exact hg.hammingDist_le_of_two_mul_le_approx hδ (by exact_mod_cast h2)

open Classical in
private theorem card_wrongPointsApprox_succ (f : (Fin (n + 1) → F) → F) (δ : ℝ) (j : Fin n) :
    #(wrongPointsApprox f δ j.succ) =
      ∑ t, #(wrongPointsApprox (fun y => f (Fin.cons t y)) δ j) := by
  have hline (x : Fin (n + 1) → F) :
      lineRestrict f x j.succ = lineRestrict (fun y => f (Fin.cons (x 0) y)) (Fin.tail x) j := by
    funext t
    simp only [lineRestrict, Fin.cons_update, Fin.cons_self_tail]
  have : wrongPointsApprox f δ j.succ =
      ({x | ¬IsApproxAffine δ
        (lineRestrict (fun y => f (Fin.cons (x 0) y)) (Fin.tail x) j)} :
          Finset (Fin (n + 1) → F)) := by
    ext x
    simp only [wrongPointsApprox, mem_filter, mem_univ, true_and, hline]
  rw [this]
  exact Fin.card_filter_zero_tail
    (fun t y => ¬IsApproxAffine δ (lineRestrict (fun y => f (Fin.cons t y)) y j))

/-- The `δ`-wrong points of the slices `x 0 = t` add up to at most those of `f`. -/
private theorem sum_sum_card_wrongPointsApprox_le (f : (Fin (n + 1) → F) → F) (δ : ℝ) :
    ∑ t, ∑ j : Fin n, #(wrongPointsApprox (fun y => f (Fin.cons t y)) δ j) ≤
      ∑ i, #(wrongPointsApprox f δ i) := by
  rw [Fin.sum_univ_succ, sum_comm]
  simp only [← card_wrongPointsApprox_succ]
  exact Nat.le_add_left _ _

open Classical in
/-- Slice interpolation for `δ`-approximate affineness: interpolating multilinear approximations
`g₁`, `g₂` of two slices `t₁ ≠ t₂` misses only direction-`0` `δ`-wrong points, direction-`0`
corrupt points, and points over slice errors or slice corruptions. -/
private theorem exists_isMultilinear_hammingDist_le_of_slices_approx (f : (Fin (n + 1) → F) → F)
    (δ : ℝ) {t₁ t₂ : F} (h12 : t₁ ≠ t₂) {g₁ g₂ : (Fin n → F) → F}
    (hg₁ : IsMultilinear g₁) (hg₂ : IsMultilinear g₂) :
    ∃ g, IsMultilinear g ∧ hammingDist f g ≤
      #(wrongPointsApprox f δ 0) + #(corruptPoints f δ 0) +
        Fintype.card F *
          ((hammingDist (fun y => f (Fin.cons t₁ y)) g₁ +
              #{y : Fin n → F | Fin.cons t₁ y ∈ corruptPoints f δ 0}) +
            (hammingDist (fun y => f (Fin.cons t₂ y)) g₂ +
              #{y : Fin n → F | Fin.cons t₂ y ∈ corruptPoints f δ 0})) := by
  have hd : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  let g := sliceInterpolant t₁ t₂ g₁ g₂
  have hg0 := lineRestrict_sliceInterpolant_zero t₁ t₂ g₁ g₂
  have hg : IsMultilinear g := isMultilinear_sliceInterpolant t₁ t₂ hg₁ hg₂
  refine ⟨g, hg, ?_⟩
  let bad (t : F) (h : (Fin n → F) → F) : Finset (Fin (n + 1) → F) :=
    {x | f (Fin.cons t (Fin.tail x)) ≠ h (Fin.tail x) ∨
      Fin.cons t (Fin.tail x) ∈ corruptPoints f δ 0}
  have hsub : ({x | f x ≠ g x} : Finset (Fin (n + 1) → F)) ⊆
      (wrongPointsApprox f δ 0 ∪ corruptPoints f δ 0) ∪ (bad t₁ g₁ ∪ bad t₂ g₂) := by
    intro x hx
    simp only [bad, mem_filter, mem_univ, true_and, mem_union] at hx ⊢
    by_contra! hc
    obtain ⟨⟨hnotW, hnotC⟩, ⟨h1, hC1⟩, ⟨h2, hC2⟩⟩ := hc
    have hcons (t : F) : update x 0 t = Fin.cons t (Fin.tail x) := by
      rw [← Fin.update_cons_zero (x 0) (Fin.tail x) t, Fin.cons_self_tail]
    have hl_aff : IsAffineFun (lineApprox f δ 0 x) := isAffineFun_lineApprox hnotW
    have hxval : lineApprox f δ 0 x (x 0) = f x := by
      simp only [corruptPoints, mem_filter, mem_univ, true_and, not_and, not_not] at hnotC
      exact (hnotC hnotW).symm
    have htval (t : F) (hnotCt : Fin.cons t (Fin.tail x) ∉ corruptPoints f δ 0) :
        lineApprox f δ 0 x t = f (Fin.cons t (Fin.tail x)) := by
      have hnotWt : Fin.cons t (Fin.tail x) ∉ wrongPointsApprox f δ 0 := by
        rw [← hcons, mem_wrongPointsApprox_update]
        exact hnotW
      simp only [corruptPoints, mem_filter, mem_univ, true_and, not_and, not_not] at hnotCt
      have heq := (hnotCt hnotWt).symm
      simpa [← hcons, lineApprox_update] using heq
    have hline := hl_aff.eq_of_eq_of_eq (hg x 0) h12
      (by rw [hg0]; simp only [htval t₁ hC1, h1, sub_self, zero_div, zero_mul, add_zero])
      (by rw [hg0]; simp only [htval t₂ hC2, h2, div_self hd, one_mul, add_sub_cancel])
    exact hx (hxval.symm.trans (by simpa using congrFun hline (x 0)))
  have hcard (t : F) (h : (Fin n → F) → F) :
      #(bad t h) ≤ Fintype.card F *
        (hammingDist (fun y => f (Fin.cons t y)) h +
          #{y : Fin n → F | Fin.cons t y ∈ corruptPoints f δ 0}) := by
    have hsplit : bad t h = ({x | f (Fin.cons t (Fin.tail x)) ≠ h (Fin.tail x)} :
          Finset (Fin (n + 1) → F)) ∪
        ({x | Fin.cons t (Fin.tail x) ∈ corruptPoints f δ 0} : Finset (Fin (n + 1) → F)) := by
      ext x
      simp [bad]
    rw [hsplit]
    calc #(_ ∪ _) ≤ #{x : Fin (n + 1) → F | f (Fin.cons t (Fin.tail x)) ≠ h (Fin.tail x)} +
          #{x : Fin (n + 1) → F | Fin.cons t (Fin.tail x) ∈ corruptPoints f δ 0} :=
          card_union_le _ _
      _ = Fintype.card F * hammingDist (fun y => f (Fin.cons t y)) h +
            Fintype.card F * #{y : Fin n → F | Fin.cons t y ∈ corruptPoints f δ 0} := by
          rw [Fin.card_filter_zero_tail (fun _ y => f (Fin.cons t y) ≠ h y),
            Fin.card_filter_zero_tail (fun _ y => Fin.cons t y ∈ corruptPoints f δ 0),
            sum_const, sum_const, card_univ, smul_eq_mul, smul_eq_mul, hammingDist]
      _ = _ := by rw [← mul_add]
  calc hammingDist f g = #({x | f x ≠ g x} : Finset (Fin (n + 1) → F)) := rfl
    _ ≤ #(wrongPointsApprox f δ 0 ∪ corruptPoints f δ 0) + (#(bad t₁ g₁) + #(bad t₂ g₂)) :=
        (card_le_card hsub).trans ((card_union_le _ _).trans
          (Nat.add_le_add_left (card_union_le _ _) _))
    _ ≤ #(wrongPointsApprox f δ 0) + #(corruptPoints f δ 0) + (#(bad t₁ g₁) + #(bad t₂ g₂)) :=
        Nat.add_le_add_right (card_union_le _ _) _
    _ ≤ _ := by
        refine Nat.add_le_add_left ?_ _
        rw [mul_add]
        exact Nat.add_le_add (hcard t₁ g₁) (hcard t₂ g₂)

open Classical in
/-- Induction on the dimension for `δ`-approximate multilinearity testing, using thresholds
decaying by `1 - 1 / (2 n)` per dimension and a `1 / 40` Markov budget on direction-`0` corrupt
points. -/
private theorem exists_isMultilinear_hammingDist_le_mul_approx {m : ℕ} (hm : 0 < m)
    {δ ε₀ γ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (400 * (m : ℝ) ^ 2))
    (hqm : 40 * (m : ℝ) ^ 2 ≤ Fintype.card F) (hε₀ : 0 ≤ ε₀)
    (hγ : ε₀ + δ + 1 / 20 + 2 * γ ≤ 1 / 2) :
    ∀ k : ℕ, (2 * (k : ℝ) + 1) * (ε₀ + k * δ) + 2 * (k : ℝ) ^ 2 / Fintype.card F ≤ γ →
      ∀ h : (Fin k → F) → F, (∑ i, (#(wrongPointsApprox h δ i) : ℝ)) <
        (1 - 1 / (2 * (m : ℝ))) ^ k * ε₀ * (Fintype.card F : ℝ) ^ k →
        ∃ g, IsMultilinear g ∧ (hammingDist h g : ℝ) ≤ γ * (Fintype.card F : ℝ) ^ k := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hr_nonneg : 0 ≤ 1 - 1 / (2 * (m : ℝ)) := by
    have : 1 / (2 * (m : ℝ)) ≤ 1 := (div_le_one (by positivity)).2 (by linarith only [hm1])
    linarith only [this]
  have hr_le_one : 1 - 1 / (2 * (m : ℝ)) ≤ 1 := sub_le_self _ (by positivity)
  intro k
  induction k with
  | zero =>
    intro hk h _
    refine ⟨h, fun _ i => i.elim0, ?_⟩
    simp only [hammingDist_self, Nat.cast_zero, pow_zero, mul_one]
    simp only [CharP.cast_eq_zero, zero_mul, add_zero, mul_zero, zero_add, one_mul, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div] at hk
    linarith only [hk, hε₀]
  | succ k ih =>
    intro hk f hf
    have hk' : (2 * (k : ℝ) + 1) * (ε₀ + k * δ) + 2 * (k : ℝ) ^ 2 / Fintype.card F ≤ γ := by
      refine le_trans ?_ hk
      push_cast
      gcongr <;> linarith only [Nat.cast_nonneg (α := ℝ) k]
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ,
        θ = (1 - 1 / (2 * (m : ℝ))) ^ k * ε₀ * (Fintype.card F : ℝ) ^ k := ⟨_, rfl⟩
    rw [← hθ] at ih
    have hT : (∑ i, (#(wrongPointsApprox f δ i) : ℝ)) <
        ((1 - 1 / (2 * (m : ℝ))) * Fintype.card F) * θ := by
      calc _ < _ := hf
        _ = ((1 - 1 / (2 * (m : ℝ))) * Fintype.card F) *
            ((1 - 1 / (2 * (m : ℝ))) ^ k * ε₀ * (Fintype.card F : ℝ) ^ k) := by ring
        _ = _ := by rw [hθ]
    have hθpos : 0 < θ := by
      have h0 : (0 : ℝ) ≤ ∑ i, (#(wrongPointsApprox f δ i) : ℝ) := by positivity
      have hmul : 0 < ((1 - 1 / (2 * (m : ℝ))) * Fintype.card F) * θ := h0.trans_lt hT
      exact pos_of_mul_pos_right hmul (mul_nonneg hr_nonneg hq.le)
    -- At least two slices have `< θ` wrong points and `< (1 / 40) |F|^k` direction-0 corrupt
    -- points.
    let badW : Finset F :=
      {t | θ ≤ ∑ j, (#(wrongPointsApprox (fun y => f (Fin.cons t y)) δ j) : ℝ)}
    let badC : Finset F :=
      {t | (1 / 40 : ℝ) * (Fintype.card F : ℝ) ^ k ≤
        (#{y : Fin k → F | Fin.cons t y ∈ corruptPoints f δ 0} : ℝ)}
    have hbadW : (#badW : ℝ) * θ < ((1 - 1 / (2 * (m : ℝ))) * Fintype.card F) * θ := by
      calc (#badW : ℝ) * θ = ∑ _t ∈ badW, θ := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ t ∈ badW, ∑ j, (#(wrongPointsApprox (fun y => f (Fin.cons t y)) δ j) : ℝ) := by
            refine sum_le_sum fun t ht => ?_
            simp only [badW, mem_filter, mem_univ, true_and] at ht
            exact ht
        _ ≤ ∑ t, ∑ j, (#(wrongPointsApprox (fun y => f (Fin.cons t y)) δ j) : ℝ) :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
        _ ≤ ∑ i, (#(wrongPointsApprox f δ i) : ℝ) := by
            exact_mod_cast sum_sum_card_wrongPointsApprox_le f δ
        _ < _ := hT
    have hbadW_lt : (#badW : ℝ) < (1 - 1 / (2 * (m : ℝ))) * Fintype.card F :=
      lt_of_mul_lt_mul_right hbadW hθpos.le
    have hsumC : ∑ t : F, (#{y : Fin k → F | Fin.cons t y ∈ corruptPoints f δ 0} : ℝ) =
        (#(corruptPoints f δ 0) : ℝ) := by
      have heq : ∑ t : F, #{y : Fin k → F | Fin.cons t y ∈ corruptPoints f δ 0} =
          #(corruptPoints f δ 0) := by
        rw [← Fin.card_filter_zero_tail (fun t y => Fin.cons t y ∈ corruptPoints f δ 0)]
        simp [Fin.cons_self_tail]
      exact_mod_cast heq
    have hbadC : (#badC : ℝ) * ((1 / 40 : ℝ) * (Fintype.card F : ℝ) ^ k) ≤
        δ * (Fintype.card F : ℝ) ^ (k + 1) := by
      calc (#badC : ℝ) * ((1 / 40 : ℝ) * (Fintype.card F : ℝ) ^ k) =
            ∑ _t ∈ badC, ((1 / 40 : ℝ) * (Fintype.card F : ℝ) ^ k) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ t ∈ badC, (#{y : Fin k → F | Fin.cons t y ∈ corruptPoints f δ 0} : ℝ) := by
            refine sum_le_sum fun t ht => ?_
            simp only [badC, mem_filter, mem_univ, true_and] at ht
            exact ht
        _ ≤ ∑ t, (#{y : Fin k → F | Fin.cons t y ∈ corruptPoints f δ 0} : ℝ) :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
        _ = (#(corruptPoints f δ 0) : ℝ) := hsumC
        _ ≤ δ * (Fintype.card F : ℝ) ^ (k + 1) := card_corruptPoints_le f hδ0 0
    have hbadC_le : (#badC : ℝ) ≤ 40 * δ * Fintype.card F := by
      have hden : (0 : ℝ) < (1 / 40 : ℝ) * (Fintype.card F : ℝ) ^ k := by positivity
      refine le_of_mul_le_mul_right (hbadC.trans_eq ?_) hden
      ring
    -- Bound `(40 * δ - 1 / (2 m)) * |F| ≤ -16 ≤ -2`, leaving at least two good slices.
    have hm_sq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      rw [sq]
      exact le_mul_of_one_le_left (by positivity) hm1
    have hδm : 40 * δ ≤ 1 / (10 * (m : ℝ)) := by
      have h1 : 400 * (m : ℝ) ^ 2 * δ ≤ 1 := by rwa [le_div_iff₀' (by positivity)] at hδ
      have h2 : 400 * (m : ℝ) * δ ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hm_sq hδ0
        linarith only [h1, this, mul_assoc (400 : ℝ) ((m : ℝ) ^ 2) δ,
          mul_assoc (400 : ℝ) (m : ℝ) δ]
      rw [le_div_iff₀' (by positivity)]
      linarith only [h2, mul_assoc (10 : ℝ) (m : ℝ) (40 * δ)]
    have hgap : (4 / (10 * (m : ℝ))) * Fintype.card F ≥ 16 := by
      have hcalc : (4 / (10 * (m : ℝ))) * (40 * (m : ℝ) ^ 2) = 16 * m := by
        have hm0 : (m : ℝ) ≠ 0 := by linarith only [hm1]
        field_simp
        ring
      have h1 : 16 * (m : ℝ) ≤ (4 / (10 * (m : ℝ))) * Fintype.card F :=
        hcalc ▸ mul_le_mul_of_nonneg_left hqm (by positivity)
      linarith only [h1, hm1]
    have htotal : (#badW : ℝ) + (#badC : ℝ) < (Fintype.card F : ℝ) - 16 := by
      have hcomb : (1 - 1 / (2 * (m : ℝ))) * (Fintype.card F : ℝ) + 40 * δ * Fintype.card F ≤
          (Fintype.card F : ℝ) - (4 / (10 * (m : ℝ))) * Fintype.card F := by
        have hstep : 1 - 1 / (2 * (m : ℝ)) + 40 * δ ≤ 1 - 4 / (10 * (m : ℝ)) := by
          have hm0 : (m : ℝ) ≠ 0 := by linarith only [hm1]
          have heq : (1 : ℝ) - 1 / (2 * m) + 1 / (10 * m) = 1 - 4 / (10 * m) := by
            field_simp; ring
          linarith only [hδm, heq]
        have := mul_le_mul_of_nonneg_right hstep hq.le
        linarith only [this]
      linarith only [hbadW_lt, hbadC_le, hcomb, hgap]
    let good : Finset F := (badW ∪ badC)ᶜ
    have hcompl_le : #goodᶜ ≤ #badW + #badC := by
      simpa [good, compl_compl] using card_union_le badW badC
    have hlt_nat : #goodᶜ + 1 < Fintype.card F := by
      have hlt_r : ((#badW + #badC + 1 : ℕ) : ℝ) < Fintype.card F := by
        push_cast; linarith only [htotal]
      have : #badW + #badC + 1 < Fintype.card F := by exact_mod_cast hlt_r
      omega
    have hcard : #good + #goodᶜ = Fintype.card F := card_add_card_compl good
    obtain ⟨t₁, ht₁, t₂, ht₂, h12⟩ := one_lt_card.mp (by omega : 1 < #good)
    have ht₁W : (∑ j, (#(wrongPointsApprox (fun y => f (Fin.cons t₁ y)) δ j) : ℝ)) < θ := by
      simp only [good, badW, mem_compl, mem_union, mem_filter, mem_univ, true_and, not_or,
        not_le] at ht₁
      exact ht₁.1
    have ht₂W : (∑ j, (#(wrongPointsApprox (fun y => f (Fin.cons t₂ y)) δ j) : ℝ)) < θ := by
      simp only [good, badW, mem_compl, mem_union, mem_filter, mem_univ, true_and, not_or,
        not_le] at ht₂
      exact ht₂.1
    have ht₁C : (#{y : Fin k → F | Fin.cons t₁ y ∈ corruptPoints f δ 0} : ℝ) <
        (1 / 40 : ℝ) * (Fintype.card F : ℝ) ^ k := by
      simp only [good, badC, mem_compl, mem_union, mem_filter, mem_univ, true_and, not_or,
        not_le] at ht₁
      exact ht₁.2
    have ht₂C : (#{y : Fin k → F | Fin.cons t₂ y ∈ corruptPoints f δ 0} : ℝ) <
        (1 / 40 : ℝ) * (Fintype.card F : ℝ) ^ k := by
      simp only [good, badC, mem_compl, mem_union, mem_filter, mem_univ, true_and, not_or,
        not_le] at ht₂
      exact ht₂.2
    obtain ⟨g₁, hg₁, hd₁⟩ := ih hk' _ ht₁W
    obtain ⟨g₂, hg₂, hd₂⟩ := ih hk' _ ht₂W
    obtain ⟨g, hg, hfg⟩ :=
      exists_isMultilinear_hammingDist_le_of_slices_approx f δ h12 hg₁ hg₂
    refine ⟨g, hg, ?_⟩
    have hpow : (1 - 1 / (2 * (m : ℝ))) ^ (k + 1) ≤ 1 := pow_le_one₀ hr_nonneg hr_le_one
    have hTle : (∑ i, (#(wrongPointsApprox f δ i) : ℝ)) ≤
        ε₀ * (Fintype.card F : ℝ) ^ (k + 1) := by
      calc _ ≤ _ := hf.le
        _ ≤ 1 * ε₀ * (Fintype.card F : ℝ) ^ (k + 1) := by gcongr
        _ = ε₀ * (Fintype.card F : ℝ) ^ (k + 1) := by ring
    have hW0 : (#(wrongPointsApprox f δ 0) : ℝ) ≤ ∑ i, (#(wrongPointsApprox f δ i) : ℝ) :=
      single_le_sum (f := fun i => (#(wrongPointsApprox f δ i) : ℝ)) (fun i _ => by positivity)
        (mem_univ (0 : Fin (k + 1)))
    have hhalf : (hammingDist f g : ℝ) ≤
        (ε₀ + δ + 1 / 20 + 2 * γ) * (Fintype.card F : ℝ) ^ (k + 1) := by
      calc (hammingDist f g : ℝ) ≤ (#(wrongPointsApprox f δ 0) : ℝ) +
            (#(corruptPoints f δ 0) : ℝ) + (Fintype.card F : ℝ) *
              (((hammingDist (fun y => f (Fin.cons t₁ y)) g₁ : ℝ) +
                  #{y : Fin k → F | Fin.cons t₁ y ∈ corruptPoints f δ 0}) +
                ((hammingDist (fun y => f (Fin.cons t₂ y)) g₂ : ℝ) +
                  #{y : Fin k → F | Fin.cons t₂ y ∈ corruptPoints f δ 0})) := by
              exact_mod_cast hfg
        _ ≤ ε₀ * (Fintype.card F : ℝ) ^ (k + 1) + δ * (Fintype.card F : ℝ) ^ (k + 1) +
              (Fintype.card F : ℝ) *
                ((γ * (Fintype.card F : ℝ) ^ k + (1 / 40 : ℝ) * (Fintype.card F : ℝ) ^ k) +
                  (γ * (Fintype.card F : ℝ) ^ k + (1 / 40 : ℝ) * (Fintype.card F : ℝ) ^ k)) := by
              gcongr
              · exact hW0.trans hTle
              · exact card_corruptPoints_le f hδ0 0
        _ = (ε₀ + δ + 1 / 20 + 2 * γ) * (Fintype.card F : ℝ) ^ (k + 1) := by ring
    have hself := hg.hammingDist_le_of_le_mul_approx hδ0 (by linarith only [hε₀, hδ0, hγ]) hhalf
    rw [Nat.add_sub_cancel] at hself
    calc (hammingDist f g : ℝ) ≤ _ := hself
      _ ≤ (2 * ((k + 1 : ℕ) : ℝ) + 1) *
            (ε₀ * (Fintype.card F : ℝ) ^ (k + 1) +
              ((k + 1 : ℕ) : ℝ) * δ * (Fintype.card F : ℝ) ^ (k + 1)) +
            2 * ((k + 1 : ℕ) : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ k := by gcongr
      _ = ((2 * ((k + 1 : ℕ) : ℝ) + 1) * (ε₀ + ((k + 1 : ℕ) : ℝ) * δ) +
            2 * ((k + 1 : ℕ) : ℝ) ^ 2 / Fintype.card F) * (Fintype.card F : ℝ) ^ (k + 1) := by
          field_simp
          ring
      _ ≤ γ * (Fintype.card F : ℝ) ^ (k + 1) := by gcongr

/-- **Polynomial soundness of the multilinearity test (`δ`-approximate lines)**: if in every
direction fewer than an `ε` fraction of lines fail to be `δ`-approximately affine
(`Cslib.Code.wrongPointsApprox`), `|F| ≥ 40 n ^ 2`, `0 ≤ δ ≤ 1 / (400 n ^ 2)` and
`ε ≤ 1 / (800 n ^ 3)`, then some multilinear function agrees with `f` outside fewer than a
`3 n ^ 2 (ε + δ + 1 / |F|)` fraction of the points
[Babai, Fortnow, Lund, Theorem 5.13][BabaiFortnowLund1991]. -/
theorem exists_isMultilinear_hammingDist_lt_of_approx (f : (Fin n → F) → F) {ε δ : ℝ}
    (hn : 0 < n) (hq : 40 * n ^ 2 ≤ Fintype.card F) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / (400 * n ^ 2)) (hε : ε ≤ 1 / (800 * n ^ 3))
    (hW : ∀ i, (#(wrongPointsApprox f δ i) : ℝ) < ε * Fintype.card F ^ n) :
    ∃ g, IsMultilinear g ∧
      (hammingDist f g : ℝ) < 3 * n ^ 2 * (ε + δ + 1 / Fintype.card F) * Fintype.card F ^ n := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hqr : 40 * (n : ℝ) ^ 2 ≤ Fintype.card F := by exact_mod_cast hq
  have hεpos : 0 < ε := by
    have h0 : (0 : ℝ) ≤ #(wrongPointsApprox f δ ⟨0, hn⟩) := by positivity
    have : 0 < ε * (Fintype.card F : ℝ) ^ n := h0.trans_lt (hW ⟨0, hn⟩)
    exact pos_of_mul_pos_left this (by positivity)
  have hsum : (∑ i, (#(wrongPointsApprox f δ i) : ℝ)) < n * ε * (Fintype.card F : ℝ) ^ n := by
    calc (∑ i, (#(wrongPointsApprox f δ i) : ℝ)) < ∑ _i : Fin n, ε * (Fintype.card F : ℝ) ^ n :=
          sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, mem_univ _⟩ fun i _ => hW i
      _ = n * ε * (Fintype.card F : ℝ) ^ n := by simp [mul_assoc]
  -- Run the induction with `ε₀ = 3 n ε` and `γ = 1 / 5`.
  have hn2 : (n : ℝ) ≤ n ^ 2 := by rw [sq]; exact le_mul_of_one_le_left (Nat.cast_nonneg n) hnr
  have hn3 : (n : ℝ) ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hnr (by decide)
  have hεn : (n : ℝ) ^ 2 * ε ≤ 1 / 800 := by
    have h1 : 800 * (n : ℝ) ^ 3 * ε ≤ 1 := by rwa [le_div_iff₀' (by positivity)] at hε
    linarith only [h1, mul_le_mul_of_nonneg_right hn3 hεpos.le,
      mul_assoc (800 : ℝ) ((n : ℝ) ^ 3) ε]
  have hε1 : (n : ℝ) * ε ≤ 1 / 800 := (mul_le_mul_of_nonneg_right hn2 hεpos.le).trans hεn
  have hδn : (n : ℝ) ^ 2 * δ ≤ 1 / 400 := by
    have h1 : 400 * (n : ℝ) ^ 2 * δ ≤ 1 := by rwa [le_div_iff₀' (by positivity)] at hδ
    linarith only [h1, mul_assoc (400 : ℝ) ((n : ℝ) ^ 2) δ]
  have hδ1 : δ ≤ 1 / 400 := by
    have hsq1 : (1 : ℝ) ≤ n ^ 2 := hnr.trans hn2
    linarith only [hδn, mul_le_mul_of_nonneg_right hsq1 hδ0]
  have hqn : 2 * (n : ℝ) ^ 2 / Fintype.card F ≤ 1 / 20 :=
    (div_le_iff₀ hq0).2 (by linarith only [hqr])
  have hpow : (1 : ℝ) / 2 ≤ (1 - 1 / (2 * (n : ℝ))) ^ n := by
    have h1n : 1 / (2 * (n : ℝ)) ≤ 1 := (div_le_one (by positivity)).2 (by linarith only [hnr])
    have hb := one_add_mul_le_pow (a := -(1 / (2 * (n : ℝ)))) (by linarith only [h1n]) n
    have hn2n : (n : ℝ) * (1 / (2 * (n : ℝ))) = 1 / 2 := by
      have hn0 : (n : ℝ) ≠ 0 := by linarith only [hnr]
      field_simp
    rw [← sub_eq_add_neg] at hb
    linarith only [hb, hn2n, mul_neg (n : ℝ) (1 / (2 * (n : ℝ)))]
  have hγ1 : 3 * (n : ℝ) * ε + δ + 1 / 20 + 2 * (1 / 5 : ℝ) ≤ 1 / 2 := by
    linarith only [hε1, hδ1, mul_assoc (3 : ℝ) (n : ℝ) ε]
  have hγ2 : (2 * (n : ℝ) + 1) * (3 * n * ε + n * δ) + 2 * n ^ 2 / Fintype.card F ≤ 1 / 5 := by
    have hle : (2 * (n : ℝ) + 1) * (3 * n * ε + n * δ) ≤
        3 * n * (3 * n * ε + n * δ) :=
      mul_le_mul_of_nonneg_right (by linarith only [hnr]) (by positivity)
    linarith only [hle, hεn, hδn, hqn,
      show 3 * (n : ℝ) * (3 * n * ε + n * δ) = 9 * (n ^ 2 * ε) + 3 * (n ^ 2 * δ) by ring]
  have hnε : (n : ℝ) * ε ≤ 1 / 2 * (3 * n * ε) := by
    linarith only [show (0 : ℝ) ≤ n * ε by positivity, mul_assoc (3 : ℝ) (n : ℝ) ε]
  obtain ⟨g, hg, hfg⟩ := exists_isMultilinear_hammingDist_le_mul_approx (F := F) hn hδ0 hδ hqr
    (by positivity) hγ1 n hγ2 f (by
      calc (∑ i, (#(wrongPointsApprox f δ i) : ℝ)) < n * ε * (Fintype.card F : ℝ) ^ n := hsum
        _ ≤ 1 / 2 * (3 * n * ε) * (Fintype.card F : ℝ) ^ n := by gcongr
        _ ≤ (1 - 1 / (2 * (n : ℝ))) ^ n * (3 * n * ε) * (Fintype.card F : ℝ) ^ n := by gcongr)
  refine ⟨g, hg, ?_⟩
  have hself' := hg.hammingDist_le_of_le_mul_approx hδ0 (by norm_num) hfg
  have hqn1 : (Fintype.card F : ℝ) ^ (n - 1) * Fintype.card F = (Fintype.card F : ℝ) ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hn_pos : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  calc (hammingDist f g : ℝ) ≤ _ := hself'
    _ < (2 * n + 1) * (n * ε * (Fintype.card F : ℝ) ^ n +
          n * δ * (Fintype.card F : ℝ) ^ n) +
        2 * (n : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ (n - 1) := by gcongr
    _ ≤ 3 * n ^ 2 * (ε + δ) * (Fintype.card F : ℝ) ^ n +
          2 * (n : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ (n - 1) := by
        rw [show (3 : ℝ) * n ^ 2 * (ε + δ) * (Fintype.card F : ℝ) ^ n =
            3 * n * (n * ε * (Fintype.card F : ℝ) ^ n + n * δ * (Fintype.card F : ℝ) ^ n) by ring]
        gcongr
        linarith only [hnr]
    _ ≤ 3 * n ^ 2 * (ε + δ + 1 / Fintype.card F) * (Fintype.card F : ℝ) ^ n := by
        rw [← hqn1, ← sub_nonneg]; field_simp; ring_nf; positivity

/-- **Polynomial soundness of the multilinearity test**, at `δ = 0`: if in every direction fewer
than an `ε` fraction of the lines carry a restriction of `f` that is not affine,
`|F| ≥ 40 n ^ 2` and `ε ≤ 1 / (800 n ^ 3)`, then some multilinear function agrees with `f`
outside fewer than a `3 n ^ 2 (ε + 1 / |F|)` fraction of the points
[Babai, Fortnow, Lund, Theorem 5.13][BabaiFortnowLund1991]. -/
theorem exists_isMultilinear_hammingDist_lt (f : (Fin n → F) → F) {ε : ℝ} (hn : 0 < n)
    (hq : 40 * n ^ 2 ≤ Fintype.card F) (hε : ε ≤ 1 / (800 * n ^ 3))
    (hW : ∀ i, (#(wrongPoints f i) : ℝ) < ε * Fintype.card F ^ n) :
    ∃ g, IsMultilinear g ∧
      (hammingDist f g : ℝ) < 3 * n ^ 2 * (ε + 1 / Fintype.card F) * Fintype.card F ^ n := by
  have h := exists_isMultilinear_hammingDist_lt_of_approx f (δ := 0) hn hq le_rfl (by positivity)
    hε (fun i => by simpa [wrongPointsApprox_zero] using hW i)
  simpa [add_zero] using h

/-- **Two-prover `Test0` soundness**: if a line oracle `L : Fin n → (Fin n → F) → (F → F)`
returning affine functions on canonical axis-parallel lines `update x i 0` agrees with a point
oracle `f` on a uniformly random `(i, x)` with rejection probability `< ε * δ / n`, then every
direction has fewer than an `ε` fraction of `δ`-wrong lines and `f` agrees with a multilinear
function outside a `3 n ^ 2 (ε + δ + 1 / |F|)` fraction of the points
[Babai, Fortnow, Lund, §5][BabaiFortnowLund1991]. -/
theorem exists_isMultilinear_hammingDist_lt_of_lineOracle (f : (Fin n → F) → F)
    (L : Fin n → (Fin n → F) → (F → F)) (hL : ∀ i x, IsAffineFun (L i x))
    {ε δ : ℝ} (hn : 0 < n) (hq : 40 * n ^ 2 ≤ Fintype.card F)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (400 * n ^ 2)) (hε : ε ≤ 1 / (800 * n ^ 3))
    (hrej : (𝔼 i : Fin n, 𝔼 x : Fin n → F,
      if L i (update x i 0) (x i) = f x then (0 : ℝ) else 1) < ε * δ / n) :
    ∃ g, IsMultilinear g ∧
      (hammingDist f g : ℝ) < 3 * n ^ 2 * (ε + δ + 1 / Fintype.card F) * Fintype.card F ^ n := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq' : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card (Fin n → F) : ℝ) = (Fintype.card F : ℝ) ^ n := by
    simp [Fintype.card_pi]
  -- Convert expected rejection over `(i, x)` into total disagreement count across directions.
  have hsum_rej : (∑ i : Fin n, (#({x | L i (update x i 0) (x i) ≠ f x} :
      Finset (Fin n → F)) : ℝ)) < ε * δ * (Fintype.card F : ℝ) ^ n := by
    have hexp (i : Fin n) :
        (𝔼 x : Fin n → F, if L i (update x i 0) (x i) = f x then (0 : ℝ) else (1 : ℝ)) =
          (#({x : Fin n → F | L i (update x i 0) (x i) ≠ f x} : Finset (Fin n → F)) : ℝ) /
            (Fintype.card F : ℝ) ^ n := by
      rw [Fintype.expect_eq_sum_div_card, hcard, Finset.natCast_card_filter]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [ite_not]
    simp_rw [hexp] at hrej
    rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin, ← sum_div, div_div,
      div_lt_iff₀ (show (0 : ℝ) < (Fintype.card F : ℝ) ^ n * n by positivity)] at hrej
    have hrhs : ε * δ / (n : ℝ) * ((Fintype.card F : ℝ) ^ n * n) =
        ε * δ * (Fintype.card F : ℝ) ^ n := by
      have hn0 : (n : ℝ) ≠ 0 := hn'.ne'
      field_simp
    rwa [hrhs] at hrej
  have hδpos : 0 < δ := by
    have h0 : (0 : ℝ) ≤ ∑ i : Fin n, (#({x | L i (update x i 0) (x i) ≠ f x} :
        Finset (Fin n → F)) : ℝ) := by positivity
    have hmul : 0 < ε * δ * (Fintype.card F : ℝ) ^ n := h0.trans_lt hsum_rej
    rcases lt_or_eq_of_le hδ0 with h | rfl
    · exact h
    · simp at hmul
  refine exists_isMultilinear_hammingDist_lt_of_approx f hn hq hδ0 hδ hε fun i => ?_
  let D : Finset (Fin n → F) := {x | L i (update x i 0) (x i) ≠ f x}
  have hDi : (#D : ℝ) < ε * δ * (Fintype.card F : ℝ) ^ n := by
    have hle : (#D : ℝ) ≤ ∑ j : Fin n, (#({x | L j (update x j 0) (x j) ≠ f x} :
        Finset (Fin n → F)) : ℝ) :=
      Finset.single_le_sum (f := fun j => (#({x | L j (update x j 0) (x j) ≠ f x} :
        Finset (Fin n → F)) : ℝ)) (fun _ _ => by positivity) (Finset.mem_univ i)
    exact hle.trans_lt hsum_rej
  -- Count line-point disagreements inside `wrongPointsApprox f δ i` via the involution
  -- `(x, t) ↦ (update x i t, x i)`.
  let τ : (Fin n → F) × F → (Fin n → F) × F := fun p => (update p.1 i p.2, p.1 i)
  have hτ : Function.Involutive τ := fun p => by
    ext j
    · by_cases hj : j = i
      · subst hj; simp [τ]
      · simp [τ, hj]
    · simp [τ]
  let g : (Fin n → F) × F → ℝ := fun p =>
    if p.1 ∈ wrongPointsApprox f δ i ∧ L i (update p.1 i 0) (p.1 i) ≠ f p.1 then 1 else 0
  have hsum_eq : ∑ p : (Fin n → F) × F, g p = ∑ p : (Fin n → F) × F, g (τ p) :=
    (Fintype.sum_equiv hτ.toPerm _ _ fun _ => rfl).symm
  have hLHS : ∑ p : (Fin n → F) × F, g p ≤ (Fintype.card F : ℝ) * (#D : ℝ) := by
    rw [Fintype.sum_prod_type]
    have hsplit (x : Fin n → F) : (∑ _t : F, g (x, _t)) =
        if x ∈ wrongPointsApprox f δ i ∩ D then (Fintype.card F : ℝ) else 0 := by
      by_cases hx : x ∈ wrongPointsApprox f δ i ∧ L i (update x i 0) (x i) ≠ f x
      · have hmem : x ∈ wrongPointsApprox f δ i ∩ D :=
          Finset.mem_inter.mpr ⟨hx.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2⟩⟩
        simp [g, hx, hmem]
      · have hnotmem : x ∉ wrongPointsApprox f δ i ∩ D := by
          intro hm
          rw [Finset.mem_inter] at hm
          exact hx ⟨hm.1, (Finset.mem_filter.mp hm.2).2⟩
        simp [g, hx, hnotmem]
    simp_rw [hsplit, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
      mul_comm _ (Fintype.card F : ℝ)]
    have hcard_le : (#(wrongPointsApprox f δ i ∩ D) : ℝ) ≤ (#D : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)
    exact mul_le_mul_of_nonneg_left hcard_le hq'.le
  have hRHS : (#(wrongPointsApprox f δ i) : ℝ) * (δ * Fintype.card F) ≤
      ∑ p : (Fin n → F) × F, g (τ p) := by
    rw [Fintype.sum_prod_type]
    have hτ_apply (x : Fin n → F) (t : F) :
        g (τ (x, t)) = if x ∈ wrongPointsApprox f δ i ∧
          lineRestrict f x i t ≠ L i (update x i 0) t then 1 else 0 := by
      by_cases hx : x ∈ wrongPointsApprox f δ i <;>
        by_cases heq : f (update x i t) = L i (update x i 0) t <;>
        simp [g, τ, mem_wrongPointsApprox_update, lineRestrict, hx, heq, ne_comm]
    simp_rw [hτ_apply]
    calc (#(wrongPointsApprox f δ i) : ℝ) * (δ * Fintype.card F) =
          ∑ _x ∈ wrongPointsApprox f δ i, (δ * Fintype.card F) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ wrongPointsApprox f δ i,
            ∑ t : F, if x ∈ wrongPointsApprox f δ i ∧
              lineRestrict f x i t ≠ L i (update x i 0) t then (1 : ℝ) else 0 := by
            refine Finset.sum_le_sum fun x hx => ?_
            have hnot : ¬ IsApproxAffine δ (lineRestrict f x i) := by
              simpa [wrongPointsApprox] using hx
            have hlt : δ * Fintype.card F <
                (#(Finset.univ.filter fun t => lineRestrict f x i t ≠ L i (update x i 0) t) :
                  ℝ) := by
              by_contra! hle
              exact hnot ⟨L i (update x i 0), hL i (update x i 0), hle⟩
            have heq : (∑ t : F, if x ∈ wrongPointsApprox f δ i ∧
                  lineRestrict f x i t ≠ L i (update x i 0) t then (1 : ℝ) else 0) =
                (#(Finset.univ.filter fun t => lineRestrict f x i t ≠ L i (update x i 0) t) :
                  ℝ) := by
              rw [Finset.natCast_card_filter]
              refine Finset.sum_congr rfl fun t _ => by simp [hx]
            linarith only [hlt, heq]
      _ ≤ ∑ x : Fin n → F, ∑ t : F, if x ∈ wrongPointsApprox f δ i ∧
              lineRestrict f x i t ≠ L i (update x i 0) t then (1 : ℝ) else 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
  have hmul :
      δ * (#(wrongPointsApprox f δ i) : ℝ) * Fintype.card F ≤ (#D : ℝ) * Fintype.card F := by
    linarith only [hsum_eq, hLHS, hRHS,
      show (#(wrongPointsApprox f δ i) : ℝ) * (δ * Fintype.card F) =
        δ * (#(wrongPointsApprox f δ i) : ℝ) * Fintype.card F by ring,
      show (Fintype.card F : ℝ) * (#D : ℝ) = (#D : ℝ) * Fintype.card F by ring]
  have hδW : δ * (#(wrongPointsApprox f δ i) : ℝ) ≤ (#D : ℝ) :=
    le_of_mul_le_mul_right hmul hq'
  exact lt_of_mul_lt_mul_left (show δ * (#(wrongPointsApprox f δ i) : ℝ) <
      δ * (ε * (Fintype.card F : ℝ) ^ n) by
    linarith only [hδW, hDi, mul_left_comm δ ε ((Fintype.card F : ℝ) ^ n)]) hδ0

end Cslib.Code
