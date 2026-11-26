/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.BipartiteMatching
public import CslibFrontier.Probability.OptimalStopping.MatroidSecretary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Transversal matroid secretary and truthful online USV mechanisms

Formalizes the **Price Sampling Algorithm** for bounded-left-degree transversal matroids and the
associated truthful online mechanism in the Unknown Single-Value (USV) unit-demand domain
([BabaioffImmorlicaKleinberg2007], Section 4, Theorems 4.1 and 4.2, p. 6).

A bipartite graph `G : L × R → Bool` induces a transversal matroid on left vertices `L` in which a
subset of left vertices is independent iff it can be matched to distinct right vertices `R`. Left
vertices `L` arrive in uniformly random order `σ : Fin (Fintype.card L) ≃ L`. After observing a
sample `S` of the first `s = ⌈|L|/2⌉` arrivals without selection, each right vertex `r` is assigned
price equal to the maximum weight of a sampled neighbor of `r` (`0` if none was sampled). Each
subsequent arrival `l` is matched greedily to a lowest-price unmatched neighbor `r` whose price
is strictly less than `w l`.

## Model notes and deviations

* **Well-behaved weights:** following [BabaioffImmorlicaKleinberg2007] (Section 2), Theorem 4.1
  assumes `w x = w y → w x = 0` for `x ≠ y`. Without this hypothesis, a `1`-item graph with two
  equal-weight neighbors `w l₁ = w l₂ > 0` fails the `4d`-approximation under strict `<` pricing.
* **No linear order needed on `R`:** `priceSamplingStep` selects any minimum-price candidate via
  `Finset.exists_min_image`, so no `[LinearOrder R]` instance is needed.
* **`2 ≤ Fintype.card L`:** when `|L| = 1`, `s = ⌈1/2⌉ = 1` leaves an empty post-sample stream.
* **Truthfulness (Theorem 4.2):** ex-post DSIC truthfulness and individual rationality hold for
  every arrival order `σ` without any left-degree bound `d`, assuming only nonnegative values for
  other agents (`∀ l' ≠ l, 0 ≤ (profile l').value`).

## Main definitions

* `Cslib.Probability.OptimalStopping.TransversalSecretary.itemPrice`,
  `.priceSamplingStep`, `.priceSamplingMatch`, `.priceSamplingPMF`,
  `.expectedPriceSamplingWeight`: the Price Sampling Algorithm and its expected weight.
* `Cslib.Probability.OptimalStopping.TransversalSecretary.USVType`,
  `.profileGraph`, `.profileWeight`, `.priceSamplingUSVAlloc`,
  `.priceSamplingUSVPayment`, `.priceSamplingUSVUtility`: Unknown Single-Value unit-demand agents
  and the Price Sampling online posted-price mechanism.

## Main results

* `Cslib.Probability.OptimalStopping.TransversalSecretary.priceSamplingMatch_isMatching`,
  `.sum_le_four_mul_degree_mul_expectedPriceSampling`: **Theorem 4.1** of
  [BabaioffImmorlicaKleinberg2007]: `priceSamplingMatch` always outputs a valid bipartite matching
  in `G` and achieves a `4d`-approximation on transversal matroids of left degree at most `d`.
* `Cslib.Probability.OptimalStopping.TransversalSecretary.priceSamplingUSV_ir`,
  `.priceSamplingUSV_truthful`, `.priceSamplingUSV_welfare`: **Theorem 4.2** of
  [BabaioffImmorlicaKleinberg2007]: ex-post individual rationality, ex-post dominant-strategy
  truthfulness (even without bounded degree), and `4d`-competitive social welfare under truthful
  reporting.

## References

* [M. Babaioff, N. Immorlica, and R. Kleinberg, *Matroids, Secretary Problems, and Online
  Mechanisms*][BabaioffImmorlicaKleinberg2007], Sections 2 and 4
-/

public section

namespace Cslib.Probability.OptimalStopping.TransversalSecretary

open Cslib.Algorithms.Lean.MaxFlow
open Cslib.Probability.OptimalStopping.MatroidSecretary
open Cslib.Probability.PMF
open scoped ENNReal

/-! ### Price Sampling Algorithm for bounded-degree transversal matroids -/

section PriceSampling

local instance instNonemptyPermTransversal (L : Type*) [Fintype L] :
    Nonempty (Fin (Fintype.card L) ≃ L) :=
  ⟨(Fintype.equivFin L).symm⟩

/-- Item price `w(l*_S(r))`: maximum weight of a sampled neighbor of `r`, or `0` if `r` has no
sampled neighbors. -/
@[expose] noncomputable def itemPrice {L R : Type*} (G : L × R → Bool) (w : L → ℝ)
    (S : Finset L) (r : R) : ℝ :=
  sampleMax w (S.filter fun l => G (l, r) = true)

theorem itemPrice_nonneg {L R : Type*} (G : L × R → Bool) (w : L → ℝ)
    {S : Finset L} (hw : ∀ l ∈ S, 0 ≤ w l) (r : R) :
    0 ≤ itemPrice G w S r := by
  unfold itemPrice sampleMax
  split_ifs with hne
  · obtain ⟨l, hl⟩ := hne
    exact (hw l (Finset.mem_filter.mp hl).1).trans (Finset.le_sup' w hl)
  · exact le_rfl

/-- Single online step of the Price Sampling Algorithm for left vertex `l`: collects all
unmatched neighbors of `l` with price strictly below `w l` and, if nonempty, matches `l` to a
minimum-price candidate. -/
@[expose] noncomputable def priceSamplingStep {L R : Type*} [Fintype R] [DecidableEq L]
    [DecidableEq R] (G : L × R → Bool) (w : L → ℝ) (p : R → ℝ)
    (M : Finset (L × R)) (l : L) : Finset (L × R) :=
  open scoped Classical in
  if h : (Finset.univ.filter fun r : R =>
      G (l, r) = true ∧ p r < w l ∧ r ∉ M.image Prod.snd).Nonempty then
    insert (l, Classical.choose ((Finset.univ.filter fun r : R =>
      G (l, r) = true ∧ p r < w l ∧ r ∉ M.image Prod.snd).exists_min_image p h)) M
  else M

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- **Price Sampling Algorithm** ([BabaioffImmorlicaKleinberg2007], Section 4): observes the first
`s = (|L| + 1) / 2` arriving left vertices to set item prices `itemPrice G w S`, then scans the
remaining arrival list with `priceSamplingStep`. -/
@[expose] noncomputable def priceSamplingMatch (G : L × R → Bool) (w : L → ℝ)
    (σ : Fin (Fintype.card L) ≃ L) : Finset (L × R) :=
  let s := (Fintype.card L + 1) / 2
  let p := itemPrice G w (sampleSet σ s)
  (postSampleList σ s).foldl (priceSamplingStep G w p) ∅

/-- Randomized distribution over matchings produced by `priceSamplingMatch` under uniform random
arrival order `σ`. -/
@[expose] noncomputable def priceSamplingPMF (G : L × R → Bool) (w : L → ℝ) :
    PMF (Finset (L × R)) :=
  (uniformOfFintype (Fin (Fintype.card L) ≃ L)).map (priceSamplingMatch G w)

/-- Expected weight of left vertices matched by `priceSamplingMatch` under a uniformly random
arrival order. -/
@[expose] noncomputable def expectedPriceSamplingWeight (G : L × R → Bool) (w : L → ℝ) : ℝ :=
  ∑ σ : Fin (Fintype.card L) ≃ L,
    ((uniformOfFintype (Fin (Fintype.card L) ≃ L) σ).toReal) *
      ∑ e ∈ priceSamplingMatch G w σ, w e.1

omit [Fintype L] in
private theorem mem_priceSamplingStep_of_notMem {G : L × R → Bool} {w : L → ℝ} {p : R → ℝ}
    {M0 : Finset (L × R)} {a : L} {e : L × R}
    (he : e ∈ priceSamplingStep G w p M0 a) (hnot : e ∉ M0) :
    e.1 = a ∧ G (a, e.2) = true ∧ p e.2 < w a ∧ e.2 ∉ M0.image Prod.snd ∧
      ∀ r, G (a, r) = true → p r < w a → r ∉ M0.image Prod.snd → p e.2 ≤ p r := by
  unfold priceSamplingStep at he
  split_ifs at he with hne
  · rcases Finset.mem_insert.mp he with rfl | hm0
    · obtain ⟨hmem, hmin⟩ := Classical.choose_spec (Finset.exists_min_image _ p hne)
      obtain ⟨-, hG, hp, hfree⟩ := Finset.mem_filter.mp hmem
      exact ⟨rfl, hG, hp, hfree, fun r h1 h2 h3 =>
        hmin r (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, h3⟩)⟩
    · exact absurd hm0 hnot
  · exact absurd he hnot

omit [Fintype L] in
private theorem subset_foldl_priceSamplingStep (G : L × R → Bool) (w : L → ℝ) (p : R → ℝ)
    (xs : List L) (M0 : Finset (L × R)) :
    M0 ⊆ xs.foldl (priceSamplingStep G w p) M0 := by
  induction xs generalizing M0 with
  | nil => exact Finset.Subset.rfl
  | cons a t ih =>
    refine Finset.Subset.trans ?_ (ih _)
    unfold priceSamplingStep
    split_ifs <;> simp [Finset.subset_insert]

omit [Fintype L] in
private theorem mem_foldl_priceSamplingStep_imp (G : L × R → Bool) (w : L → ℝ) (p : R → ℝ)
    (xs : List L) (M0 : Finset (L × R)) {e : L × R}
    (he : e ∈ xs.foldl (priceSamplingStep G w p) M0) :
    e ∈ M0 ∨ e.1 ∈ xs := by
  induction xs generalizing M0 with
  | nil => exact Or.inl he
  | cons a t ih =>
    rcases ih _ he with hstep | ht
    · by_cases hm0 : e ∈ M0
      · exact Or.inl hm0
      · exact Or.inr ((mem_priceSamplingStep_of_notMem hstep hm0).1 ▸ List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ ht)

omit [Fintype L] in
private theorem notMem_fst_priceSamplingStep (G : L × R → Bool) (w : L → ℝ) (p : R → ℝ)
    (M0 : Finset (L × R)) {a x : L} (hne : x ≠ a) (hx : x ∉ M0.image Prod.fst) :
    x ∉ (priceSamplingStep G w p M0 a).image Prod.fst := by
  intro hmem
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hmem
  exact hne (mem_priceSamplingStep_of_notMem he fun h => hx (Finset.mem_image_of_mem _ h)).1

omit [Fintype L] in
private theorem foldl_priceSamplingStep_isMatching (G : L × R → Bool) (w : L → ℝ) (p : R → ℝ)
    {xs : List L} (hnodup : xs.Nodup) {M0 : Finset (L × R)} (hM0 : IsMatching G M0)
    (hfresh : ∀ l ∈ xs, l ∉ M0.image Prod.fst) :
    IsMatching G (xs.foldl (priceSamplingStep G w p) M0) := by
  induction xs generalizing M0 with
  | nil => exact hM0
  | cons a t ih =>
    obtain ⟨ha_not_t, hnodup_t⟩ := List.nodup_cons.mp hnodup
    have ha_fresh : a ∉ M0.image Prod.fst := hfresh a (List.mem_cons_self ..)
    have hM1 : IsMatching G (priceSamplingStep G w p M0 a) := by
      unfold priceSamplingStep
      split_ifs with hne
      · obtain ⟨-, hG, -, hfree⟩ :=
          Finset.mem_filter.mp (Classical.choose_spec (Finset.exists_min_image _ p hne)).1
        refine ⟨fun e he => ?_, fun u v₁ v₂ h₁ h₂ => ?_, fun u₁ u₂ v h₁ h₂ => ?_⟩
        · exact (Finset.mem_insert.mp he).elim (fun h => h ▸ hG) (hM0.1 e)
        · rcases Finset.mem_insert.mp h₁ with h₁ | h₁ <;>
            rcases Finset.mem_insert.mp h₂ with h₂ | h₂
          · exact (Prod.ext_iff.mp h₁).2.trans (Prod.ext_iff.mp h₂).2.symm
          · exact absurd (Finset.mem_image.mpr ⟨_, h₂, (Prod.ext_iff.mp h₁).1⟩) ha_fresh
          · exact absurd (Finset.mem_image.mpr ⟨_, h₁, (Prod.ext_iff.mp h₂).1⟩) ha_fresh
          · exact hM0.2.1 u v₁ v₂ h₁ h₂
        · rcases Finset.mem_insert.mp h₁ with h₁ | h₁ <;>
            rcases Finset.mem_insert.mp h₂ with h₂ | h₂
          · exact (Prod.ext_iff.mp h₁).1.trans (Prod.ext_iff.mp h₂).1.symm
          · exact absurd (Finset.mem_image.mpr ⟨_, h₂, (Prod.ext_iff.mp h₁).2⟩) hfree
          · exact absurd (Finset.mem_image.mpr ⟨_, h₁, (Prod.ext_iff.mp h₂).2⟩) hfree
          · exact hM0.2.2 u₁ u₂ v h₁ h₂
      · exact hM0
    exact ih hnodup_t hM1 fun l hl =>
      notMem_fst_priceSamplingStep G w p M0 (fun h => ha_not_t (h ▸ hl))
        (hfresh l (List.mem_cons_of_mem _ hl))

/-- Every execution of `priceSamplingMatch` produces a valid matching in `G`. -/
theorem priceSamplingMatch_isMatching (G : L × R → Bool) (w : L → ℝ)
    (σ : Fin (Fintype.card L) ≃ L) :
    IsMatching G (priceSamplingMatch G w σ) :=
  foldl_priceSamplingStep_isMatching G w _ (postSampleList_nodup σ _)
    ⟨fun _ h => by simp at h, fun _ _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩
    fun _ _ => by simp

omit [Fintype L] in
private theorem exists_matched_of_uncontested_neighbor (G : L × R → Bool) (w : L → ℝ) (p : R → ℝ)
    (xs : List L) (M0 : Finset (L × R)) {l : L} {r : R}
    (hl : l ∈ xs) (hG : G (l, r) = true) (hplt : p r < w l)
    (hr_free : r ∉ M0.image Prod.snd)
    (hother : ∀ a ∈ xs, a ≠ l → ¬ (G (a, r) = true ∧ p r < w a)) :
    ∃ r' : R, (l, r') ∈ xs.foldl (priceSamplingStep G w p) M0 := by
  induction xs generalizing M0 with
  | nil => simp at hl
  | cons a t ih =>
    by_cases ha : a = l
    · subst ha
      have hcand : (Finset.univ.filter fun r' : R =>
          G (a, r') = true ∧ p r' < w a ∧ r' ∉ M0.image Prod.snd).Nonempty :=
        ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG, hplt, hr_free⟩⟩
      simp only [List.foldl_cons, priceSamplingStep, hcand, ↓reduceDIte]
      exact ⟨_, subset_foldl_priceSamplingStep G w p t _ (Finset.mem_insert_self ..)⟩
    · refine ih (priceSamplingStep G w p M0 a) ((List.mem_cons.mp hl).resolve_left (Ne.symm ha))
        (fun hmem => ?_) fun b hb => hother b (List.mem_cons_of_mem _ hb)
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hmem
      obtain ⟨-, hG', hp', -⟩ :=
        mem_priceSamplingStep_of_notMem he fun h => hr_free (Finset.mem_image_of_mem _ h)
      exact hother a (List.mem_cons_self ..) ha ⟨hG', hp'⟩

/-- **Theorem 4.1 (Transversal Matroid Price Sampling)** of
[BabaioffImmorlicaKleinberg2007] (Section 4, p. 6): for any bipartite graph `G : L × R → Bool` of
left degree at most `d` with `2 ≤ |L|` and well-behaved nonnegative weights `w : L → ℝ`
(`w x = w y → w x = 0` for `x ≠ y`), the expected weight matched by `priceSamplingMatch G w` is
at least `1 / (4 * d)` of the weight of any matching `M`. -/
theorem sum_le_four_mul_degree_mul_expectedPriceSampling
    (G : L × R → Bool) (w : L → ℝ)
    (hw : ∀ l, 0 ≤ w l)
    (hwb : ∀ x y, x ≠ y → w x = w y → w x = 0)
    {d : ℕ} (hd : ∀ l : L, (Finset.univ.filter fun r : R => G (l, r) = true).card ≤ d)
    (hn : 2 ≤ Fintype.card L)
    {M : Finset (L × R)} (hM : IsMatching G M) :
    ∑ e ∈ M, w e.1 ≤ 4 * (d : ℝ) * expectedPriceSamplingWeight G w := by
  classical
  have hL : Nonempty L := Fintype.card_pos_iff.mp (by omega)
  let Ract : Finset R := Finset.univ.filter fun r : R => ∃ l : L, G (l, r) = true
  let N : R → Finset L := fun r => Finset.univ.filter fun l : L => G (l, r) = true
  let h : R → L := fun r =>
    if hr : (N r).Nonempty then Classical.choose ((N r).exists_max_image w hr)
    else Classical.choice hL
  have hh_mem : ∀ r ∈ Ract, h r ∈ N r := fun r hr => by
    obtain ⟨l, hl⟩ := (Finset.mem_filter.mp hr).2
    have hne : (N r).Nonempty := ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩⟩
    simpa only [h, hne, ↓reduceDIte] using (Classical.choose_spec ((N r).exists_max_image w hne)).1
  have hh_max : ∀ r ∈ Ract, ∀ l ∈ N r, w l ≤ w (h r) := fun r _ l hl => by
    have hne : (N r).Nonempty := ⟨l, hl⟩
    simpa only [h, hne, ↓reduceDIte] using
      (Classical.choose_spec ((N r).exists_max_image w hne)).2 l hl
  let H : Finset L := Ract.image h
  -- Claim 1: `∑ e ∈ M, w e.1 ≤ d * ∑ l ∈ H, w l`.
  have hclaim1 : ∑ e ∈ M, w e.1 ≤ (d : ℝ) * ∑ l ∈ H, w l := by
    have hinj : Set.InjOn Prod.snd (M : Set (L × R)) := fun e₁ h₁ e₂ h₂ hsnd =>
      Prod.ext (hM.2.2 e₁.1 e₂.1 e₁.2 h₁ (hsnd ▸ h₂)) hsnd
    have hM_le_R : ∑ e ∈ M, w e.1 ≤ ∑ r ∈ Ract, w (h r) := by
      calc ∑ e ∈ M, w e.1
          ≤ ∑ e ∈ M, w (h e.2) := Finset.sum_le_sum fun ⟨l, r⟩ he =>
              hh_max r (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨l, hM.1 (l, r) he⟩⟩) l
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM.1 (l, r) he⟩)
        _ = ∑ r ∈ M.image Prod.snd, w (h r) :=
            (Finset.sum_image (f := fun r => w (h r)) (fun e₁ h₁ e₂ h₂ => hinj h₁ h₂)).symm
        _ ≤ ∑ r ∈ Ract, w (h r) := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.image_subset_iff.mpr fun ⟨l, r⟩ he =>
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, l, hM.1 (l, r) he⟩)
            fun r _ _ => hw (h r)
    have hfib : ∑ r ∈ Ract, w (h r) = ∑ l ∈ H, ∑ r ∈ Ract with h r = l, w (h r) :=
      (Finset.sum_fiberwise_of_maps_to (fun r hr => Finset.mem_image_of_mem h hr)
        (fun r => w (h r))).symm
    calc ∑ e ∈ M, w e.1
        ≤ ∑ r ∈ Ract, w (h r) := hM_le_R
      _ = ∑ l ∈ H, ∑ r ∈ Ract with h r = l, w (h r) := hfib
      _ ≤ ∑ l ∈ H, (d : ℝ) * w l := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [Finset.sum_congr rfl (fun r hr => congrArg w (Finset.mem_filter.mp hr).2),
            Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (hw l)
          refine Nat.cast_le.mpr ((Finset.card_le_card fun r hr => ?_).trans (hd l))
          obtain ⟨hr_act, rfl⟩ := Finset.mem_filter.mp hr
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp (hh_mem r hr_act)).2⟩
      _ = (d : ℝ) * ∑ l ∈ H, w l := by rw [Finset.mul_sum]
  -- Claim 2: `∑ l ∈ H, w l ≤ 4 * expectedPriceSamplingWeight G w`.
  have hclaim2 : ∑ l ∈ H, w l ≤ 4 * expectedPriceSamplingWeight G w := by
    let μ := uniformOfFintype (Fin (Fintype.card L) ≃ L)
    let s := (Fintype.card L + 1) / 2
    have hcard_perm : (Fintype.card (Fin (Fintype.card L) ≃ L) : ℝ) =
        ((Nat.factorial (Fintype.card L) : ℕ) : ℝ) := by
      rw [Fintype.card_congr (Equiv.equivCongr (Equiv.refl _) (Fintype.equivFin L)),
        Fintype.card_perm, Fintype.card_fin]
    have hl_bound : ∀ l ∈ H, w l ≤
        4 * ∑ σ : Fin (Fintype.card L) ≃ L, (μ σ).toReal *
          ∑ e ∈ priceSamplingMatch G w σ with e.1 = l, w e.1 := by
      intro l hl
      by_cases hwl : w l = 0
      · rw [hwl]
        refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun σ _ =>
          mul_nonneg ENNReal.toReal_nonneg (Finset.sum_nonneg fun e _ => hw e.1))
      have hwl_pos : 0 < w l := lt_of_le_of_ne (hw l) (Ne.symm hwl)
      obtain ⟨r, hr_act, hr_eq⟩ := Finset.mem_image.mp hl
      have hG_lr : G (l, r) = true := hr_eq ▸ (Finset.mem_filter.mp (hh_mem r hr_act)).2
      have hmax_r : ∀ y ∈ N r, w y ≤ w l := fun y hy => hr_eq ▸ hh_max r hr_act y hy
      -- Choose comparison vertex `lcmp ≠ l`: second-best neighbor of `r` if one exists, else any
      -- element distinct from `l`.
      have hex_cmp : ∃ lcmp : L, lcmp ≠ l ∧
          ∀ σ : Fin (Fintype.card L) ≃ L, lcmp ∈ sampleSet σ s → l ∉ sampleSet σ s →
            ∃ r' : R, (l, r') ∈ priceSamplingMatch G w σ := by
        by_cases hsecond : ((N r).erase l).Nonempty
        · obtain ⟨s2, hs2_mem, hs2_max⟩ := ((N r).erase l).exists_max_image w hsecond
          have hs2_ne : s2 ≠ l := (Finset.mem_erase.mp hs2_mem).1
          have hs2_N : s2 ∈ N r := Finset.erase_subset _ _ hs2_mem
          have hs2_lt : w s2 < w l := (hmax_r s2 hs2_N).lt_of_ne fun heq =>
            hwl_pos.ne' (heq ▸ hwb s2 l hs2_ne heq)
          refine ⟨s2, hs2_ne, fun σ hs2S hlNS => ?_⟩
          have hp_eq : itemPrice G w (sampleSet σ s) r = w s2 := by
            apply le_antisymm
            · refine sampleMax_le ⟨s2, Finset.mem_filter.mpr ⟨hs2S, (Finset.mem_filter.mp hs2_N).2⟩⟩
                fun y hy => ?_
              have hy' := Finset.mem_filter.mp hy
              have hy_ne : y ≠ l := fun h => hlNS (h ▸ hy'.1)
              exact hs2_max y (Finset.mem_erase.mpr
                ⟨hy_ne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'.2⟩⟩)
            · exact le_sampleMax_of_mem
                (Finset.mem_filter.mpr ⟨hs2S, (Finset.mem_filter.mp hs2_N).2⟩)
          refine exists_matched_of_uncontested_neighbor G w _ (postSampleList σ s) ∅
            ((mem_postSampleList_iff_notMem_sampleSet σ s l).mpr hlNS) hG_lr
            (hp_eq ▸ hs2_lt) (by simp) fun a _ ha_ne ⟨haG, ha_lt⟩ => ?_
          have ha_le : w a ≤ w s2 := hs2_max a
            (Finset.mem_erase.mpr ⟨ha_ne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, haG⟩⟩)
          linarith [hp_eq]
        · obtain ⟨l', hl'⟩ : (Finset.univ.erase l).Nonempty := Finset.card_pos.mp <| by
            rw [Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ]
            omega
          refine ⟨l', (Finset.mem_erase.mp hl').1, fun σ _ hlNS => ?_⟩
          have hempty : (sampleSet σ s).filter (fun y => G (y, r) = true) = ∅ :=
            Finset.filter_eq_empty_iff.mpr fun y hyS hyG =>
              if hyl : y = l then hlNS (hyl ▸ hyS)
              else hsecond ⟨y, Finset.mem_erase.mpr
                ⟨hyl, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyG⟩⟩⟩
          have hp_zero : itemPrice G w (sampleSet σ s) r = 0 := by
            simp [itemPrice, hempty, sampleMax]
          refine exists_matched_of_uncontested_neighbor G w _ (postSampleList σ s) ∅
            ((mem_postSampleList_iff_notMem_sampleSet σ s l).mpr hlNS) hG_lr
            (hp_zero ▸ hwl_pos) (by simp) fun a _ ha_ne ⟨haG, _⟩ => ?_
          exact hsecond ⟨a, Finset.mem_erase.mpr
            ⟨ha_ne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, haG⟩⟩⟩
      obtain ⟨lcmp, hcmp_ne, hmatched⟩ := hex_cmp
      have hprob := one_fourth_le_prob_split hcmp_ne hn
      have hprob_eq : ((μ.toOuterMeasure {σ | lcmp ∈ sampleSet σ s ∧ l ∉ sampleSet σ s}).toReal) =
          ∑ σ : Fin (Fintype.card L) ≃ L, (μ σ).toReal *
            if lcmp ∈ sampleSet σ s ∧ l ∉ sampleSet σ s then (1 : ℝ) else 0 := by
        calc ((μ.toOuterMeasure {σ | lcmp ∈ sampleSet σ s ∧ l ∉ sampleSet σ s}).toReal)
            = ((Finset.univ.filter fun σ : Fin (Fintype.card L) ≃ L =>
                lcmp ∈ sampleSet σ s ∧ l ∉ sampleSet σ s).card : ℝ) /
                ((Nat.factorial (Fintype.card L) : ℕ) : ℝ) := by
              rw [toOuterMeasure_uniformOfFintype_toReal, hcard_perm]
              rfl
          _ = ((Nat.factorial (Fintype.card L) : ℕ) : ℝ)⁻¹ * ∑ σ : Fin (Fintype.card L) ≃ L,
                if lcmp ∈ sampleSet σ s ∧ l ∉ sampleSet σ s then (1 : ℝ) else 0 := by
              rw [Finset.sum_boole, div_eq_inv_mul]
          _ = ∑ σ : Fin (Fintype.card L) ≃ L, (μ σ).toReal *
                if lcmp ∈ sampleSet σ s ∧ l ∉ sampleSet σ s then (1 : ℝ) else 0 := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun σ _ => by simp [μ, uniformOfFintype_apply, hcard_perm]
      have hw_mul := mul_le_mul_of_nonneg_right (hprob.trans_eq hprob_eq) hwl_pos.le
      rw [Finset.sum_mul] at hw_mul
      have hterm_le : ∑ σ : Fin (Fintype.card L) ≃ L,
          ((μ σ).toReal * if lcmp ∈ sampleSet σ s ∧ l ∉ sampleSet σ s then (1 : ℝ) else 0) * w l ≤
          ∑ σ : Fin (Fintype.card L) ≃ L, (μ σ).toReal *
            ∑ e ∈ priceSamplingMatch G w σ with e.1 = l, w e.1 := by
        refine Finset.sum_le_sum fun σ _ => ?_
        split_ifs with hs
        · obtain ⟨r', hr'⟩ := hmatched σ hs.1 hs.2
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (fun e _ => hw e.1)
              (Finset.mem_filter (p := fun e => e.1 = l).mpr ⟨hr', rfl⟩))
            ENNReal.toReal_nonneg
        · simpa only [mul_zero, zero_mul] using mul_nonneg ENNReal.toReal_nonneg
            (Finset.sum_nonneg fun e _ => hw e.1)
      linarith [hw_mul.trans hterm_le]
    calc ∑ l ∈ H, w l
        ≤ ∑ l ∈ H, 4 * ∑ σ : Fin (Fintype.card L) ≃ L, (μ σ).toReal *
            ∑ e ∈ priceSamplingMatch G w σ with e.1 = l, w e.1 := Finset.sum_le_sum hl_bound
      _ = 4 * ∑ σ : Fin (Fintype.card L) ≃ L, (μ σ).toReal *
            ∑ l ∈ H, ∑ e ∈ priceSamplingMatch G w σ with e.1 = l, w e.1 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          refine congrArg (4 * ·) (Finset.sum_congr rfl fun σ _ => ?_)
          rw [← Finset.mul_sum]
      _ ≤ 4 * ∑ σ : Fin (Fintype.card L) ≃ L, (μ σ).toReal *
            ∑ e ∈ priceSamplingMatch G w σ, w e.1 := by
          gcongr with σ
          rw [← Finset.sum_biUnion fun l₁ _ l₂ _ hne =>
            Finset.disjoint_filter.mpr fun _ _ h₁ h₂ => hne (h₁.symm.trans h₂)]
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.biUnion_subset.mpr fun _ _ => Finset.filter_subset _ _) fun e _ _ => hw e.1
      _ = 4 * expectedPriceSamplingWeight G w := rfl
  calc ∑ e ∈ M, w e.1 ≤ (d : ℝ) * ∑ l ∈ H, w l := hclaim1
    _ ≤ (d : ℝ) * (4 * expectedPriceSamplingWeight G w) :=
        mul_le_mul_of_nonneg_left hclaim2 (Nat.cast_nonneg d)
    _ = 4 * (d : ℝ) * expectedPriceSamplingWeight G w := by ring

end PriceSampling

/-! ### Truthful online mechanism in the Unknown Single-Value (USV) domain -/

section USVMechanism

/-- A buyer's private type in the Unknown Single-Value (USV) unit-demand domain
([BabaioffImmorlicaKleinberg2007], Sections 2 and 4): scalar value `value` for receiving any
desired item `r` with `desired r = true`, and value `0` for undesired items. -/
structure USVType (R : Type*) where
  /-- Buyer's scalar valuation for obtaining a desired item. -/
  value : ℝ
  /-- Indicator of desired items (`desired r = true` iff `r ∈ T_l`). -/
  desired : R → Bool

/-- Bipartite demand graph induced by a reported USV type profile. -/
@[expose] def profileGraph {L R : Type*} (profile : L → USVType R) : L × R → Bool :=
  fun e => (profile e.1).desired e.2

/-- Agent weight vector induced by a reported USV type profile. -/
@[expose] def profileWeight {L R : Type*} (profile : L → USVType R) : L → ℝ :=
  fun l => (profile l).value

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- Item allocated to agent `l` under a reported USV profile and arrival order `σ`. -/
@[expose] noncomputable def priceSamplingUSVAlloc (profile : L → USVType R)
    (σ : Fin (Fintype.card L) ≃ L) (l : L) : Option R :=
  open scoped Classical in
  if h : ∃ r : R, (l, r) ∈ priceSamplingMatch (profileGraph profile) (profileWeight profile) σ
  then some (Classical.choose h)
  else none

/-- Payment charged to agent `l` under the Price Sampling USV mechanism: `itemPrice` of the
allocated item, or `0` if unallocated. -/
@[expose] noncomputable def priceSamplingUSVPayment (profile : L → USVType R)
    (σ : Fin (Fintype.card L) ≃ L) (l : L) : ℝ :=
  match priceSamplingUSVAlloc profile σ l with
  | some r => itemPrice (profileGraph profile) (profileWeight profile)
      (sampleSet σ ((Fintype.card L + 1) / 2)) r
  | none => 0

/-- Utility of an agent with true type `trueType` receiving `alloc` and paying `payment`. -/
@[expose] def priceSamplingUSVUtility (trueType : USVType R) (alloc : Option R)
    (payment : ℝ) : ℝ :=
  (match alloc with
  | some r => if trueType.desired r = true then trueType.value else 0
  | none => 0) - payment

private theorem priceSamplingUSVAlloc_eq_some_iff (profile : L → USVType R)
    (σ : Fin (Fintype.card L) ≃ L) (l : L) (r : R) :
    priceSamplingUSVAlloc profile σ l = some r ↔
      (l, r) ∈ priceSamplingMatch (profileGraph profile) (profileWeight profile) σ := by
  classical
  have hm := priceSamplingMatch_isMatching (profileGraph profile) (profileWeight profile) σ
  unfold priceSamplingUSVAlloc
  split_ifs with h
  · exact ⟨fun heq => Option.some.inj heq ▸ Classical.choose_spec h,
      fun hmem => congrArg some (hm.2.1 l _ r (Classical.choose_spec h) hmem)⟩
  · exact ⟨fun heq => by simp at heq, fun hmem => absurd ⟨r, hmem⟩ h⟩

omit [Fintype L] in
private theorem mem_foldl_priceSamplingStep_cand (G : L × R → Bool) (w : L → ℝ) (p : R → ℝ)
    {xs : List L} (hnodup : xs.Nodup) {M0 : Finset (L × R)}
    (hfresh : ∀ x ∈ xs, x ∉ M0.image Prod.fst) {l : L} {r : R}
    (hmem : (l, r) ∈ xs.foldl (priceSamplingStep G w p) M0) (hnot : (l, r) ∉ M0) :
    G (l, r) = true ∧ p r < w l := by
  induction xs generalizing M0 with
  | nil => exact absurd hmem hnot
  | cons a t ih =>
    obtain ⟨ha_not_t, hnodup_t⟩ := List.nodup_cons.mp hnodup
    by_cases hmem1 : (l, r) ∈ priceSamplingStep G w p M0 a
    · obtain ⟨rfl, hG, hp, -⟩ := mem_priceSamplingStep_of_notMem hmem1 hnot
      exact ⟨hG, hp⟩
    · exact ih hnodup_t (fun x hx =>
        notMem_fst_priceSamplingStep G w p M0 (fun h => ha_not_t (by rw [← h]; exact hx))
          (hfresh x (List.mem_cons_of_mem _ hx))) hmem hmem1

omit [Fintype L] in
private theorem foldl_priceSamplingStep_split_agent
    (G₁ G₂ : L × R → Bool) (w₁ w₂ : L → ℝ) (p : R → ℝ) (xs : List L) (M0 : Finset (L × R))
    {l : L} (hnodup : xs.Nodup) (hl : l ∈ xs)
    (hfresh : ∀ x ∈ xs, x ∉ M0.image Prod.fst)
    (hG : ∀ a ≠ l, ∀ r, G₁ (a, r) = G₂ (a, r))
    (hw : ∀ a ≠ l, w₁ a = w₂ a) :
    ∃ Mbefore : Finset (L × R),
      l ∉ Mbefore.image Prod.fst ∧
      (∀ r : R, (l, r) ∈ xs.foldl (priceSamplingStep G₁ w₁ p) M0 ↔
        (l, r) ∈ priceSamplingStep G₁ w₁ p Mbefore l) ∧
      (∀ r : R, (l, r) ∈ xs.foldl (priceSamplingStep G₂ w₂ p) M0 ↔
        (l, r) ∈ priceSamplingStep G₂ w₂ p Mbefore l) := by
  induction xs generalizing M0 with
  | nil => simp at hl
  | cons a t ih =>
    obtain ⟨ha_not_t, hnodup_t⟩ := List.nodup_cons.mp hnodup
    by_cases ha : a = l
    · subst ha
      have hiff (G' w') (r : R) :
          (a, r) ∈ t.foldl (priceSamplingStep G' w' p) (priceSamplingStep G' w' p M0 a) ↔
            (a, r) ∈ priceSamplingStep G' w' p M0 a :=
        ⟨fun h => (mem_foldl_priceSamplingStep_imp G' w' p t _ h).resolve_right ha_not_t,
          fun h => subset_foldl_priceSamplingStep G' w' p t _ h⟩
      exact ⟨M0, hfresh a (List.mem_cons_self ..), hiff G₁ w₁, hiff G₂ w₂⟩
    · have hstep : priceSamplingStep G₁ w₁ p M0 a = priceSamplingStep G₂ w₂ p M0 a := by
        simp only [priceSamplingStep, hG a ha, hw a ha]
      rw [List.foldl_cons, List.foldl_cons, hstep]
      exact ih (priceSamplingStep G₂ w₂ p M0 a) hnodup_t
        ((List.mem_cons.mp hl).resolve_left (Ne.symm ha)) fun x hx =>
          notMem_fst_priceSamplingStep G₂ w₂ p M0 (fun h => ha_not_t (by rw [← h]; exact hx))
            (hfresh x (List.mem_cons_of_mem _ hx))

private theorem alloc_none_of_notMem_post (profile : L → USVType R)
    (σ : Fin (Fintype.card L) ≃ L) {l : L}
    (hl : l ∉ postSampleList σ ((Fintype.card L + 1) / 2)) :
    priceSamplingUSVAlloc profile σ l = none := by
  cases h : priceSamplingUSVAlloc profile σ l with
  | none => rfl
  | some r =>
    exact absurd ((mem_foldl_priceSamplingStep_imp (profileGraph profile) (profileWeight profile) _
      (postSampleList σ _) ∅ ((priceSamplingUSVAlloc_eq_some_iff profile σ l r).mp h)).resolve_left
      (Finset.notMem_empty _)) hl

/-- **Ex-post individual rationality** ([BabaioffImmorlicaKleinberg2007], Theorem 4.2): under
truthful reporting, every agent's utility is nonnegative for every arrival order `σ` (regardless of
left degree `d` or other agents' reports). -/
theorem priceSamplingUSV_ir (profile : L → USVType R) (σ : Fin (Fintype.card L) ≃ L) (l : L) :
    0 ≤ priceSamplingUSVUtility (profile l)
      (priceSamplingUSVAlloc profile σ l) (priceSamplingUSVPayment profile σ l) := by
  unfold priceSamplingUSVUtility priceSamplingUSVPayment
  cases h : priceSamplingUSVAlloc profile σ l with
  | none => norm_num
  | some r =>
    obtain ⟨hdes, hlt⟩ := mem_foldl_priceSamplingStep_cand (profileGraph profile)
      (profileWeight profile) _ (postSampleList_nodup σ _) (fun _ _ => by simp)
      ((priceSamplingUSVAlloc_eq_some_iff profile σ l r).mp h) (by simp)
    dsimp only [profileGraph, profileWeight] at hdes hlt
    simp only [hdes, ↓reduceIte]
    linarith

/-- **Ex-post dominant-strategy truthfulness (Theorem 4.2)** of [BabaioffImmorlicaKleinberg2007]
(Section 4, p. 6): in the Unknown Single-Value (USV) unit-demand domain—even without any bound
`d` on desired set sizes—truthfully reporting both `value` and `desired` maximizes agent `l`'s
utility for every arrival order `σ` and every nonnegative report profile of the other agents. -/
theorem priceSamplingUSV_truthful (profile : L → USVType R) (σ : Fin (Fintype.card L) ≃ L)
    (l : L) (trueType misreport : USVType R)
    (hothers : ∀ l' ≠ l, 0 ≤ (profile l').value) :
    priceSamplingUSVUtility trueType
        (priceSamplingUSVAlloc (Function.update profile l misreport) σ l)
        (priceSamplingUSVPayment (Function.update profile l misreport) σ l) ≤
      priceSamplingUSVUtility trueType
        (priceSamplingUSVAlloc (Function.update profile l trueType) σ l)
        (priceSamplingUSVPayment (Function.update profile l trueType) σ l) := by
  classical
  set s := (Fintype.card L + 1) / 2
  set profT := Function.update profile l trueType
  set profM := Function.update profile l misreport
  have hutil_T_nonneg : 0 ≤ priceSamplingUSVUtility trueType
      (priceSamplingUSVAlloc profT σ l) (priceSamplingUSVPayment profT σ l) := by
    simpa only [profT, Function.update_self] using priceSamplingUSV_ir profT σ l
  by_cases hl_post : l ∈ postSampleList σ s
  · have hl_not_S : l ∉ sampleSet σ s := (mem_postSampleList_iff_notMem_sampleSet σ s l).mp hl_post
    have hp_eq : itemPrice (profileGraph profT) (profileWeight profT) (sampleSet σ s) =
        itemPrice (profileGraph profM) (profileWeight profM) (sampleSet σ s) := by
      funext r
      unfold itemPrice sampleMax
      rw [Finset.filter_congr (q := fun a => profileGraph profM (a, r) = true) fun a haS => by
        simp only [profileGraph, profT, profM,
          Function.update_of_ne fun h : a = l => hl_not_S (h ▸ haS)]]
      split_ifs with hne
      · exact Finset.sup'_congr hne rfl fun a ha => by
          simp only [profileWeight, profT, profM,
            Function.update_of_ne fun h : a = l => hl_not_S (h ▸ (Finset.mem_filter.mp ha).1)]
      · rfl
    set p := itemPrice (profileGraph profT) (profileWeight profT) (sampleSet σ s)
    have hp_nonneg : ∀ r : R, 0 ≤ p r :=
      itemPrice_nonneg (profileGraph profT) (profileWeight profT) fun a haS => by
        have hne : a ≠ l := fun h => hl_not_S (h ▸ haS)
        simpa only [profileWeight, profT, Function.update_of_ne hne] using hothers a hne
    obtain ⟨Mbefore, hl_fresh, hiffT, hiffM⟩ :=
      foldl_priceSamplingStep_split_agent (profileGraph profT) (profileGraph profM)
        (profileWeight profT) (profileWeight profM) p (postSampleList σ s) ∅
        (postSampleList_nodup σ s) hl_post (fun _ _ => Finset.notMem_empty _)
        (fun a ha r => by simp only [profileGraph, profT, profM, Function.update_of_ne ha])
        (fun a ha => by simp only [profileWeight, profT, profM, Function.update_of_ne ha])
    have hnot_Mb : ∀ r, (l, r) ∉ Mbefore := fun r h => hl_fresh (Finset.mem_image_of_mem _ h)
    cases hallocM : priceSamplingUSVAlloc profM σ l with
    | none =>
      calc priceSamplingUSVUtility trueType none (priceSamplingUSVPayment profM σ l)
          = 0 := by simp [priceSamplingUSVUtility, priceSamplingUSVPayment, hallocM]
        _ ≤ priceSamplingUSVUtility trueType (priceSamplingUSVAlloc profT σ l)
            (priceSamplingUSVPayment profT σ l) := hutil_T_nonneg
    | some r' =>
      have hstepM : (l, r') ∈ priceSamplingStep (profileGraph profM) (profileWeight profM) p
          Mbefore l := (hiffM r').mp <| by
        simpa only [priceSamplingMatch, s, p, hp_eq] using
          (priceSamplingUSVAlloc_eq_some_iff profM σ l r').mp hallocM
      have hr'_snd : r' ∉ Mbefore.image Prod.snd :=
        (mem_priceSamplingStep_of_notMem hstepM (hnot_Mb r')).2.2.2.1
      have hpayM : priceSamplingUSVPayment profM σ l = p r' := by
        rw [priceSamplingUSVPayment, hallocM, ← hp_eq]
      conv_lhs => rw [priceSamplingUSVUtility, hpayM]
      by_cases hdes : trueType.desired r' = true
      · simp only [hdes, ↓reduceIte]
        by_cases hlt : p r' < trueType.value
        · have hdesT : profileGraph profT (l, r') = true := by simp [profileGraph, profT, hdes]
          have hltT : p r' < profileWeight profT l := by simp [profileWeight, profT, hlt]
          have hcandT : (Finset.univ.filter fun r : R =>
              profileGraph profT (l, r) = true ∧ p r < profileWeight profT l ∧
                r ∉ Mbefore.image Prod.snd).Nonempty :=
            ⟨r', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdesT, hltT, hr'_snd⟩⟩
          set r₀ := Classical.choose (Finset.exists_min_image _ p hcandT)
          have hmT_step : (l, r₀) ∈
              priceSamplingStep (profileGraph profT) (profileWeight profT) p Mbefore l := by
            rw [priceSamplingStep, dite_eq_left hcandT]
            exact Finset.mem_insert_self ..
          obtain ⟨-, hG₀, -, -, hmin₀⟩ := mem_priceSamplingStep_of_notMem hmT_step (hnot_Mb r₀)
          have hallocT : priceSamplingUSVAlloc profT σ l = some r₀ :=
            (priceSamplingUSVAlloc_eq_some_iff profT σ l r₀).mpr ((hiffT r₀).mpr hmT_step)
          simp only [profileGraph, profT, Function.update_self] at hG₀
          simp only [priceSamplingUSVUtility, priceSamplingUSVPayment, hallocT, hG₀, ↓reduceIte]
          linarith [hmin₀ r' hdesT hltT hr'_snd]
        · linarith
      · simp only [hdes, Bool.false_eq_true, ↓reduceIte, zero_sub]
        linarith [hp_nonneg r']
  · simp only [priceSamplingUSVUtility, priceSamplingUSVPayment,
      alloc_none_of_notMem_post profT σ hl_post, alloc_none_of_notMem_post profM σ hl_post,
      sub_zero, le_rfl]

/-- **Social welfare guarantee of the USV mechanism** ([BabaioffImmorlicaKleinberg2007],
Theorem 4.2): when agents report truthfully, have well-behaved nonnegative valuations, and each
agent desires at most `d` items with `2 ≤ |L|`, the expected social welfare is a `4d`-approximation
to the maximum weight matching. -/
theorem priceSamplingUSV_welfare (profile : L → USVType R)
    (hw : ∀ l, 0 ≤ (profile l).value)
    (hwb : ∀ x y, x ≠ y → (profile x).value = (profile y).value → (profile x).value = 0)
    {d : ℕ} (hd : ∀ l : L, (Finset.univ.filter fun r : R => (profile l).desired r = true).card ≤ d)
    (hn : 2 ≤ Fintype.card L)
    {M : Finset (L × R)} (hM : IsMatching (profileGraph profile) M) :
    ∑ e ∈ M, (profile e.1).value ≤
      4 * (d : ℝ) * expectedPriceSamplingWeight (profileGraph profile) (profileWeight profile) :=
  sum_le_four_mul_degree_mul_expectedPriceSampling (profileGraph profile) (profileWeight profile)
    hw hwb hd hn hM

end USVMechanism

end Cslib.Probability.OptimalStopping.TransversalSecretary

