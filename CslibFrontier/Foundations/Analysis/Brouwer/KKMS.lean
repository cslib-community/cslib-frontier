/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Topology.Instances.Real.Lemmas
import CslibFrontier.Foundations.Analysis.Brouwer.Simplex
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Farkas
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# The KKM and KKMS covering theorems on the simplex

This module proves the **Knaster–Kuratowski–Mazurkiewicz (KKM) lemma**
([KnasterKuratowskiMazurkiewicz1929]) and Shapley's balanced generalization, the **KKMS theorem**
([Shapley1973]).

Given a finite family of closed sets `{F S}` indexed by coalitions `S : Finset A` that covers every
face `{q : A → ℝ | (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧ ∀ i ∉ T, q i = 0}` of the unit simplex by the
subfamily `{F S | S ⊆ T, S.Nonempty}`, `Cslib.Brouwer.exists_balanced_inter_of_kkmCover` exhibits a
simplex point `q` and nonnegative balanced weights `w : Finset A → ℝ` (`w ∅ = 0` and
`∑_{S : i ∈ S} w S = 1` for every `i`) such that `q ∈ F S` whenever `0 < w S`.

The proof proceeds by fixed-point and hyperplane-separation arguments: if no simplex point belongs
to a balanced intersection, Farkas' lemma (`Matrix.not_exists_nonneg_mulVec_eq_iff`) produces a
separating direction at each point, a distance-based continuous partition of unity on the compact
simplex pastes these directions into a continuous vector field, and Brouwer's fixed-point theorem
(`Cslib.Brouwer.exists_isFixedPt_pi_simplex`) applied to a Nash-style map yields a contradiction.
The classical KKM lemma (`Cslib.Brouwer.exists_mem_iInter_of_kkmCover`) follows immediately by
restricting the cover to singleton coalitions.

## Main results

* `Cslib.Brouwer.exists_balanced_inter_of_kkmCover`: **Shapley's KKMS theorem** ([Shapley1973]).
* `Cslib.Brouwer.exists_mem_iInter_of_kkmCover`: **the KKM lemma**
  ([KnasterKuratowskiMazurkiewicz1929]).

## References

* [KnasterKuratowskiMazurkiewicz1929]
* [Shapley1973]
-/

public section

namespace Cslib.Brouwer

open Finset Set Matrix

section Helpers

private theorem exists_strictSep_of_not_balanced {A : Type*} [Fintype A] [DecidableEq A]
    [Nonempty A] (Fset : Finset (Finset A)) (hne : ∀ S ∈ Fset, S.Nonempty)
    (hnb : ¬ ∃ w : Finset A → ℝ, (∀ S, 0 ≤ w S) ∧ w ∅ = 0 ∧
      (∀ i : A, (∑ S with i ∈ S, w S) = 1) ∧ ∀ S, 0 < w S → S ∈ Fset) :
    ∃ v : A → ℝ, 0 < ∑ i, v i ∧ ∀ S ∈ Fset, ∑ i ∈ S, v i < 0 := by
  let M : Matrix A (Finset A) ℝ := fun i S => if S ∈ Fset ∧ i ∈ S then 1 else 0
  have hno : ¬ ∃ u : Finset A → ℝ, 0 ≤ u ∧ M *ᵥ u = fun _ => 1 := by
    rintro ⟨u, hu0 : ∀ S, 0 ≤ u S, hu1⟩
    refine hnb ⟨fun S => if S ∈ Fset then u S else 0,
      fun S => by by_cases hS : S ∈ Fset <;> simp [hS, hu0 S],
      ite_eq_right fun h => Finset.notMem_empty _ (hne ∅ h).choose_spec, fun i => ?_,
      fun S hS => by_contra fun hnot => by simp [hnot] at hS⟩
    have hi := congr_fun hu1 i
    simp only [Matrix.mulVec, dotProduct, M, ite_mul, one_mul, zero_mul] at hi
    rw [← hi, Finset.sum_filter]
    exact Finset.sum_congr rfl fun S _ => by
      by_cases hSF : S ∈ Fset <;> by_cases hiS : i ∈ S <;> simp [hSF, hiS]
  obtain ⟨y, hyM, hyb⟩ := (Matrix.not_exists_nonneg_mulVec_eq_iff M (fun _ => 1)).1 hno
  let y' : A → ℝ := fun i => -y i
  have hy'_pos : 0 < ∑ i, y' i := by
    simpa only [dotProduct, mul_one, y', Finset.sum_neg_distrib, neg_pos] using hyb
  have hy'_le (S : Finset A) (hS : S ∈ Fset) : ∑ i ∈ S, y' i ≤ 0 := by
    simpa only [y', Finset.sum_neg_distrib, neg_nonpos, Pi.zero_apply, Matrix.vecMul, dotProduct,
      M, hS, true_and, mul_ite, mul_one, mul_zero, ← Finset.sum_filter,
      Finset.filter_univ_mem] using hyM S
  let δ : ℝ := (∑ i, y' i) / (2 * (Fintype.card A : ℝ))
  have hcardA : (0 : ℝ) < Fintype.card A := Nat.cast_pos.2 Fintype.card_pos
  have hδ : 0 < δ := by positivity
  refine ⟨fun i => y' i - δ, ?_, fun S hS => ?_⟩
  · rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (Fintype.card A : ℝ) * δ = (∑ i, y' i) / 2 := by dsimp only [δ]; field_simp [hcardA.ne']
    linarith
  · have hScard : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.one_le_card.2 (hne S hS)
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    nlinarith [hy'_le S hS]

private theorem isCompact_simplex {A : Type*} [Fintype A] :
    IsCompact {q : A → ℝ | (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1} := by
  refine (isCompact_Icc (a := (0 : A → ℝ)) (b := (1 : A → ℝ))).of_isClosed_subset
    ?_ fun q hq => ⟨hq.1, fun i => ?_⟩
  · exact isClosed_Ici.inter
      (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  · calc
      q i ≤ ∑ j, q j := Finset.single_le_sum (fun j _ => hq.1 j) (Finset.mem_univ i)
      _ = 1 := hq.2

end Helpers

/-- **The Knaster–Kuratowski–Mazurkiewicz–Shapley (KKMS) theorem** ([Shapley1973]): if
`F : Finset A → Set (A → ℝ)` consists of closed sets covering every face
`{q : A → ℝ | (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧ ∀ i ∉ T, q i = 0}` of the unit simplex by
`{F S | S ⊆ T, S.Nonempty}`, then there exist a simplex point `q` and nonnegative balanced weights
`w : Finset A → ℝ` (`w ∅ = 0` and `∑_{S : i ∈ S} w S = 1` for every `i`) such that `q ∈ F S`
whenever `0 < w S`. -/
theorem exists_balanced_inter_of_kkmCover {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (F : Finset A → Set (A → ℝ))
    (hclosed : ∀ S : Finset A, S.Nonempty → IsClosed (F S))
    (hcover : ∀ T : Finset A, T.Nonempty → ∀ q : A → ℝ,
      (∀ i, 0 ≤ q i) → (∑ i, q i = 1) → (∀ i ∉ T, q i = 0) →
        ∃ S ⊆ T, S.Nonempty ∧ q ∈ F S) :
    ∃ q : A → ℝ, ((∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) ∧
      ∃ w : Finset A → ℝ, (∀ S, 0 ≤ w S) ∧ w ∅ = 0 ∧
        (∀ i : A, (∑ S with i ∈ S, w S) = 1) ∧
        ∀ S : Finset A, 0 < w S → q ∈ F S := by
  classical
  by_contra hnone
  let Δ : Set (A → ℝ) := {q | (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1}
  let active : (A → ℝ) → Finset (Finset A) := fun x =>
    Finset.univ.filter fun S : Finset A => S.Nonempty ∧ x ∈ F S
  let U : (A → ℝ) → Set (A → ℝ) := fun x =>
    ⋂ S : {S : Finset A // S.Nonempty ∧ x ∉ F S}, (F S.1)ᶜ
  have hU_open : ∀ x : A → ℝ, IsOpen (U x) := fun x =>
    isOpen_iInter_of_finite fun S => (hclosed S.1 S.2.1).isOpen_compl
  have hmem_U : ∀ x : A → ℝ, x ∈ U x := fun x =>
    Set.mem_iInter.2 fun S hx => S.2.2 hx
  have hU_sub (x z : A → ℝ) (hz : z ∈ U x) (S : Finset A) (hSne : S.Nonempty)
      (hzS : z ∈ F S) : S ∈ active x :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hSne,
      by_contra fun hxS => (Set.mem_iInter.1 hz ⟨S, hSne, hxS⟩) hzS⟩
  have hΔ_cov : Δ ⊆ ⋃ x : Δ, U x.1 := fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hmem_U x⟩
  obtain ⟨t, ht⟩ := isCompact_simplex.elim_finite_subcover (fun x : Δ => U x.1)
    (fun x => hU_open x.1) hΔ_cov
  have hsep (x : Δ) : ∃ v : A → ℝ, 0 < ∑ i, v i ∧ ∀ S ∈ active x.1, ∑ i ∈ S, v i < 0 :=
    exists_strictSep_of_not_balanced (active x.1) (fun S hS => (Finset.mem_filter.1 hS).2.1)
      fun ⟨w, hw0, hw_empty, hw_bal, hw_supp⟩ =>
        hnone ⟨x.1, x.2, w, hw0, hw_empty, hw_bal,
          fun S hSw => (Finset.mem_filter.1 (hw_supp S hSw)).2.2⟩
  choose sep hsep_pos hsep_lt using hsep
  let wt : Δ → (A → ℝ) → ℝ := fun k z =>
    if (U k.1)ᶜ.Nonempty then Metric.infDist z (U k.1)ᶜ else 1
  have hwt_cont (k : Δ) : Continuous (wt k) := by
    dsimp only [wt]
    split_ifs
    exacts [Metric.continuous_infDist_pt _, continuous_const]
  have hwt_nonneg (k : Δ) (z : A → ℝ) : 0 ≤ wt k z := by
    by_cases h : (U k.1)ᶜ.Nonempty <;> simp [wt, h, Metric.infDist_nonneg]
  have hwt_pos_iff (k : Δ) (z : A → ℝ) : 0 < wt k z ↔ z ∈ U k.1 := by
    dsimp only [wt]
    split_ifs with hne
    · simpa only [Set.notMem_compl_iff] using
        ((hU_open k.1).isClosed_compl.notMem_iff_infDist_pos hne).symm
    · exact ⟨fun _ => Set.notMem_compl_iff.1 (Set.not_nonempty_iff_eq_empty.1 hne ▸
        Set.notMem_empty z), fun _ => zero_lt_one⟩
  let dir : (A → ℝ) → A → ℝ := fun z i => ∑ k ∈ t, wt k z * sep k i
  have hdir_cont : Continuous dir :=
    continuous_pi fun i => continuous_finsetSum t fun k _ => (hwt_cont k).mul continuous_const
  have hdir_sum (z : A → ℝ) (s : Finset A) :
      ∑ i ∈ s, dir z i = ∑ k ∈ t, wt k z * ∑ i ∈ s, sep k i := by
    simp only [dir, Finset.mul_sum]
    exact Finset.sum_comm
  have hdir_pos (z : A → ℝ) (hz : z ∈ Δ) : 0 < ∑ i, dir z i := by
    obtain ⟨k₀, hk₀, hzk₀⟩ := Set.mem_iUnion₂.1 (ht hz)
    rw [hdir_sum]
    exact Finset.sum_pos' (fun k _ => mul_nonneg (hwt_nonneg k z) (hsep_pos k).le)
      ⟨k₀, hk₀, mul_pos ((hwt_pos_iff k₀ z).2 hzk₀) (hsep_pos k₀)⟩
  have hdir_neg (z : A → ℝ) (hz : z ∈ Δ) (S : Finset A) (hSne : S.Nonempty) (hzS : z ∈ F S) :
      ∑ i ∈ S, dir z i < 0 := by
    obtain ⟨k₀, hk₀, hzk₀⟩ := Set.mem_iUnion₂.1 (ht hz)
    rw [hdir_sum]
    refine Finset.sum_neg' (fun k _ => ?_)
      ⟨k₀, hk₀, mul_neg_of_pos_of_neg ((hwt_pos_iff k₀ z).2 hzk₀)
        (hsep_lt k₀ S (hU_sub k₀.1 z hzk₀ S hSne hzS))⟩
    rcases (hwt_nonneg k z).lt_or_eq with hpos | h0
    · exact (mul_neg_of_pos_of_neg hpos
        (hsep_lt k S (hU_sub k.1 z ((hwt_pos_iff k z).1 hpos) S hSne hzS))).le
    · simp [← h0]
  let gain : (A → ℝ) → A → ℝ := fun z i => max 0 (dir z i - ∑ j, dir z j * z j)
  let denom : (A → ℝ) → ℝ := fun z => 1 + ∑ j, gain z j
  let step : (A → ℝ) → A → ℝ := fun z i => (z i + gain z i) / denom z
  have hgain_cont (i : A) : Continuous fun z => gain z i :=
    continuous_const.max (((continuous_apply i).comp hdir_cont).sub
      (continuous_finsetSum Finset.univ fun j _ =>
        ((continuous_apply j).comp hdir_cont).mul (continuous_apply j)))
  have hdenom_pos (z : A → ℝ) : 0 < denom z := by
    dsimp only [denom]; linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => le_max_left 0
      (dir z j - ∑ l, dir z l * z l)]
  have hstep_cont : Continuous step :=
    continuous_pi fun i => ((continuous_apply i).add (hgain_cont i)).div
      (continuous_const.add (continuous_finsetSum Finset.univ fun j _ => hgain_cont j))
      fun z => (hdenom_pos z).ne'
  have hstep_maps : MapsTo step Δ Δ := fun z hz =>
    ⟨fun i => div_nonneg (add_nonneg (hz.1 i) (le_max_left _ _)) (hdenom_pos z).le, by
      simp only [step, ← Finset.sum_div, Finset.sum_add_distrib, hz.2]
      exact div_self (hdenom_pos z).ne'⟩
  obtain ⟨p, hp, hfix⟩ := Cslib.Brouwer.exists_isFixedPt_pi_simplex
    (f := fun (p : Unit → A → ℝ) _ => step (p ())) (fun p hp _ => hstep_maps (hp ()))
    (continuous_pi fun _ => hstep_cont.comp (continuous_apply ())).continuousOn
  obtain ⟨z, hzΔ, hfz⟩ : ∃ z ∈ Δ, step z = z := ⟨p (), hp (), congrFun hfix ()⟩
  let μ : ℝ := ∑ j, dir z j * z j
  have hgain_eq (i : A) : gain z i = z i * ∑ j, gain z j := by
    have hi := congrFun hfz i
    dsimp only [step, denom] at hi
    rw [div_eq_iff (hdenom_pos z).ne'] at hi; linarith
  have hgt_gain (i : A) (hgi : 0 < gain z i) : μ < dir z i := by
    by_contra! hle
    linarith [max_eq_left (sub_nonpos.2 hle) ▸ hgi]
  have hswap_μ : ∑ i, z i * dir z i = μ := Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hex_pos : ∃ i₀, 0 < z i₀ := by
    by_contra! h0
    linarith [hzΔ.2, Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => h0 i]
  have hsum_gain_zero : ∑ j, gain z j = 0 := by
    by_contra hne0
    have hpos_sum : 0 < ∑ j, gain z j :=
      lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => le_max_left _ _) (Ne.symm hne0)
    have hpos_gain {j : A} (hj : 0 < z j) : 0 < gain z j := hgain_eq j ▸ mul_pos hj hpos_sum
    obtain ⟨i₀, hi₀⟩ := hex_pos
    have hlt : ∑ i, z i * μ < ∑ i, z i * dir z i :=
      Finset.sum_lt_sum (fun i _ => by
        rcases (hzΔ.1 i).lt_or_eq with hi | hi
        · exact (mul_lt_mul_of_pos_left (hgt_gain i (hpos_gain hi)) hi).le
        · simp [← hi])
        ⟨i₀, Finset.mem_univ i₀, mul_lt_mul_of_pos_left (hgt_gain i₀ (hpos_gain hi₀)) hi₀⟩
    rw [← Finset.sum_mul, hzΔ.2, one_mul, hswap_μ] at hlt
    exact lt_irrefl _ hlt
  have hdir_le (i : A) : dir z i ≤ μ := by
    have hgi : gain z i = 0 := by rw [hgain_eq i, hsum_gain_zero, mul_zero]
    linarith [le_max_right (0 : ℝ) (dir z i - μ), hgi]
  have hμ_pos : 0 < μ := by
    have hsum_le : ∑ i, dir z i ≤ Fintype.card A * μ := by
      simpa using (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hdir_le i)
    nlinarith [hdir_pos z hzΔ, (Nat.cast_pos.2 Fintype.card_pos : (0 : ℝ) < Fintype.card A)]
  have hdir_eq_of_pos (i : A) (hi : 0 < z i) : dir z i = μ := by
    by_contra hne_i
    have hlt : ∑ j, z j * dir z j < ∑ j, z j * μ :=
      Finset.sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hdir_le j) (hzΔ.1 j))
        ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (lt_of_le_of_ne (hdir_le i) hne_i) hi⟩
    rw [← Finset.sum_mul, hzΔ.2, one_mul, hswap_μ] at hlt
    exact lt_irrefl _ hlt
  let T : Finset A := Finset.univ.filter fun i => 0 < z i
  obtain ⟨i₀, hi₀⟩ := hex_pos
  obtain ⟨S, hST, hSne, hzS⟩ := hcover T ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi₀⟩⟩ z
    hzΔ.1 hzΔ.2 fun i hi => le_antisymm (by simpa [T] using hi) (hzΔ.1 i)
  have hS_pos : 0 < ∑ i ∈ S, dir z i := by
    rw [Finset.sum_congr rfl fun i hi => hdir_eq_of_pos i (Finset.mem_filter.1 (hST hi)).2,
      Finset.sum_const, nsmul_eq_mul]
    exact mul_pos (Nat.cast_pos.2 (Finset.card_pos.2 hSne)) hμ_pos
  exact lt_irrefl (0 : ℝ) (hS_pos.trans (hdir_neg z hzΔ S hSne hzS))

/-- **The Knaster–Kuratowski–Mazurkiewicz (KKM) lemma** ([KnasterKuratowskiMazurkiewicz1929]): if
`F : A → Set (A → ℝ)` is a family of closed sets covering every face
`{q : A → ℝ | (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧ ∀ i ∉ T, q i = 0}` by `{F i | i ∈ T}`, then
`⋂ i, F i` meets the unit simplex. -/
theorem exists_mem_iInter_of_kkmCover {A : Type*} [Fintype A] [Nonempty A]
    (F : A → Set (A → ℝ))
    (hclosed : ∀ i : A, IsClosed (F i))
    (hcover : ∀ T : Finset A, T.Nonempty → ∀ q : A → ℝ,
      (∀ i, 0 ≤ q i) → (∑ i, q i = 1) → (∀ i ∉ T, q i = 0) →
        ∃ i ∈ T, q ∈ F i) :
    ∃ q : A → ℝ, ((∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) ∧ ∀ i : A, q ∈ F i := by
  classical
  let G : Finset A → Set (A → ℝ) := fun S => ⋃ (i : A) (_ : S = {i}), F i
  have hG_single (i : A) : G {i} = F i := Set.ext fun _ => by simp [G]
  obtain ⟨q, hq, w, hw0, _, hw_bal, hqG⟩ := exists_balanced_inter_of_kkmCover G
    (fun _ _ => isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun _ => hclosed i)
    fun T hT q hq0 hq1 hqout => by
      obtain ⟨i, hiT, hqi⟩ := hcover T hT q hq0 hq1 hqout
      exact ⟨{i}, Finset.singleton_subset_iff.2 hiT, Finset.singleton_nonempty i,
        hG_single i ▸ hqi⟩
  refine ⟨q, hq, fun i => hG_single i ▸ hqG {i} ?_⟩
  suffices w {i} = 1 by linarith
  rw [← hw_bal i, Finset.sum_eq_single {i} (fun S hS hSne => ?_) (by simp)]
  refine le_antisymm (not_lt.1 fun hwS => ?_) (hw0 S)
  obtain ⟨j, rfl, -⟩ := Set.mem_iUnion₂.1 (hqG S hwS)
  exact hSne (congrArg singleton (Finset.mem_singleton.1 (Finset.mem_filter.1 hS).2).symm)

end Cslib.Brouwer
