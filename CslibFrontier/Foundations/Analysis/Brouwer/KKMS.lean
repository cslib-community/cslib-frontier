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
    rintro ⟨u, hu0, hu1⟩
    refine hnb ⟨fun S => if S ∈ Fset then u S else 0, fun S => ?_, ?_, fun i => ?_,
      fun S hS => ?_⟩
    · dsimp only
      split_ifs
      · exact hu0 S
      · rfl
    · dsimp only
      split_ifs with h
      · exact False.elim (Finset.notMem_empty _ (hne ∅ h).choose_spec)
      · rfl
    · have hi := congr_fun hu1 i
      simp only [Matrix.mulVec, dotProduct, M, ite_mul, one_mul, zero_mul] at hi
      rw [← hi, Finset.sum_filter]
      refine Finset.sum_congr rfl fun S _ => ?_
      by_cases hSF : S ∈ Fset <;> by_cases hiS : i ∈ S <;> simp [hSF, hiS]
    · dsimp only at hS
      by_contra hnot
      simp [hnot] at hS
  obtain ⟨y, hyM, hyb⟩ := (Matrix.not_exists_nonneg_mulVec_eq_iff M (fun _ => 1)).1 hno
  let y' : A → ℝ := fun i => -y i
  have hy'_pos : 0 < ∑ i, y' i := by
    simp only [dotProduct, mul_one] at hyb
    simp only [y', Finset.sum_neg_distrib, neg_pos]
    exact hyb
  have hy'_le : ∀ S ∈ Fset, ∑ i ∈ S, y' i ≤ 0 := by
    intro S hS
    have hcol := hyM S
    rw [Pi.zero_apply] at hcol
    simp only [Matrix.vecMul, dotProduct, M, hS, true_and, mul_ite, mul_one, mul_zero,
      ← Finset.sum_filter] at hcol
    have hsum : ∑ i ∈ S, y i = ∑ x with x ∈ S, y x := by
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext i; simp
    simp only [y', Finset.sum_neg_distrib, neg_nonpos]
    linarith
  let δ : ℝ := (∑ i, y' i) / (2 * (Fintype.card A : ℝ))
  have hcardA : (0 : ℝ) < Fintype.card A := Nat.cast_pos.2 Fintype.card_pos
  have hδ : 0 < δ := by positivity
  refine ⟨fun i => y' i - δ, ?_, fun S hS => ?_⟩
  · rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hmul : (Fintype.card A : ℝ) * δ = (∑ i, y' i) / 2 := by
      dsimp only [δ]
      field_simp [hcardA.ne']
    linarith
  · have hScard : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.one_le_card.2 (hne S hS)
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    nlinarith [hy'_le S hS]

private theorem isCompact_simplex {A : Type*} [Fintype A] :
    IsCompact {q : A → ℝ | (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1} := by
  refine (isCompact_Icc (a := (0 : A → ℝ)) (b := (1 : A → ℝ))).of_isClosed_subset
    ?_ fun q hq => ⟨hq.1, fun i => ?_⟩
  · have hclosed1 : IsClosed {q : A → ℝ | ∀ i, 0 ≤ q i} := by
      simpa only [Set.ofPred_forall] using
        isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have hclosed2 : IsClosed {q : A → ℝ | ∑ i, q i = 1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact hclosed1.inter hclosed2
  · calc q i ≤ ∑ j, q j := Finset.single_le_sum (fun j _ => hq.1 j) (Finset.mem_univ i)
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
  have hU_sub : ∀ x z : A → ℝ, z ∈ U x → ∀ S : Finset A, S.Nonempty → z ∈ F S → S ∈ active x := by
    intro x z hz S hSne hzS
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hSne, ?_⟩
    by_contra hxS
    exact (Set.mem_iInter.1 hz ⟨S, hSne, hxS⟩) hzS
  have hΔ_cov : Δ ⊆ ⋃ x : Δ, U x.1 := fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hmem_U x⟩
  obtain ⟨t, ht⟩ := isCompact_simplex.elim_finite_subcover (fun x : Δ => U x.1)
    (fun x => hU_open x.1) hΔ_cov
  have hsep : ∀ x : Δ, ∃ v : A → ℝ, 0 < ∑ i, v i ∧ ∀ S ∈ active x.1, ∑ i ∈ S, v i < 0 := by
    intro x
    refine exists_strictSep_of_not_balanced (active x.1)
      (fun S hS => (Finset.mem_filter.1 hS).2.1) fun ⟨w, hw0, hw_empty, hw_bal, hw_supp⟩ => ?_
    refine hnone ⟨x.1, x.2, w, hw0, hw_empty, hw_bal, fun S hSw => ?_⟩
    exact (Finset.mem_filter.1 (hw_supp S hSw)).2.2
  choose sep hsep_pos hsep_lt using hsep
  let wt : Δ → (A → ℝ) → ℝ := fun k z =>
    if _ : (U k.1)ᶜ.Nonempty then Metric.infDist z (U k.1)ᶜ else 1
  have hwt_cont : ∀ k : Δ, Continuous (wt k) := fun k => by
    dsimp only [wt]
    split_ifs
    · exact Metric.continuous_infDist_pt _
    · exact continuous_const
  have hwt_nonneg : ∀ k : Δ, ∀ z, 0 ≤ wt k z := fun k z => by
    dsimp only [wt]
    split_ifs
    · exact Metric.infDist_nonneg
    · exact zero_le_one
  have hwt_pos_iff : ∀ k : Δ, ∀ z, 0 < wt k z ↔ z ∈ U k.1 := fun k z => by
    dsimp only [wt]
    split_ifs with hne
    · simpa only [Set.notMem_compl_iff] using
        ((hU_open k.1).isClosed_compl.notMem_iff_infDist_pos hne).symm
    · have huniv : (U k.1)ᶜ = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
      have hmem : z ∈ U k.1 := by
        rw [← Set.notMem_compl_iff, huniv]
        exact Set.notMem_empty z
      exact ⟨fun _ => hmem, fun _ => zero_lt_one⟩
  let dir : (A → ℝ) → A → ℝ := fun z i => ∑ k ∈ t, wt k z * sep k i
  have hdir_cont : Continuous dir :=
    continuous_pi fun i => continuous_finsetSum t fun k _ => (hwt_cont k).mul continuous_const
  have hdir_pos : ∀ z ∈ Δ, 0 < ∑ i, dir z i := by
    intro z hz
    obtain ⟨_, hk_mem, hzk⟩ := Set.mem_iUnion₂.1 (ht hz)
    have hkt : ∃ k ∈ t, 0 < wt k z * ∑ i, sep k i :=
      ⟨_, hk_mem, mul_pos ((hwt_pos_iff _ z).2 hzk) (hsep_pos _)⟩
    have hsum_eq : ∑ i, dir z i = ∑ k ∈ t, wt k z * ∑ i, sep k i := by
      simp only [dir, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hsum_eq]
    exact Finset.sum_pos' (fun k _ => mul_nonneg (hwt_nonneg k z) (hsep_pos k).le) hkt
  have hdir_neg : ∀ z ∈ Δ, ∀ S : Finset A, S.Nonempty → z ∈ F S → ∑ i ∈ S, dir z i < 0 := by
    intro z hz S hSne hzS
    obtain ⟨k₀, hk₀, hzk₀⟩ := Set.mem_iUnion₂.1 (ht hz)
    have hkt : ∃ k ∈ t, wt k z * ∑ i ∈ S, sep k i < 0 := by
      refine ⟨k₀, hk₀, mul_neg_of_pos_of_neg ((hwt_pos_iff k₀ z).2 hzk₀) ?_⟩
      exact hsep_lt k₀ S (hU_sub k₀.1 z hzk₀ S hSne hzS)
    have hsum_eq : ∑ i ∈ S, dir z i = ∑ k ∈ t, wt k z * ∑ i ∈ S, sep k i := by
      simp only [dir, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hsum_eq]
    refine Finset.sum_neg' (fun k _ => ?_) hkt
    rcases (hwt_nonneg k z).lt_or_eq with hpos | h0
    · have hzUk := (hwt_pos_iff k z).1 hpos
      exact (mul_neg_of_pos_of_neg hpos (hsep_lt k S (hU_sub k.1 z hzUk S hSne hzS))).le
    · simp [← h0]
  let gain : (A → ℝ) → A → ℝ := fun z i => max 0 (dir z i - ∑ j, dir z j * z j)
  let denom : (A → ℝ) → ℝ := fun z => 1 + ∑ j, gain z j
  let step : (A → ℝ) → A → ℝ := fun z i => (z i + gain z i) / denom z
  have hgain_cont : ∀ i, Continuous fun z => gain z i := fun i =>
    continuous_const.max
      ((continuous_apply i).comp hdir_cont |>.sub
        (continuous_finsetSum Finset.univ fun j _ =>
          ((continuous_apply j).comp hdir_cont).mul (continuous_apply j)))
  have hdenom_pos : ∀ z, 0 < denom z := fun z => by
    have hg : 0 ≤ ∑ j, gain z j := Finset.sum_nonneg fun j _ => le_max_left _ _
    dsimp only [denom]
    linarith
  have hstep_cont : Continuous step :=
    continuous_pi fun i =>
      ((continuous_apply i).add (hgain_cont i)).div
        (continuous_const.add (continuous_finsetSum Finset.univ fun j _ => hgain_cont j))
        fun z => (hdenom_pos z).ne'
  have hstep_maps : MapsTo step Δ Δ := by
    intro z hz
    refine ⟨fun i => div_nonneg (add_nonneg (hz.1 i) (le_max_left _ _)) (hdenom_pos z).le, ?_⟩
    simp only [step, ← Finset.sum_div, Finset.sum_add_distrib, hz.2]
    exact div_self (hdenom_pos z).ne'
  let f : (Unit → A → ℝ) → (Unit → A → ℝ) := fun p _ => step (p ())
  have hf_maps : MapsTo f {p | ∀ _ : Unit, (∀ i, 0 ≤ p () i) ∧ ∑ i, p () i = 1}
      {p | ∀ _ : Unit, (∀ i, 0 ≤ p () i) ∧ ∑ i, p () i = 1} :=
    fun p hp _ => hstep_maps (hp ())
  have hf_cont : ContinuousOn f {p | ∀ _ : Unit, (∀ i, 0 ≤ p () i) ∧ ∑ i, p () i = 1} :=
    (continuous_pi fun _ => hstep_cont.comp (continuous_apply ())).continuousOn
  obtain ⟨p, hp, hfix⟩ := Cslib.Brouwer.exists_isFixedPt_pi_simplex hf_maps hf_cont
  set z : A → ℝ := p ()
  have hzΔ : z ∈ Δ := hp ()
  have hfz : step z = z := congrFun hfix ()
  let μ : ℝ := ∑ j, dir z j * z j
  have hgain_eq : ∀ i, gain z i = z i * ∑ j, gain z j := fun i => by
    have hi := congrFun hfz i
    dsimp only [step, denom] at hi
    rw [div_eq_iff (hdenom_pos z).ne'] at hi
    linarith
  have hgt_gain : ∀ i, 0 < gain z i → μ < dir z i := fun i hgi => by
    by_contra hle
    rw [not_lt] at hle
    have : gain z i = 0 := max_eq_left (sub_nonpos.2 hle)
    linarith
  have hsum_gain_zero : ∑ j, gain z j = 0 := by
    by_contra hne0
    have hpos_sum : 0 < ∑ j, gain z j :=
      lt_of_le_of_ne (Finset.sum_nonneg fun j _ => le_max_left _ _) (Ne.symm hne0)
    have hlt : ∑ i, z i * μ < ∑ i, z i * dir z i := by
      obtain ⟨i₀, hi₀⟩ : ∃ i₀, 0 < z i₀ := by
        by_contra h0
        push Not at h0
        have : ∑ i, z i ≤ 0 := Finset.sum_nonpos fun i _ => h0 i
        linarith [hzΔ.2]
      refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, Finset.mem_univ i₀, ?_⟩
      · rcases (hzΔ.1 i).lt_or_eq with hi | hi
        · exact (mul_lt_mul_of_pos_left
            (hgt_gain i (by rw [hgain_eq i]; exact mul_pos hi hpos_sum)) hi).le
        · simp [← hi]
      · exact mul_lt_mul_of_pos_left
          (hgt_gain i₀ (by rw [hgain_eq i₀]; exact mul_pos hi₀ hpos_sum)) hi₀
    rw [← Finset.sum_mul, hzΔ.2, one_mul] at hlt
    have hswap : ∑ i, z i * dir z i = μ := Finset.sum_congr rfl fun i _ => mul_comm _ _
    linarith
  have hdir_le : ∀ i, dir z i ≤ μ := fun i => by
    have hgi : gain z i = 0 := by rw [hgain_eq i, hsum_gain_zero, mul_zero]
    have hmax : max 0 (dir z i - μ) ≤ 0 := hgi.le
    linarith [le_max_right (0 : ℝ) (dir z i - μ)]
  have hμ_pos : 0 < μ := by
    have hsum_le : ∑ i, dir z i ≤ ∑ _i : A, μ := Finset.sum_le_sum fun i _ => hdir_le i
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum_le
    have hcard : (0 : ℝ) < Fintype.card A := Nat.cast_pos.2 Fintype.card_pos
    nlinarith [hdir_pos z hzΔ]
  have hdir_eq_of_pos : ∀ i, 0 < z i → dir z i = μ := fun i hi => by
    by_contra hne_i
    have hlt_i : dir z i < μ := lt_of_le_of_ne (hdir_le i) hne_i
    have hlt : ∑ j, z j * dir z j < ∑ j, z j * μ :=
      Finset.sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hdir_le j) (hzΔ.1 j))
        ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hlt_i hi⟩
    rw [← Finset.sum_mul, hzΔ.2, one_mul] at hlt
    have hswap : ∑ j, z j * dir z j = μ := Finset.sum_congr rfl fun j _ => mul_comm _ _
    linarith
  let T : Finset A := Finset.univ.filter fun i => 0 < z i
  have hT_ne : T.Nonempty := by
    by_contra hTe
    rw [Finset.not_nonempty_iff_eq_empty] at hTe
    have hz0 : ∀ i, z i = 0 := fun i => by
      have hi : i ∉ T := hTe ▸ Finset.notMem_empty i
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
      exact le_antisymm hi (hzΔ.1 i)
    have hsum0 : ∑ i, z i = 0 := Finset.sum_eq_zero fun i _ => hz0 i
    linarith [hzΔ.2]
  have hz_out : ∀ i ∉ T, z i = 0 := fun i hi => by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    exact le_antisymm hi (hzΔ.1 i)
  obtain ⟨S, hST, hSne, hzS⟩ := hcover T hT_ne z hzΔ.1 hzΔ.2 hz_out
  have hS_pos : 0 < ∑ i ∈ S, dir z i := by
    have hsum_eq : ∑ i ∈ S, dir z i = ∑ _i ∈ S, μ := by
      refine Finset.sum_congr rfl fun i hi => hdir_eq_of_pos i ?_
      have hiT := hST hi
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hiT
      exact hiT
    rw [hsum_eq, Finset.sum_const, nsmul_eq_mul]
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
  let G : Finset A → Set (A → ℝ) := fun S =>
    if h : ∃ i : A, S = {i} then F h.choose else ∅
  have hG_closed : ∀ S : Finset A, S.Nonempty → IsClosed (G S) := fun S _ => by
    dsimp only [G]
    split_ifs with h
    · exact hclosed h.choose
    · exact isClosed_empty
  have hG_cover : ∀ T : Finset A, T.Nonempty → ∀ q : A → ℝ,
      (∀ i, 0 ≤ q i) → (∑ i, q i = 1) → (∀ i ∉ T, q i = 0) →
        ∃ S ⊆ T, S.Nonempty ∧ q ∈ G S := by
    intro T hT q hq0 hq1 hqout
    obtain ⟨i, hiT, hqi⟩ := hcover T hT q hq0 hq1 hqout
    refine ⟨{i}, Finset.singleton_subset_iff.2 hiT, Finset.singleton_nonempty i, ?_⟩
    dsimp only [G]
    split_ifs with hex
    · have hchoose : hex.choose = i := Finset.singleton_injective hex.choose_spec.symm
      rwa [hchoose]
    · exact False.elim (hex ⟨i, rfl⟩)
  obtain ⟨q, hq, w, hw0, _, hw_bal, hqG⟩ := exists_balanced_inter_of_kkmCover G hG_closed hG_cover
  refine ⟨q, hq, fun i => ?_⟩
  have hwi : (∑ S with i ∈ S, w S) = 1 := hw_bal i
  have hzero : ∀ S : Finset A, S ≠ {i} → i ∈ S → w S = 0 := by
    intro S hne hiS
    by_contra hnw
    have hwpos : 0 < w S := lt_of_le_of_ne (hw0 S) (Ne.symm hnw)
    have hqS := hqG S hwpos
    dsimp only [G] at hqS
    split_ifs at hqS with hex
    · obtain ⟨j, rfl⟩ := hex
      have hij : i = j := Finset.mem_singleton.1 hiS
      exact hne (by rw [hij])
    · exact hqS
  have hsingle : w {i} = 1 := by
    rw [← hwi]
    rw [Finset.sum_eq_single {i}]
    · intro S hS hSne
      exact hzero S hSne (Finset.mem_filter.1 hS).2
    · intro hnot
      exfalso
      exact hnot (Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_singleton_self i⟩)
  have hqi := hqG {i} (by linarith)
  dsimp only [G] at hqi
  split_ifs at hqi with hex
  · have hchoose : hex.choose = i := Finset.singleton_injective hex.choose_spec.symm
    rwa [hchoose] at hqi
  · exact False.elim (hex ⟨i, rfl⟩)

end Cslib.Brouwer
