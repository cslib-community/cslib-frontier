/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Unique
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.Internal
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Generic Line-to-Affine Correlated-Agreement Lift (Sections 6.3 and 7.3)

Formalizes Lemma 6.3 and the Section 6.3 / 7.3 line-to-affine correlated-agreement reduction of
[BenSassonCarmonIshaiKoppartySaraf2020], passing from a finite `L`-element divergence cover of
`reedSolomon α k` to shared `W`-weighted agreement over every affine subspace generator `u j`.

## Main results

* `Cslib.Code.exists_weighted_correlatedAgreement_affine_of_divergence`: generic weighted affine
  lift from a finite candidate-codeword list via linear-subspace covering.
* `Cslib.Code.exists_weighted_correlatedAgreement_affine_of_line`: line-to-affine correlated
  agreement lift under density strictly exceeding `B_line / |F|`.
-/

public section

namespace Cslib.Code

open scoped BigOperators
open Finset Polynomial

/-- Private helper: any proper `F`-submodule of `Fin ℓ → F` has cardinality at most
`|F| ^ (ℓ - 1)`. -/
private theorem card_submodule_le_pow_pred_of_ne_top
    {F : Type*} [Field F] [Fintype F] {ℓ : ℕ}
    {K : Submodule F (Fin ℓ → F)} [Fintype K] (hK : K ≠ ⊤) :
    Fintype.card K ≤ (Fintype.card F) ^ (ℓ - 1) := by
  have hlt : Module.finrank F K < Module.finrank F (Fin ℓ → F) := Submodule.finrank_lt hK
  rw [Module.finrank_fin_fun] at hlt
  have hle : Module.finrank F K ≤ ℓ - 1 := by omega
  rw [Module.card_eq_pow_finrank (K := F)]
  exact Nat.pow_le_pow_right Fintype.card_pos hle

private theorem hyperplane_shift_filter_card {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {m : ℕ} {d : Fin m → F} {j₀ : Fin m} (hj₀ : d j₀ ≠ 0) (T : Finset (Fin m → F)) :
    ∑ z ∈ Finset.univ.filter fun z : Fin m → F => z j₀ = 0,
      ((Finset.univ : Finset F).filter fun t => z + t • d ∈ T).card = T.card := by
  let H := Finset.univ.filter fun z : Fin m → F => z j₀ = 0
  have hprod : ((H ×ˢ (Finset.univ : Finset F)).filter fun p => p.1 + p.2 • d ∈ T).card =
      T.card :=
    Finset.card_bij (fun p _ => p.1 + p.2 • d) (fun _ hp => (mem_filter.1 hp).2)
      (fun p₁ hp₁ p₂ hp₂ heq => by
        have h1 : p₁.1 j₀ = 0 := (mem_filter.1 (mem_product.1 (mem_filter.1 hp₁).1).1).2
        have h2 : p₂.1 j₀ = 0 := (mem_filter.1 (mem_product.1 (mem_filter.1 hp₂).1).1).2
        have hj := congrFun heq j₀
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h2, zero_add] at hj
        have ht : p₁.2 = p₂.2 := mul_right_cancel₀ hj₀ hj
        exact Prod.ext (add_right_cancel (ht ▸ heq)) ht)
      fun y hyT =>
        let t := y j₀ * (d j₀)⁻¹
        have hzH : y - t • d ∈ H := mem_filter.2 ⟨mem_univ _, by
          simp only [t, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_assoc,
            inv_mul_cancel₀ hj₀, mul_one, sub_self]⟩
        ⟨(y - t • d, t), mem_filter.2 ⟨mem_product.2 ⟨hzH, mem_univ t⟩,
          by simpa only [sub_add_cancel] using hyT⟩, sub_add_cancel y _⟩
  rw [← hprod, Finset.card_filter, Finset.sum_product]
  exact Finset.sum_congr rfl fun z _ => by rw [Finset.card_filter]

/-- Private helper (parameter-space [BenSassonCarmonIshaiKoppartySaraf2020, Lemma 6.3], printed
pp. 29–30 of the accepted JACM 2023 manuscript): if `B_line * |F| ^ m < |F| * #T` affine parameters
`z ∈ T` have `W`-weighted agreement at least `B_W` with `C`, then every direction word
`∑ j, d j • u j` in the associated linear span also has `W`-weighted agreement at least `B_W` with
`C`. -/
private theorem all_close_dir_of_line_correlatedAgreement
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {C : Submodule F (ι → F)} {W : ι → ℕ} {B_W B_line m : ℕ}
    (hline : ∀ (a b : ι → F) (S : Finset F),
      B_line < S.card →
      (∀ t ∈ S, ∃ c ∈ C, B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => (a + t • b) i = c i), W i) →
      ∃ D' : Finset ι, B_W ≤ ∑ i ∈ D', W i ∧
        ∃ w₀ ∈ C, ∃ w₁ ∈ C, ∀ i ∈ D', a i = w₀ i ∧ b i = w₁ i)
    (u₀ : ι → F) (u : Fin m → (ι → F))
    (T : Finset (Fin m → F))
    (hT : B_line * (Fintype.card F) ^ m < Fintype.card F * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ C,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + ∑ j : Fin m, z j • u j) i = c i), W i) :
    ∀ d : Fin m → F, ∃ c ∈ C,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => (∑ j : Fin m, d j • u j) i = c i), W i := by
  classical
  obtain ⟨z_ne, hz_ne⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.mul_zero] at hT; exact Nat.not_lt_zero _ hT)
  have hBW_le_tot : B_W ≤ ∑ i : ι, W i :=
    let ⟨_, _, hge⟩ := hclose z_ne hz_ne
    hge.trans (Finset.sum_le_sum_of_subset fun _ _ => mem_univ _)
  intro d
  by_cases hd0 : ∀ j : Fin m, d j = 0
  · refine ⟨0, C.zero_mem, ?_⟩
    rw [show (∑ j : Fin m, d j • u j) = 0 from Finset.sum_eq_zero fun j _ => by
      rw [hd0 j, zero_smul]]
    simpa only [Pi.zero_apply, eq_self, filter_true_of_mem (fun _ _ => trivial)] using hBW_le_tot
  · push Not at hd0; obtain ⟨j₀, hj₀⟩ := hd0
    have hm_pos : 1 ≤ m := Fin.pos j₀
    have hT_gt : B_line * (Fintype.card F) ^ (m - 1) < T.card := Nat.lt_of_mul_lt_mul_left <| by
      calc Fintype.card F * (B_line * (Fintype.card F) ^ (m - 1))
          = B_line * (Fintype.card F) ^ m := by
              conv_rhs => rw [← Nat.sub_add_cancel hm_pos, pow_succ]
              ring
        _ < Fintype.card F * T.card := hT
    let H := Finset.univ.filter fun z : Fin m → F => z j₀ = 0
    have hsum_lt : (∑ _z ∈ H, B_line) <
        ∑ z ∈ H, ((Finset.univ : Finset F).filter fun t => z + t • d ∈ T).card := by
      rw [hyperplane_shift_filter_card hj₀ T, Finset.sum_const, smul_eq_mul,
        card_filter_coord_eq_zero j₀, Nat.mul_comm]
      exact hT_gt
    obtain ⟨z, _, hz_gt⟩ := Finset.exists_lt_of_sum_lt hsum_lt
    obtain ⟨D', hD'_ge, _, _, w₁, hw₁C, hag⟩ :=
      hline (u₀ + ∑ j : Fin m, z j • u j) (∑ j : Fin m, d j • u j)
        ((Finset.univ : Finset F).filter fun t => z + t • d ∈ T) hz_gt fun t ht => by
          have hrew : (u₀ + ∑ j : Fin m, z j • u j) + t • (∑ j : Fin m, d j • u j) =
              u₀ + ∑ j : Fin m, (z + t • d) j • u j := by
            funext i
            simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_mul,
              Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, add_assoc]
          exact hrew ▸ hclose (z + t • d) (mem_filter.1 ht).2
    exact ⟨w₁, hw₁C, hD'_ge.trans (Finset.sum_le_sum_of_subset fun i hi =>
      mem_filter.2 ⟨mem_univ i, (hag i hi).2⟩)⟩

/-- Private helper (homogenization `Ū = span(U)` of
[BenSassonCarmonIshaiKoppartySaraf2020, Section 6.3], printed p. 30 lines 16–25 of the accepted
JACM 2023 manuscript): lifts 1D line correlated agreement from `B_line * |F| ^ ℓ < |F| * #T` to
weighted proximity across the entire affine space `u₀ + ∑ j, z j • u j`. -/
private theorem all_close_affine_of_line_correlatedAgreement
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {C : Submodule F (ι → F)} {W : ι → ℕ} {B_W B_line ℓ : ℕ}
    (hline : ∀ (a b : ι → F) (S : Finset F),
      B_line < S.card →
      (∀ t ∈ S, ∃ c ∈ C, B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => (a + t • b) i = c i), W i) →
      ∃ D' : Finset ι, B_W ≤ ∑ i ∈ D', W i ∧
        ∃ w₀ ∈ C, ∃ w₁ ∈ C, ∀ i ∈ D', a i = w₀ i ∧ b i = w₁ i)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : B_line * (Fintype.card F) ^ ℓ < Fintype.card F * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ C,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) :
    ∀ z : Fin ℓ → F, ∃ c ∈ C,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i := by
  classical
  have hdir := all_close_dir_of_line_correlatedAgreement hline u₀ u T hT hclose
  let u' : Fin (ℓ + 1) → (ι → F) := Fin.cons (α := fun _ => ι → F) u₀ u
  let consF : F → (Fin ℓ → F) → (Fin (ℓ + 1) → F) := Fin.cons (α := fun _ => F)
  let T₀ : Finset (Fin (ℓ + 1) → F) := (Finset.univ : Finset (Fin ℓ → F)).image (consF 0)
  let T₁ : Finset (Fin (ℓ + 1) → F) :=
    ((Finset.univ : Finset Fˣ) ×ˢ T).image fun p => consF (p.1 : F) ((p.1 : F) • p.2)
  have hT₀_card : T₀.card = (Fintype.card F) ^ ℓ := by
    have hinj : Function.Injective (consF 0) := fun _ _ h => funext fun j => by
      simpa only [consF, Fin.cons_succ] using congrFun h j.succ
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  have hT₁_card : T₁.card = (Fintype.card F - 1) * T.card := by
    have hinj : Function.Injective (fun p : Fˣ × (Fin ℓ → F) =>
        consF (p.1 : F) ((p.1 : F) • p.2)) := fun p₁ p₂ h => by
      have hs : (p₁.1 : F) = p₂.1 := by simpa only [consF, Fin.cons_zero] using congrFun h 0
      exact Prod.ext (Units.ext hs) (funext fun j => mul_left_cancel₀ p₂.1.ne_zero (by
        simpa only [consF, Fin.cons_succ, Pi.smul_apply, smul_eq_mul, hs] using congrFun h j.succ))
    rw [Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_univ,
      Fintype.card_units]
  have hdisj : Disjoint T₀ T₁ := Finset.disjoint_left.2 fun _ hx₀ hx₁ => by
    obtain ⟨_, _, rfl⟩ := mem_image.1 hx₀; obtain ⟨p, _, hp⟩ := mem_image.1 hx₁
    exact p.1.ne_zero (by simpa only [consF, Fin.cons_zero] using congrFun hp 0)
  have hT_bar_gt : B_line * (Fintype.card F) ^ (ℓ + 1) < Fintype.card F * (T₀ ∪ T₁).card := by
    have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have h1 := Nat.mul_lt_mul_of_pos_right (lt_card_field_of_density_threshold hT)
      (Nat.pow_pos (Fintype.card_pos (α := F)) (n := ℓ))
    have h2 := Nat.mul_le_mul_left (Fintype.card F - 1) hT.le
    rw [Finset.card_union_of_disjoint hdisj, hT₀_card, hT₁_card]
    calc B_line * (Fintype.card F) ^ (ℓ + 1)
        = (1 + (Fintype.card F - 1)) * (B_line * (Fintype.card F) ^ ℓ) := by
          rw [show 1 + (Fintype.card F - 1) = Fintype.card F by omega, pow_succ]; ring
      _ = B_line * (Fintype.card F) ^ ℓ +
            (Fintype.card F - 1) * (B_line * (Fintype.card F) ^ ℓ) := by ring
      _ < _ := Nat.add_lt_add_of_lt_of_le h1 h2
      _ = Fintype.card F * ((Fintype.card F) ^ ℓ + (Fintype.card F - 1) * T.card) := by ring
  have hall := all_close_dir_of_line_correlatedAgreement hline 0 u' (T₀ ∪ T₁) hT_bar_gt
    fun x hx => by
    rw [zero_add]
    rcases mem_union.1 hx with hx₀ | hx₁
    · obtain ⟨d, _, rfl⟩ := mem_image.1 hx₀
      simpa only [Fin.sum_univ_succ, u', consF, Fin.cons_zero, Fin.cons_succ, zero_smul,
        zero_add] using hdir d
    · obtain ⟨p, hp, rfl⟩ := mem_image.1 hx₁
      obtain ⟨c, hcC, hge⟩ := hclose p.2 (mem_product.1 hp).2
      refine ⟨(p.1 : F) • c, C.smul_mem _ hcC, ?_⟩
      have hfilt : (Finset.univ.filter fun i =>
            (∑ k : Fin (ℓ + 1), consF (p.1 : F) ((p.1 : F) • p.2) k • u' k) i =
              ((p.1 : F) • c) i) =
          Finset.univ.filter fun i => (u₀ + ∑ j : Fin ℓ, p.2 j • u j) i = c i := by
        ext i
        simp only [mem_filter, mem_univ, true_and, Fin.sum_univ_succ, u', consF, Fin.cons_zero,
          Fin.cons_succ, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.add_apply, mul_assoc,
          ← Finset.mul_sum, ← mul_add, mul_right_inj' p.1.ne_zero]
      rwa [hfilt]
  intro z
  simpa only [Fin.sum_univ_succ, u', consF, Fin.cons_zero, Fin.cons_succ, one_smul] using
    hall (consF 1 z)

/-- Submodule of affine directions `d : Fin ℓ → F` whose combination `∑ j, d j • u j` agrees with
some codeword of `C` on `D`. -/
private def agreeDirSubmodule {F ι : Type*} [Field F] {ℓ : ℕ}
    (C : Submodule F (ι → F)) (u : Fin ℓ → (ι → F)) (D : Finset ι) :
    Submodule F (Fin ℓ → F) where
  carrier := {d | ∃ w ∈ C, ∀ i ∈ D, (∑ j : Fin ℓ, d j • u j) i = w i}
  zero_mem' := ⟨0, C.zero_mem, fun _ _ => by simp⟩
  add_mem' := by
    rintro d₁ d₂ ⟨w₁, hw₁, h₁⟩ ⟨w₂, hw₂, h₂⟩
    refine ⟨w₁ + w₂, C.add_mem hw₁ hw₂, fun i hi => ?_⟩
    have hadd : (∑ j : Fin ℓ, (d₁ + d₂) j • u j) i =
        (∑ j : Fin ℓ, d₁ j • u j) i + (∑ j : Fin ℓ, d₂ j • u j) i := by
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_mul,
        Finset.sum_add_distrib]
    rw [hadd, h₁ i hi, h₂ i hi, Pi.add_apply]
  smul_mem' := by
    rintro a d ⟨w, hw, h⟩
    refine ⟨a • w, C.smul_mem a hw, fun i hi => ?_⟩
    simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, mul_assoc, Finset.mul_sum] using
      congrArg (a * ·) (h i hi)

/-- Any finite subset of a weight-maximized agreement set on `supp W` contains the entire
support-filtered agreement set. -/
private theorem suppW_agree_subset_of_sum_le {ι : Type*} [Fintype ι]
    {F : Type*} [DecidableEq F] {W : ι → ℕ} {u₀ w₀ : ι → F} {D_z : Finset ι} {B : ℕ}
    (hDz_sub : ∀ i ∈ D_z, u₀ i = w₀ i) (hDz_ge : B ≤ ∑ i ∈ D_z, W i)
    (hmax : ∑ i ∈ Finset.univ.filter (fun i => u₀ i = w₀ i), W i ≤ B) :
    (Finset.univ.filter fun i => W i ≠ 0).filter (fun i => u₀ i = w₀ i) ⊆ D_z := by
  classical
  intro i₀ hi₀; by_contra hi₀_not
  have hsupp (X : Finset ι) : ∑ i ∈ X ∩ Finset.univ.filter (fun i => W i ≠ 0), W i =
      ∑ i ∈ X, W i := Finset.sum_subset Finset.inter_subset_left fun i hiX hnot =>
    by_contra fun hne => hnot (mem_inter.2 ⟨hiX, mem_filter.2 ⟨mem_univ i, hne⟩⟩)
  set Dstar := (Finset.univ.filter fun i => W i ≠ 0).filter fun i => u₀ i = w₀ i
  have hsub : D_z ∩ Finset.univ.filter (fun i => W i ≠ 0) ⊆ Dstar.erase i₀ := fun i hi =>
    let ⟨hiDz, hiS⟩ := mem_inter.1 hi
    mem_erase.2 ⟨fun heq => hi₀_not (heq ▸ hiDz), mem_filter.2 ⟨hiS, hDz_sub i hiDz⟩⟩
  have hsum_er := hsupp D_z ▸ Finset.sum_le_sum_of_subset hsub
  have hsplit : W i₀ + ∑ i ∈ Dstar.erase i₀, W i =
      ∑ i ∈ Finset.univ.filter (fun i => u₀ i = w₀ i), W i := by
    rw [Finset.add_sum_erase Dstar W hi₀]
    rw [show Dstar = (Finset.univ.filter fun i => u₀ i = w₀ i) ∩
      Finset.univ.filter (fun i => W i ≠ 0) by
      ext i; simp only [Dstar, mem_filter, mem_inter, mem_univ, true_and, and_comm], hsupp]
  have hW_pos : 0 < W i₀ := Nat.pos_of_ne_zero (mem_filter.1 (mem_filter.1 hi₀).1).2
  omega

/-- If `Fin ℓ → F` (`1 ≤ ℓ`) is covered by `L < |F|` translates of `F`-submodules, one of those
submodules is `⊤`. -/
private theorem exists_submodule_eq_top_of_cover {F : Type*} [Field F] [Fintype F]
    {α : Type*} {ℓ L : ℕ} (hℓ : 1 ≤ ℓ) (hL : L < Fintype.card F)
    {L_star : Finset α} (hLne : L_star.Nonempty) (hLcard : L_star.card ≤ L)
    (z_star : Fin ℓ → F) (K : α → Submodule F (Fin ℓ → F))
    (hcover : ∀ z : Fin ℓ → F, ∃ c ∈ L_star, z - z_star ∈ K c) :
    ∃ c ∈ L_star, K c = ⊤ := by
  classical
  let U : α → Finset (Fin ℓ → F) := fun c => Finset.univ.filter fun z => z - z_star ∈ K c
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image L_star (fun c => (U c).card) hLne
  refine ⟨c, hc, by_contra fun hne => ?_⟩
  have hU_pos : 0 < (U c).card := Finset.card_pos.2
    ⟨z_star, mem_filter.2 ⟨mem_univ _, by rw [sub_self]; exact (K c).zero_mem⟩⟩
  have hU_eq : (U c).card = Fintype.card (K c) := by
    rw [← Finset.card_univ]
    exact Finset.card_bij (fun z hz => (⟨z - z_star, (mem_filter.1 hz).2⟩ : K c))
      (fun _ _ => mem_univ _)
      (fun _ _ _ _ h => sub_left_inj.1 (Subtype.ext_iff.1 h))
      fun d _ => ⟨d.1 + z_star, mem_filter.2 ⟨mem_univ _, by rw [add_sub_cancel_right]; exact d.2⟩,
        Subtype.ext (add_sub_cancel_right _ _)⟩
  have hpigeon : (Fintype.card F) ^ ℓ ≤ L * (U c).card := calc
    (Fintype.card F) ^ ℓ = (Finset.univ : Finset (Fin ℓ → F)).card := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    _ ≤ (L_star.biUnion U).card := Finset.card_le_card fun z _ =>
        let ⟨a, ha, hm⟩ := hcover z; mem_biUnion.2 ⟨a, ha, mem_filter.2 ⟨mem_univ z, hm⟩⟩
    _ ≤ ∑ a ∈ L_star, (U a).card := Finset.card_biUnion_le
    _ ≤ L_star.card * (U c).card :=
        (Finset.sum_le_sum fun a ha => hmax a ha).trans_eq (by simp)
    _ ≤ L * (U c).card := Nat.mul_le_mul_right _ hLcard
  have hpow : (Fintype.card F) ^ ℓ = Fintype.card F * (Fintype.card F) ^ (ℓ - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hℓ, pow_succ, Nat.mul_comm]
  have hlt := Nat.mul_lt_mul_of_pos_right hL hU_pos
  have hle := Nat.mul_le_mul_left (Fintype.card F)
    (hU_eq.trans_le (card_submodule_le_pow_pred_of_ne_top hne))
  omega

/-- **Generic divergence-and-subspace lift from everywhere-close affine spaces to simultaneous
weighted correlated agreement** ([BenSassonCarmonIshaiKoppartySaraf2020], Section 6.3 on printed
pp. 30–31 and Section 7.3 on printed p. 34 of the accepted JACM 2023 manuscript, refined for zero
coordinate weights).

Given any linear code `C : Submodule F (ι → F)` over a finite field `F` with codeword list-size
bound `L` at `W`-weighted agreement `B_W` (`2 ≤ ℓ → L < |F|`) and full-line weighted correlated
agreement for every threshold `B' ≥ B_W`: if every point of `u₀ + ∑ j : Fin ℓ, z j • u j` achieves
`W`-weighted agreement at least `B_W` with `C`, then there exist a single subset `D' ⊆ supp W`
(`∀ i ∈ D', W i ≠ 0`) with `B_W ≤ ∑ i ∈ D', W i` and codewords `v₀, v_j ∈ C` agreeing with
`u₀, u_j` on `D'`.

Intersecting candidate agreement sets at the minimal-agreement point `u*` with `supp W` repairs
Section 7.3's "verbatim" claim on printed p. 34 when `W` has zero entries. Defining the direction
subspace directly via `C`'s restriction image lets this generic linear-code lemma avoid the unique
extension from `D'` used on printed p. 31 (for Reed–Solomon codes under Theorem 7.4, `α > ρ` makes
that extension available). The support guarantee `∀ i ∈ D', W i ≠ 0` is exported here and dropped
by the Reed–Solomon specializations. -/
theorem exists_weighted_correlatedAgreement_affine_of_divergence
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {C : Submodule F (ι → F)} {W : ι → ℕ} {B_W L ℓ : ℕ}
    (hlist : ∀ u : ι → F, ∃ Lset : Finset (ι → F), Lset.card ≤ L ∧
      ∀ c ∈ C, B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => u i = c i), W i → c ∈ Lset)
    (hline_all : ∀ {B' : ℕ}, B_W ≤ B' → ∀ a b : ι → F,
      (∀ t : F, ∃ c ∈ C,
        B' ≤ ∑ i ∈ Finset.univ.filter (fun i => (a + t • b) i = c i), W i) →
      ∃ D' : Finset ι, B' ≤ ∑ i ∈ D', W i ∧
        ∃ w₀ ∈ C, ∃ w₁ ∈ C, ∀ i ∈ D', a i = w₀ i ∧ b i = w₁ i)
    (hL : 2 ≤ ℓ → L < Fintype.card F)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (hall : ∀ z : Fin ℓ → F, ∃ c ∈ C,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) :
    ∃ D' : Finset ι, (∀ i ∈ D', W i ≠ 0) ∧ B_W ≤ ∑ i ∈ D', W i ∧
      ∃ v₀ ∈ C, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ C) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  classical
  let suppW := Finset.univ.filter fun i : ι => W i ≠ 0
  have hsum_supp (X : Finset ι) : ∑ i ∈ X ∩ suppW, W i = ∑ i ∈ X, W i :=
    Finset.sum_subset Finset.inter_subset_left fun i hiX hnot =>
      by_contra fun hne => hnot (mem_inter.2 ⟨hiX, mem_filter.2 ⟨mem_univ i, hne⟩⟩)
  match ℓ with
  | 0 =>
    obtain ⟨v₀, hv₀, hge⟩ := hall 0
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hge
    exact ⟨(Finset.univ.filter fun i => u₀ i = v₀ i) ∩ suppW,
      fun _ hi => (mem_filter.1 (mem_inter.1 hi).2).2,
      by rw [hsum_supp]; exact hge, v₀, hv₀, Fin.elim0,
      fun j => j.elim0, fun _ hi => ⟨(mem_filter.1 (mem_inter.1 hi).1).2, fun j => j.elim0⟩⟩
  | 1 =>
    obtain ⟨D₀, hD₀, v₀, hv₀, v₁, hv₁, hag⟩ := hline_all le_rfl u₀ (u 0) fun t => by
      simpa only [Fin.sum_univ_one] using hall (fun _ => t)
    exact ⟨D₀ ∩ suppW, fun _ hi => (mem_filter.1 (mem_inter.1 hi).2).2,
      by rw [hsum_supp]; exact hD₀,
      v₀, hv₀, fun _ => v₁, fun _ => hv₁, fun i hi =>
      let ⟨h0, h1⟩ := hag i (mem_inter.1 hi).1; ⟨h0, fun j => by fin_cases j; exact h1⟩⟩
  | ℓ' + 2 =>
    let u_aff (z : Fin (ℓ' + 2) → F) := u₀ + ∑ j, z j • u j
    let agreeW (w c : ι → F) := ∑ i ∈ Finset.univ.filter (fun i => w i = c i), W i
    let C_fin := Finset.univ.filter fun c : ι → F => c ∈ C
    have hC_ne : C_fin.Nonempty := ⟨0, mem_filter.2 ⟨mem_univ 0, C.zero_mem⟩⟩
    let score (z : Fin (ℓ' + 2) → F) := C_fin.sup' hC_ne fun c => agreeW (u_aff z) c
    obtain ⟨z_star, _, hz_min⟩ := Finset.exists_min_image Finset.univ score ⟨0, mem_univ 0⟩
    set B_star := score z_star; set u_star := u_aff z_star
    have hBW_le_Bstar : B_W ≤ B_star :=
      let ⟨c₀, hc₀, hge⟩ := hall z_star
      hge.trans (Finset.le_sup' (fun c => agreeW u_star c) (mem_filter.2 ⟨mem_univ c₀, hc₀⟩))
    have hall_Bstar (z : Fin (ℓ' + 2) → F) : ∃ c ∈ C, B_star ≤ agreeW (u_aff z) c :=
      let ⟨c, hc, hce⟩ := Finset.exists_mem_eq_sup' hC_ne fun c => agreeW (u_aff z) c
      ⟨c, (mem_filter.1 hc).2, hce ▸ hz_min z (mem_univ z)⟩
    obtain ⟨Lraw, hLraw_card, hLraw_mem⟩ := hlist u_star
    let L_star := Lraw.filter fun c => c ∈ C ∧ B_star ≤ agreeW u_star c
    have hLstar_ne : L_star.Nonempty := let ⟨c, hc, hge⟩ := hall_Bstar z_star
      ⟨c, mem_filter.2 ⟨hLraw_mem c hc (hBW_le_Bstar.trans hge), hc, hge⟩⟩
    let D_star (c : ι → F) := suppW.filter fun i => u_star i = c i
    obtain ⟨v_star, hv_mem, hK_top⟩ := exists_submodule_eq_top_of_cover (by omega)
      (hL (by omega)) hLstar_ne ((Finset.card_filter_le _ _).trans hLraw_card) z_star
      (fun c => agreeDirSubmodule C u (D_star c)) fun z => by
        let b_dir : ι → F := ∑ j, (z - z_star) j • u j
        obtain ⟨D_z, hDz_ge, w₀, hw₀C, w₁, hw₁C, hag_z⟩ :=
          hline_all hBW_le_Bstar u_star b_dir fun t => by
            have hcomb : u_star + t • b_dir = u_aff (z_star + t • (z - z_star)) := by
              funext i
              simp only [u_star, u_aff, b_dir, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
                Finset.sum_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
                mul_assoc, add_assoc]
            exact hcomb ▸ hall_Bstar (z_star + t • (z - z_star))
        have hw₀_ge : B_star ≤ agreeW u_star w₀ := hDz_ge.trans <|
          Finset.sum_le_sum_of_subset fun i hi => mem_filter.2 ⟨mem_univ i, (hag_z i hi).1⟩
        have hsub := suppW_agree_subset_of_sum_le (fun i hi => (hag_z i hi).1) hDz_ge <|
          Finset.le_sup' (fun c => agreeW u_star c) (mem_filter.2 ⟨mem_univ w₀, hw₀C⟩)
        exact ⟨w₀, mem_filter.2 ⟨hLraw_mem w₀ hw₀C (hBW_le_Bstar.trans hw₀_ge), hw₀C, hw₀_ge⟩,
          w₁, hw₁C, fun i hi => (hag_z i (hsub hi)).2⟩
    have hmem_K (d : Fin (ℓ' + 2) → F) :
        ∃ w ∈ C, ∀ i ∈ D_star v_star, (∑ j, d j • u j) i = w i := by
      have : d ∈ agreeDirSubmodule C u (D_star v_star) := hK_top ▸ Submodule.mem_top
      exact this
    have hex_j (j : Fin (ℓ' + 2)) : ∃ vj ∈ C, ∀ i ∈ D_star v_star, u j i = vj i := by
      obtain ⟨vj, hvj, hag⟩ := hmem_K (Pi.single j 1)
      refine ⟨vj, hvj, fun i hi => ?_⟩
      have hsingle : (∑ r : Fin (ℓ' + 2), Pi.single (M := fun _ => F) j (1 : F) r • u r) = u j := by
        rw [Finset.sum_eq_single j (fun r _ hr => by simp [Pi.single_eq_of_ne hr])
          (fun h => absurd (mem_univ j) h), Pi.single_eq_same, one_smul]
      rw [← hsingle]; exact hag i hi
    choose v hvC hv_ag using hex_j
    obtain ⟨w_neg, hw_negC, hag_neg⟩ := hmem_K (-z_star)
    have hD_sum : ∑ i ∈ D_star v_star, W i = agreeW u_star v_star := by
      rw [show D_star v_star = (Finset.univ.filter fun i => u_star i = v_star i) ∩ suppW by
        ext i; simp only [D_star, mem_inter, mem_filter, mem_univ, true_and, and_comm], hsum_supp]
    refine ⟨D_star v_star, fun _ hi => (mem_filter.1 (mem_filter.1 hi).1).2,
      hD_sum ▸ hBW_le_Bstar.trans (mem_filter.1 hv_mem).2.2, v_star + w_neg,
      C.add_mem (mem_filter.1 hv_mem).2.1 hw_negC, v, hvC, fun i hi => ⟨?_, fun j => hv_ag j i hi⟩⟩
    have h0 : u₀ i = u_star i + (∑ j, (-z_star) j • u j) i := by
      simp only [u_star, u_aff, Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, neg_mul, Finset.sum_neg_distrib, add_neg_cancel_right]
    exact h0.trans <| congrArg₂ (· + ·) (mem_filter.1 hi).2 (hag_neg i hi)

/-- **Dimension-independent lift of 1D weighted line correlated agreement to arbitrary-dimensional
affine spaces** ([BenSassonCarmonIshaiKoppartySaraf2020], Lemma 6.3, Section 6.3 on printed
pp. 29–31, and Section 7.3 on printed p. 34 of the accepted JACM 2023 manuscript).

Given any linear code `C : Submodule F (ι → F)`, coordinate weights `W : ι → ℕ`, threshold `B_W`,
list-size bound `L` (`2 ≤ ℓ → L < |F|`), and 1D weighted line correlated agreement with exceptional
count `≤ B_line` for all thresholds `B' ≥ B_W`: whenever `T ⊆ (Fin ℓ → F)` satisfies
`B_line * |F| ^ ℓ < |F| * #T` (density strictly above `B_line / |F|`, independent of `ℓ`) and every
point in `T` achieves `W`-weighted agreement at least `B_W` with `C`, there exist `D' ⊆ supp W`
with `B_W ≤ ∑ i ∈ D', W i` and codewords `v₀, v_j ∈ C` agreeing with `u₀, u_j` on `D'`. -/
theorem exists_weighted_correlatedAgreement_affine_of_line
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {C : Submodule F (ι → F)} {W : ι → ℕ} {B_W B_line L ℓ : ℕ}
    (hlist : ∀ u : ι → F, ∃ Lset : Finset (ι → F), Lset.card ≤ L ∧
      ∀ c ∈ C, B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => u i = c i), W i → c ∈ Lset)
    (hline : ∀ {B' : ℕ}, B_W ≤ B' → ∀ (a b : ι → F) (S : Finset F),
      B_line < S.card →
      (∀ t ∈ S, ∃ c ∈ C, B' ≤ ∑ i ∈ Finset.univ.filter (fun i => (a + t • b) i = c i), W i) →
      ∃ D' : Finset ι, B' ≤ ∑ i ∈ D', W i ∧
        ∃ w₀ ∈ C, ∃ w₁ ∈ C, ∀ i ∈ D', a i = w₀ i ∧ b i = w₁ i)
    (hL : 2 ≤ ℓ → L < Fintype.card F)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : B_line * (Fintype.card F) ^ ℓ < Fintype.card F * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ C,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) :
    ∃ D' : Finset ι, (∀ i ∈ D', W i ≠ 0) ∧ B_W ≤ ∑ i ∈ D', W i ∧
      ∃ v₀ ∈ C, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ C) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  have hall : ∀ z : Fin ℓ → F, ∃ c ∈ C,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i :=
    all_close_affine_of_line_correlatedAgreement (fun a b S hS hcl => hline le_rfl a b S hS hcl)
      u₀ u T hT hclose
  exact exists_weighted_correlatedAgreement_affine_of_divergence hlist
    (fun hB' a b hcl =>
      have hB_lt_q : B_line < Fintype.card F := lt_card_field_of_density_threshold hT
      hline hB' a b Finset.univ (by rwa [Finset.card_univ]) (fun t _ => hcl t))
    hL u₀ u hall

end Cslib.Code
