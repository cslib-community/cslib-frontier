/-
Copyright (c) 2026 Mayank Rathee, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.ReedSolomon
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Foundations.Data.Code.Linear
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve
import CslibFrontier.Foundations.Data.Hamming
import CslibFrontier.Probability.PMF.UniformBound

/-!
# Interleaved linear codes and random-linear-combination proximity bounds

Given a linear code `C : Submodule R (ι → M)` of length `|ι|` over alphabet `M` and a row-index
type `κ`, the *`κ`-interleaved linear code* `Cslib.Code.interleavedLinear κ C` consists of the
column-indexed words `W : ι → κ → M` whose rows `i ↦ W i r` (`r : κ`) all belong to `C`. Viewing
words column-wise over the block alphabet `κ → M` reuses Mathlib's `hammingDist` and
`Cslib.Code.minDist` directly: the Hamming distance between `W, V : ι → κ → M` counts the columns
`i : ι` on which at least one row disagrees, so proximity `hammingDist W V ≤ e` to
`interleavedLinear κ C` is equivalent to correlated agreement of the rows on a shared coordinate
subset `D' : Finset ι` of size at least `|ι| - e`
(`Cslib.Code.exists_mem_interleavedLinear_hammingDist_le_iff`), and interleaving over a nonempty
row set preserves minimum distance (`Cslib.Code.minDist_interleavedLinear`).

For random row linear combinations `i ↦ ∑ r : Fin m, z r • W i r` with uniform weights
`z : Fin m → F` over a finite field `F`, this module proves two complementary proximity bounds:

1. **Universal linear-code `d / 3` bound** (`3 * (e : ℕ∞) < minDist C`, step toward `#643` and
   `#5968` after Ames, Hazay, Ishai, and Venkitasubramaniam
   [AmesHazayIshaiVenkitasubramaniam2017]; locator not re-verified against primary PDF): an
   elementary characteristic-free 1D affine-line argument shows that if more than `e + 1` points on
   `u₀ + z • u₁` lie within distance `e` of `C`, then `u₀` and `u₁` share correlated agreement on
   at least `|ι| - e` coordinates (`Cslib.Code.exists_correlatedAgreement_of_three_mul_lt_minDist`).
   Lifting through `Cslib.Code.exists_weighted_correlatedAgreement_affine_of_line` bounds the
   probability that a uniform row combination of an `e`-far word lands within distance `e` of `C` by
   `(e + 1) / |F|` uniformly for all `m : ℕ`
   (`Cslib.Code.toOuterMeasure_sum_smul_close_le_of_three_mul_lt_minDist`), with unique-codeword
   extraction above `(e + 1) / |F|`
   (`Cslib.Code.exists_unique_mem_interleavedLinear_of_three_mul_lt_minDist`).
2. **Reed–Solomon unique-decoding `d / 2` bound** (`2 * e + k ≤ |ι|`, derived from
   [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.6 / eq. (1.2)] via
   `Cslib.Code.exists_uniqueMaximal_correlatedAgreement_affine_unique`): for
   `Cslib.Code.reedSolomon α k` with distinct evaluation points `α : ι → F`, an `e`-far
   column-word `W : ι → Fin m → F` produces an `e`-close uniform row linear combination with
   probability at most `|ι| / |F|` uniformly for all `m : ℕ`
   (`Cslib.Code.toOuterMeasure_sum_smul_reedSolomon_close_le`), and exceeding `|ι| / |F|` uniquely
   determines the nearest interleaved codeword `V ∈ interleavedLinear (Fin m) (reedSolomon α k)`
   (`Cslib.Code.exists_unique_mem_interleavedLinear_reedSolomon`).

## Main definitions

* `Cslib.Code.interleavedLinear`: the `κ`-interleaved linear code `Submodule R (ι → κ → M)`.

## Main results

* `Cslib.Code.minDist_interleavedLinear`: interleaving over a nonempty row index preserves
  `Cslib.Code.minDist`.
* `Cslib.Code.exists_mem_interleavedLinear_hammingDist_le_iff`: equivalence between column-Hamming
  proximity `≤ e` to `interleavedLinear κ C` and row correlated agreement on `≥ |ι| - e`
  coordinates.
* `Cslib.Code.hammingDist_sum_smul_le`: taking a row linear combination cannot increase column
  Hamming distance.
* `Cslib.Code.exists_correlatedAgreement_of_three_mul_lt_minDist`: 1D affine-line correlated
  agreement for arbitrary linear codes when `3 * e < minDist C` and `e + 1 < #S`.
* `Cslib.Code.toOuterMeasure_sum_smul_close_le_of_three_mul_lt_minDist` &
  `Cslib.Code.exists_unique_mem_interleavedLinear_of_three_mul_lt_minDist`: universal
  `(e + 1) / |F|` interleaved proximity bound and unique-decoding extraction for linear codes
  within `d / 3`.
* `Cslib.Code.toOuterMeasure_sum_smul_reedSolomon_close_le` &
  `Cslib.Code.exists_unique_mem_interleavedLinear_reedSolomon`: `|ι| / |F|` interleaved proximity
  bound and unique-decoding extraction for Reed–Solomon codes up to `2 * e + k ≤ |ι|`.

## References

* [S. Ames, C. Hazay, Y. Ishai, M. Venkitasubramaniam, *Ligero: Lightweight Sublinear Arguments
  Without a Trusted Setup*][AmesHazayIshaiVenkitasubramaniam2017]
* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf,
  *Proximity Gaps for Reed–Solomon Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
-/

public section

namespace Cslib.Code

open Cslib.Probability Finset
open scoped BigOperators ENNReal

/-! ### Interleaved linear codes, minimum distance, and correlated agreement -/

section InterleavedLinear

/-- The *`κ`-interleaved linear code* of `C : Submodule R (ι → M)` over column alphabet `κ → M`:
a column-indexed word `W : ι → κ → M` belongs to `interleavedLinear κ C` iff every row
`i ↦ W i r` (`r : κ`) belongs to `C`. -/
def interleavedLinear (κ : Type*) {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (C : Submodule R (ι → M)) : Submodule R (ι → κ → M) where
  carrier := {W | ∀ r : κ, (fun i => W i r) ∈ C}
  add_mem' ha hb r := C.add_mem (ha r) (hb r)
  zero_mem' _ := C.zero_mem
  smul_mem' c _ hx r := C.smul_mem c (hx r)

/-- Membership in `interleavedLinear κ C` means every row belongs to `C`. -/
@[simp]
theorem mem_interleavedLinear {κ ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {C : Submodule R (ι → M)} {W : ι → κ → M} :
    W ∈ interleavedLinear κ C ↔ ∀ r : κ, (fun i => W i r) ∈ C :=
  Iff.rfl

/-- Any linear combination of the rows of a codeword `W ∈ interleavedLinear κ C` belongs to `C`. -/
theorem sum_smul_mem_of_mem_interleavedLinear {κ ι R M : Type*} [Fintype κ] [Semiring R]
    [AddCommMonoid M] [Module R M] {C : Submodule R (ι → M)} {W : ι → κ → M}
    (hW : W ∈ interleavedLinear κ C) (z : κ → R) :
    (fun i => ∑ r : κ, z r • W i r) ∈ C := by
  have heq : (fun i => ∑ r : κ, z r • W i r) = ∑ r : κ, z r • fun i => W i r := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply]
  rw [heq]
  exact Submodule.sum_mem C fun r _ => C.smul_mem (z r) (hW r)

/-- Taking a row linear combination cannot increase column Hamming distance. -/
theorem hammingDist_sum_smul_le {κ ι R M : Type*} [Fintype κ] [Fintype ι] [Semiring R]
    [AddCommMonoid M] [Module R M] [DecidableEq M] (z : κ → R) (W₁ W₂ : ι → κ → M) :
    hammingDist (fun i => ∑ r : κ, z r • W₁ i r) (fun i => ∑ r : κ, z r • W₂ i r) ≤
      hammingDist W₁ W₂ :=
  hammingDist_comp_le_hammingDist (x := W₁) (y := W₂) fun _ (v : κ → M) => ∑ r : κ, z r • v r

/-- **Minimum distance of an interleaved linear code**: when the row index `κ` is nonempty,
interleaving preserves `Cslib.Code.minDist`. -/
theorem minDist_interleavedLinear (κ : Type*) {ι R M : Type*} [Fintype κ] [Nonempty κ] [Fintype ι]
    [Ring R] [AddCommGroup M] [Module R M] [DecidableEq M] (C : Submodule R (ι → M)) :
    minDist (interleavedLinear κ C : Set (ι → κ → M)) = minDist (C : Set (ι → M)) := by
  classical
  refine le_antisymm ?_ ?_
  · refine (le_minDist_iff_hammingNorm C).2 fun c hc hc0 => ?_
    let r₀ : κ := Classical.arbitrary κ
    let W : ι → κ → M := fun i => Pi.single r₀ (c i)
    have hW : W ∈ interleavedLinear κ C := fun r => by
      rcases eq_or_ne r r₀ with rfl | hr
      · simpa only [W, Pi.single_eq_same] using hc
      · convert C.zero_mem using 1
        exact funext fun i => Pi.single_eq_of_ne (M := fun _ => M) hr (c i)
    have hnorm : hammingNorm W = hammingNorm c :=
      hammingNorm_comp (fun _ => Pi.single r₀) (fun _ => Pi.single_injective r₀) fun _ =>
        Pi.single_zero r₀
    rw [← hnorm]
    exact (le_minDist_iff_hammingNorm (interleavedLinear κ C)).1 le_rfl W hW
      (by rwa [← hammingNorm_pos_iff, hnorm, hammingNorm_pos_iff])
  · refine (le_minDist_iff_hammingNorm (interleavedLinear κ C)).2 fun W hW hW0 => ?_
    obtain ⟨r₀, hr₀⟩ : ∃ r : κ, (fun i => W i r) ≠ 0 := by
      by_contra! hall
      exact hW0 (funext fun i => funext fun r => congrFun (hall r) i)
    exact ((le_minDist_iff_hammingNorm C).1 le_rfl _ (hW r₀) hr₀).trans
      (Nat.cast_le.2 (hammingNorm_comp_le_hammingNorm (fun _ (v : κ → M) => v r₀) fun _ => rfl))

/-- **Interleaved proximity iff correlated agreement**: `W : ι → κ → M` lies within column-Hamming
distance `e` of `interleavedLinear κ C` if and only if its rows share a single agreement set
`D' : Finset ι` of size at least `|ι| - e` with codewords `v r ∈ C`. -/
theorem exists_mem_interleavedLinear_hammingDist_le_iff {κ ι R M : Type*} [Fintype κ] [Fintype ι]
    [Semiring R] [AddCommMonoid M] [Module R M] [DecidableEq M]
    {C : Submodule R (ι → M)} {W : ι → κ → M} {e : ℕ} :
    (∃ V ∈ interleavedLinear κ C, hammingDist W V ≤ e) ↔
      ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
        ∃ v : κ → (ι → M), (∀ r, v r ∈ C) ∧ ∀ i ∈ D', ∀ r, W i r = v r i := by
  classical
  constructor
  · rintro ⟨V, hV, hdist⟩
    refine ⟨Finset.univ.filter fun i => W i = V i, ?_, fun r i => V i r, hV,
      fun i hi r => congrFun (Finset.mem_filter.1 hi).2 r⟩
    have := card_filter_eq_add_hammingDist W V
    omega
  · rintro ⟨D', hD', v, hv, hag⟩
    let V : ι → κ → M := fun i r => v r i
    refine ⟨V, hv, ?_⟩
    have hcard : D'.card ≤ (Finset.univ.filter fun i => W i = V i).card :=
      Finset.card_le_card fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ i, funext (hag i hi)⟩
    have := card_filter_eq_add_hammingDist W V
    omega

end InterleavedLinear

/-! ### Universal linear-code `d / 3` correlated agreement and interleaved proximity -/

section LinearCodeThirdRadius

/-- **1D affine-line correlated agreement within one-third the minimum distance**: over an arbitrary
field `F`, if `C : Submodule F (ι → F)` satisfies `3 * (e : ℕ∞) < minDist C` and strictly more than
`e + 1` scalars `z ∈ S` satisfy that `u₀ + z • u₁` lies within Hamming distance `e` of `C`, then
`u₀` and `u₁` agree with codewords `v₀, v₁ ∈ C` on a shared coordinate subset `D' : Finset ι` of
size at least `|ι| - e`. -/
theorem exists_correlatedAgreement_of_three_mul_lt_minDist {F ι : Type*} [Field F] [DecidableEq F]
    [Fintype ι] {C : Submodule F (ι → F)} {e : ℕ}
    (hmin : 3 * (e : ℕ∞) < minDist (C : Set (ι → F)))
    (u₀ u₁ : ι → F) (S : Finset F) (hS : e + 1 < S.card)
    (hclose : ∀ z ∈ S, ∃ c ∈ C, hammingDist (u₀ + z • u₁) c ≤ e) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
      ∃ v₀ ∈ C, ∃ v₁ ∈ C, ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i := by
  classical
  obtain ⟨z₀, hz₀, z₁, hz₁, hz_ne⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
  obtain ⟨c₀, hc₀, hd₀⟩ := hclose z₀ hz₀
  obtain ⟨c₁, hc₁, hd₁⟩ := hclose z₁ hz₁
  have hsub_ne : z₁ - z₀ ≠ 0 := sub_ne_zero.2 hz_ne.symm
  let v₁ : ι → F := (z₁ - z₀)⁻¹ • (c₁ - c₀)
  let v₀ : ι → F := c₀ - z₀ • v₁
  have hv₁ : v₁ ∈ C := C.smul_mem _ (C.sub_mem hc₁ hc₀)
  have hv₀ : v₀ ∈ C := C.sub_mem hc₀ (C.smul_mem _ hv₁)
  have hv_z₀ : v₀ + z₀ • v₁ = c₀ := sub_add_cancel c₀ (z₀ • v₁)
  have hv_z₁ : v₀ + z₁ • v₁ = c₁ := by
    funext i
    simp only [v₀, v₁, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (c₁ i - c₀ i) * mul_inv_cancel₀ hsub_ne
  let η₀ : ι → F := u₀ - v₀
  let η₁ : ι → F := u₁ - v₁
  let B : Finset ι := Finset.univ.filter fun i => η₀ i ≠ 0 ∨ η₁ i ≠ 0
  have hdiff (z : F) (i : ι) : (u₀ + z • u₁) i - (v₀ + z • v₁) i = η₀ i + z * η₁ i := by
    simp only [η₀, η₁, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- Two distinct roots of `η₀ i + z * η₁ i` force `i ∉ B`.
  have hnot_mem {i : ι} {za zb : F} (hne : za ≠ zb) (ha : η₀ i + za * η₁ i = 0)
      (hb : η₀ i + zb * η₁ i = 0) : i ∉ B := by
    have hη₁ : η₁ i = 0 := mul_eq_zero.1
      (show (za - zb) * η₁ i = 0 by linear_combination ha - hb) |>.resolve_left (sub_ne_zero.2 hne)
    have hη₀ : η₀ i = 0 := by simpa only [hη₁, mul_zero, add_zero] using ha
    simp [B, hη₀, hη₁]
  have hB_sub : B ⊆ (Finset.univ.filter fun i => (u₀ + z₀ • u₁) i ≠ c₀ i) ∪
      (Finset.univ.filter fun i => (u₀ + z₁ • u₁) i ≠ c₁ i) := by
    intro i hi
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra! hboth
    exact hnot_mem hz_ne (by rw [← hdiff, hv_z₀, hboth.1, sub_self])
      (by rw [← hdiff, hv_z₁, hboth.2, sub_self]) hi
  have hB_le : B.card ≤ 2 * e := by
    have hcard := (Finset.card_le_card hB_sub).trans (Finset.card_union_le _ _)
    change B.card ≤ hammingDist (u₀ + z₀ • u₁) c₀ + hammingDist (u₀ + z₁ • u₁) c₁ at hcard
    omega
  have hdist_v (z : F) (hz : z ∈ S) : hammingDist (u₀ + z • u₁) (v₀ + z • v₁) ≤ e := by
    obtain ⟨cz, hcz, hdz⟩ := hclose z hz
    have hle_B : hammingDist (u₀ + z • u₁) (v₀ + z • v₁) ≤ B.card := by
      refine Finset.card_le_card fun i hi => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, B] at hi ⊢
      by_contra! h0
      exact hi (by rw [← sub_eq_zero, hdiff z i, h0.1, h0.2, mul_zero, add_zero])
    have htri := hammingDist_triangle cz (u₀ + z • u₁) (v₀ + z • v₁)
    rw [hammingDist_comm cz (u₀ + z • u₁)] at htri
    have hceq : cz = v₀ + z • v₁ := by
      by_contra hne
      exact hmin.not_ge ((minDist_le_hammingDist hcz (C.add_mem hv₀ (C.smul_mem z hv₁)) hne).trans
        (by exact_mod_cast (by omega : hammingDist cz (v₀ + z • v₁) ≤ 3 * e)))
    rwa [← hceq]
  have hzero_ge (z : F) (hz : z ∈ S) :
      B.card - e ≤ (B.filter fun i => η₀ i + z * η₁ i = 0).card := by
    have hpart := Finset.card_filter_add_card_filter_not (s := B) (fun i => η₀ i + z * η₁ i = 0)
    have hle : (B.filter fun i => ¬ (η₀ i + z * η₁ i = 0)).card ≤
        hammingDist (u₀ + z • u₁) (v₀ + z • v₁) :=
      Finset.card_le_card fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ i, fun h =>
        (Finset.mem_filter.1 hi).2 (by rw [← hdiff z i, h, sub_self])⟩
    have := hdist_v z hz
    omega
  have hroot_le (i : ι) (hi : i ∈ B) :
      (S.filter fun z => η₀ i + z * η₁ i = 0).card ≤ 1 :=
    Finset.card_le_one.2 fun za hza zb hzb => by
      by_contra hne
      exact hnot_mem hne (Finset.mem_filter.1 hza).2 (Finset.mem_filter.1 hzb).2 hi
  have hsum_bound : S.card * (B.card - e) ≤ B.card := by
    have h1 := Finset.card_nsmul_le_sum S _ _ hzero_ge
    have h2 := Finset.sum_le_card_nsmul B _ 1 hroot_le
    simp only [smul_eq_mul, mul_one, Finset.card_filter] at h1 h2
    exact h1.trans (Finset.sum_comm.trans_le h2)
  have hB_le_e : B.card ≤ e := by
    by_contra! hgt
    have hmul := Nat.mul_le_mul_right (B.card - e) (show e + 2 ≤ S.card by omega)
    have he_le := Nat.le_mul_of_pos_right e (show 0 < B.card - e by omega)
    rw [Nat.succ_mul, Nat.succ_mul] at hmul
    omega
  refine ⟨Bᶜ, by rw [Finset.card_compl]; omega, v₀, hv₀, v₁, hv₁, fun i hi => ?_⟩
  simp only [B, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_or, ne_eq,
    not_not] at hi
  exact ⟨sub_eq_zero.1 hi.1, sub_eq_zero.1 hi.2⟩

private lemma exists_correlatedAgreement_affine_of_three_mul_lt_minDist
    {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {C : Submodule F (ι → F)} {e m : ℕ}
    (hmin : 3 * (e : ℕ∞) < minDist (C : Set (ι → F)))
    (W : ι → Fin m → F) (T : Finset (Fin m → F))
    (hT : (e + 1) * (Fintype.card F) ^ m < Fintype.card F * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ C, hammingDist (fun i => ∑ r : Fin m, z r • W i r) c ≤ e) :
    ∃ V ∈ interleavedLinear (Fin m) C, hammingDist W V ≤ e := by
  classical
  have htwo : 2 * (e : ℕ∞) < minDist (C : Set (ι → F)) :=
    lt_of_le_of_lt (by gcongr; norm_num) hmin
  have hagree (x c : ι → F) : ∑ i ∈ Finset.univ.filter (fun i => x i = c i), (1 : ℕ) +
      hammingDist x c = Fintype.card ι := by
    rw [← Finset.card_eq_sum_ones]
    exact card_filter_eq_add_hammingDist x c
  have hlist (u : ι → F) : ∃ Lset : Finset (ι → F), Lset.card ≤ 1 ∧
      ∀ c ∈ C, Fintype.card ι - e ≤
        ∑ i ∈ Finset.univ.filter (fun i => u i = c i), (1 : ℕ) → c ∈ Lset := by
    by_cases hex : ∃ c ∈ C, hammingDist u c ≤ e
    · refine ⟨{hex.choose}, by simp, fun c hc hs => Finset.mem_singleton.2 ?_⟩
      have := hagree u c
      exact eq_of_hammingDist_le_of_two_mul_lt_minDist (w := u) htwo hc hex.choose_spec.1
        (by rw [hammingDist_comm]; omega) (by rw [hammingDist_comm]; exact hex.choose_spec.2)
    · exact ⟨∅, Nat.zero_le 1, fun c hc hs => (hex ⟨c, hc, by have := hagree u c; omega⟩).elim⟩
  have hline : ∀ {B' : ℕ}, Fintype.card ι - e ≤ B' → ∀ (a b : ι → F) (S : Finset F),
      e + 1 < S.card →
      (∀ t ∈ S, ∃ c ∈ C, B' ≤ ∑ i ∈ Finset.univ.filter (fun i => (a + t • b) i = c i), (1 : ℕ)) →
      ∃ D' : Finset ι, B' ≤ ∑ i ∈ D', (1 : ℕ) ∧
        ∃ w₀ ∈ C, ∃ w₁ ∈ C, ∀ i ∈ D', a i = w₀ i ∧ b i = w₁ i := by
    intro B' hB' a b S hS hcl
    obtain ⟨t₀, ht₀⟩ := Finset.card_pos.1 (by omega : 0 < S.card)
    obtain ⟨c₀, _, hs₀⟩ := hcl t₀ ht₀
    have := hagree (a + t₀ • b) c₀
    have hmin' : 3 * ((Fintype.card ι - B' : ℕ) : ℕ∞) < minDist (C : Set (ι → F)) :=
      lt_of_le_of_lt (by exact_mod_cast (by omega : 3 * (Fintype.card ι - B') ≤ 3 * e)) hmin
    obtain ⟨D', hD', w₀, hw₀, w₁, hw₁, hag⟩ :=
      exists_correlatedAgreement_of_three_mul_lt_minDist hmin' a b S (by omega) fun t ht => by
        obtain ⟨c, hc, hs⟩ := hcl t ht
        have := hagree (a + t • b) c
        exact ⟨c, hc, by omega⟩
    exact ⟨D', by rw [← Finset.card_eq_sum_ones]; omega, w₀, hw₀, w₁, hw₁, hag⟩
  obtain ⟨D', _, hD'_sum, _, _, v, hv, hag⟩ :=
    exists_weighted_correlatedAgreement_affine_of_line (C := C) (W := fun _ => 1)
      (B_W := Fintype.card ι - e) (B_line := e + 1) (L := 1) hlist hline
      (fun _ => Fintype.one_lt_card) 0 (fun r i => W i r) T hT fun z hz => by
        obtain ⟨c, hc, hd⟩ := hclose z hz
        have heq : (0 : ι → F) + ∑ r : Fin m, z r • (fun i => W i r) =
            fun i => ∑ r : Fin m, z r • W i r :=
          funext fun i => by simp [Finset.sum_apply]
        have := hagree (fun i => ∑ r : Fin m, z r • W i r) c
        refine ⟨c, hc, ?_⟩
        rw [heq]
        dsimp only
        omega
  exact exists_mem_interleavedLinear_hammingDist_le_iff.2
    ⟨D', by simpa only [← Finset.card_eq_sum_ones] using hD'_sum, v, hv,
      fun i hi r => (hag i hi).2 r⟩

/-- Step toward `#643` and `#5968` after [AmesHazayIshaiVenkitasubramaniam2017] (locator not
re-verified against primary PDF; universal linear-code `d / 3` interleaved proximity bound): over a
finite field `F`, if `3 * (e : ℕ∞) < minDist C` and `W : ι → Fin m → F` has column-Hamming distance
strictly greater than `e` from every codeword of `interleavedLinear (Fin m) C`, then a uniformly
random row linear combination `i ↦ ∑ r, z r • W i r` lies within Hamming distance `e` of `C` with
probability at most `(e + 1) / |F|`, uniformly for all `m : ℕ`. -/
theorem toOuterMeasure_sum_smul_close_le_of_three_mul_lt_minDist
    {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {C : Submodule F (ι → F)} {e m : ℕ}
    (hmin : 3 * (e : ℕ∞) < minDist (C : Set (ι → F)))
    {W : ι → Fin m → F}
    (hfar : ∀ V ∈ interleavedLinear (Fin m) C, e < hammingDist W V) :
    (PMF.uniformOfFintype (Fin m → F)).toOuterMeasure
        {z | ∃ c ∈ C, hammingDist (fun i => ∑ r : Fin m, z r • W i r) c ≤ e} ≤
      ((e + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  refine Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_div Fintype.card_pos ?_
  rw [Fintype.card_fun, Fintype.card_fin]
  by_contra hlt
  push Not at hlt
  obtain ⟨V, hV, hdist⟩ := exists_correlatedAgreement_affine_of_three_mul_lt_minDist hmin W _ hlt
    fun z hz => (Finset.mem_filter.1 hz).2
  exact (hfar V hV).not_ge hdist

/-- **Unique-decoding extraction for linear codes within `d / 3`**: if `3 * (e : ℕ∞) < minDist C`
and a uniform row linear combination of `W : ι → Fin m → F` lies within Hamming distance `e` of `C`
with probability strictly greater than `(e + 1) / |F|`, then there exists a unique interleaved
codeword `V ∈ interleavedLinear (Fin m) C` within column-Hamming distance `e` of `W`. -/
theorem exists_unique_mem_interleavedLinear_of_three_mul_lt_minDist
    {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {C : Submodule F (ι → F)} {e m : ℕ}
    (hmin : 3 * (e : ℕ∞) < minDist (C : Set (ι → F)))
    {W : ι → Fin m → F}
    (hprob : ((e + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) <
      (PMF.uniformOfFintype (Fin m → F)).toOuterMeasure
        {z | ∃ c ∈ C, hammingDist (fun i => ∑ r : Fin m, z r • W i r) c ≤ e}) :
    ∃! V : ι → Fin m → F, V ∈ interleavedLinear (Fin m) C ∧ hammingDist W V ≤ e := by
  have hex : ∃ V ∈ interleavedLinear (Fin m) C, hammingDist W V ≤ e := by
    by_contra hfar
    push Not at hfar
    exact hprob.not_ge (toOuterMeasure_sum_smul_close_le_of_three_mul_lt_minDist hmin hfar)
  obtain ⟨V, hV, hdist⟩ := hex
  have htwo : 2 * (e : ℕ∞) < minDist (C : Set (ι → F)) :=
    lt_of_le_of_lt (by gcongr; norm_num) hmin
  refine ⟨V, ⟨hV, hdist⟩, fun V' ⟨hV', hdist'⟩ => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · funext i r
    exact r.elim0
  · have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hmin_int : 2 * (e : ℕ∞) < minDist (interleavedLinear (Fin m) C : Set (ι → Fin m → F)) := by
      rwa [minDist_interleavedLinear]
    exact eq_of_hammingDist_le_of_two_mul_lt_minDist hmin_int hV' hV
      (by rwa [hammingDist_comm]) (by rwa [hammingDist_comm])

end LinearCodeThirdRadius

/-! ### Reed–Solomon unique-decoding `d / 2` interleaved proximity bound -/

section ReedSolomonUnique

/-- **Reed–Solomon interleaved proximity bound in the unique-decoding regime** (`2 * e + k ≤ |ι|`,
derived from [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.6 / eq. (1.2)]): over a finite field
`F` with distinct evaluation points `α : ι → F`, if `W : ι → Fin m → F` has column-Hamming distance
strictly greater than `e` from `interleavedLinear (Fin m) (reedSolomon α k)`, then a uniformly
random row linear combination `i ↦ ∑ r, z r • W i r` lies within Hamming distance `e` of
`reedSolomon α k` with probability at most `|ι| / |F|`, uniformly for all `m : ℕ`. -/
theorem toOuterMeasure_sum_smul_reedSolomon_close_le
    {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {e k m : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {W : ι → Fin m → F}
    (hfar : ∀ V ∈ interleavedLinear (Fin m) (reedSolomon α k), e < hammingDist W V) :
    (PMF.uniformOfFintype (Fin m → F)).toOuterMeasure
        {z | ∃ c ∈ reedSolomon α k, hammingDist (fun i => ∑ r : Fin m, z r • W i r) c ≤ e} ≤
      (Fintype.card ι : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  refine Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_div Fintype.card_pos ?_
  rw [Fintype.card_fun, Fintype.card_fin]
  by_contra hlt
  push Not at hlt
  obtain ⟨D', hD', _, _, v, hv, hag, _⟩ :=
    exists_uniqueMaximal_correlatedAgreement_affine_unique hα hunique 0 (fun r i => W i r) _ hlt
      fun z hz => by
        obtain ⟨c, hc, hd⟩ := (Finset.mem_filter.1 hz).2
        refine ⟨c, hc, ?_⟩
        convert hd using 2
        funext i
        simp only [Pi.add_apply, Pi.zero_apply, zero_add, Finset.sum_apply, Pi.smul_apply]
  obtain ⟨V, hV, hdist⟩ := exists_mem_interleavedLinear_hammingDist_le_iff.2
    ⟨D', hD', v, hv, fun i hi r => (hag i hi).2 r⟩
  exact (hfar V hV).not_ge hdist

/-- **Reed–Solomon interleaved correlated agreement and unique-codeword extraction in the
unique-decoding regime** (`2 * e + k ≤ |ι|`): if a uniform row linear combination of
`W : ι → Fin m → F` lies within Hamming distance `e` of `reedSolomon α k` with probability strictly
greater than `|ι| / |F|`, then there exists a unique interleaved codeword
`V ∈ interleavedLinear (Fin m) (reedSolomon α k)` within column-Hamming distance `e` of `W`
(equivalently, unique Reed–Solomon row codewords agreeing with `W` on at least `|ι| - e` shared
columns). -/
theorem exists_unique_mem_interleavedLinear_reedSolomon
    {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {e k m : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {W : ι → Fin m → F}
    (hprob : (Fintype.card ι : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) <
      (PMF.uniformOfFintype (Fin m → F)).toOuterMeasure
        {z | ∃ c ∈ reedSolomon α k, hammingDist (fun i => ∑ r : Fin m, z r • W i r) c ≤ e}) :
    ∃! V : ι → Fin m → F,
      V ∈ interleavedLinear (Fin m) (reedSolomon α k) ∧ hammingDist W V ≤ e := by
  obtain ⟨V, hV, hdist⟩ :
      ∃ V ∈ interleavedLinear (Fin m) (reedSolomon α k), hammingDist W V ≤ e := by
    by_contra! hfar
    exact hprob.not_ge (toOuterMeasure_sum_smul_reedSolomon_close_le hα hunique hfar)
  refine ⟨V, ⟨hV, hdist⟩, fun V' ⟨hV', hdist'⟩ => funext fun i => funext fun r => ?_⟩
  exact congrFun (eq_of_hammingDist_le_reedSolomon (f := fun j => W j r) hα hunique (hV' r) (hV r)
    ((hammingDist_comp_le_hammingDist fun _ (v : Fin m → F) => v r).trans hdist')
    ((hammingDist_comp_le_hammingDist fun _ (v : Fin m → F) => v r).trans hdist)) i

end ReedSolomonUnique

end Cslib.Code
