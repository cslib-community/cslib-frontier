/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Basic
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Main
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Walk
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Exchange
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Num
import CslibFrontier.Foundations.Data.Finset.DisjointCard

/-!
# Contracting length functions on unitriangular groups

Section F.1 of [AnthropicVPVNP2026]. A length function `l` on a group contracts (`Flag.Contr l μ s`)
if along every homomorphism from `Mat_μ(F₂)` the mean of `l²` over rank `μ` is at most `s²` times
the mean over rank `1`. In the contracting case the displacement lengths of the translation
action on maps into a price space contract (`Poincare.contr_len_transAct`, the remark of
Section F.1). Contraction extends to all ranks with the growth `Flag.grow` (Lemma F.1); elements
of rank one in the upper right block have length at most `18 ∑_j |x_j|` (Lemma F.2); and by
induction along the powers of two, every contracting length on `U_n` has root mean square at most
`Poincare.kappa μ s n ∑_j |x_j|` (Lemma F.3, `Poincare.bd_kappa`), where `κ_n² n = o(n²)`; the
consequence used later is `Poincare.exists_kappa_le`.

## Main definitions

* `Poincare.kappa`: the constant `ϑ_n` of Lemma F.3.

## Main results

* `Poincare.contr_len_transAct`: the remark of Section F.1.
* `Poincare.bd_kappa`: Lemma F.3.
* `Poincare.exists_kappa_le`: a window size `u` with `4 C(3u) ≤ (u − 1)²/32²`, where
  `C(n) = κ_n² n`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Section F.1, Lemmas F.1–F.3, pp. 38–39; modules `Paper.Lengths` and `Paper.Groups`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Poincare

open Finset Filter Matrix Cslib.PartyTensor Cslib.Circuits.Arithmetic.Separation.Flag
open Cslib.Circuits.Arithmetic.Separation.TwoCases
open Cslib.SLTower (U x lo hi)

/-! ### Lengths from maps into price spaces -/

/-- **Remark in Section F.1** (p. 38): if `D(μ) ≤ s D(1)` for all prices on `Mat_μ(F₂)` and the
metric of `Y` is a price, then for every map `z` from a finite group `G` to `Y` the length
`g ↦ |z, g z|` of the translation action contracts. Along `θ`, the pull-backs
`W ↦ z (θ W k)` are prices for every `k`, and the mean over `k` is the claim. -/
theorem contr_len_transAct {K : Type} [Field K] {μ : ℕ} {s : ℝ}
    (hcase : ∀ w : Mt μ → Mt μ → ℝ, IsPrice K w → distAtRank w μ ≤ s * distAtRank w 1)
    {G Y : Type} [Group G] [Fintype G] [MetricSpace Y] (hY : IsPrice K fun a b : Y => dist a b)
    (z : PiLp 2 fun _ : G => Y) : Contr ((transAct G Y).len z) μ s := by
  intro τ hτ i
  set f := fun M => (transAct G Y).len z (τ M)
  set w : G → Mt μ → Mt μ → ℝ := fun k a b => dist (z (τ a * k)) (z (τ b * k))
  have e : ∀ a W, ∑ k, w k a (a + W) ^ 2 = f W ^ 2 := fun a W => by
    simp only [w, f, IsoAct.len_apply, transAct_dist]
    exact Fintype.sum_equiv (Equiv.mulLeft (τ a)) _ _ fun k => by
      rw [Equiv.coe_mulLeft, add_comm, hτ, mul_assoc, dist_comm]
  have key : ∀ r, rankMean f r = ∑ k, meanSq (w k) r := fun r => by
    have hc : (Fintype.card (Mt μ) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [meanSq, rankMean, ← sum_div]
    rw [sum_comm, sum_congr rfl fun a _ => sum_comm, sum_congr rfl fun a _ =>
      sum_congr rfl fun W _ => e a W]
    simp only [sum_const, card_univ, nsmul_eq_mul]
    field_simp
  rw [DM_dg_eq, DM_dg_eq, card_univ, Fintype.card_fin, card_singleton, key, key, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [mul_sum]
  refine sum_le_sum fun k _ => ?_
  rw [← distAtRank_sq, ← distAtRank_sq, ← mul_pow]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hcase _ (hY.comp fun a => z (τ a * k))) 2

/-! ### Lemma F.1: growth with the rank -/

/-- The arithmetic of Lemma F.1: "we write `r` in base `μ`". If `D` vanishes at `0`, is
subadditive and has `D(μ i) ≤ s D(i)` up to `k`, then `D(r) ≤ μ(j + 1)s^j D(1)` for
`j = ⌊log_μ r⌋`. -/
private theorem le_grow {D : ℕ → ℝ} {μ k : ℕ} {s : ℝ} (hμ : 2 ≤ μ) (hs : 1 ≤ s) (h0 : D 0 = 0)
    (h1 : 0 ≤ D 1) (hadd : ∀ i j, i + j ≤ k → D (i + j) ≤ D i + D j)
    (hmul : ∀ i, μ * i ≤ k → D (μ * i) ≤ s * D i) {r : ℕ} (hr : r ≤ k) :
    D r ≤ grow μ s r * D 1 := by
  unfold grow
  by_cases hrm : r < μ
  · rw [Nat.log_of_lt hrm]
    simp only [CharP.cast_eq_zero, zero_add, mul_one, pow_zero]
    have hlin : ∀ t ≤ k, D t ≤ t * D 1 := fun t ht => by
      induction t with
      | zero => simp [h0]
      | succ t ih => push_cast; linarith [hadd t 1 ht, ih (by omega)]
    exact (hlin r hr).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hrm.le) h1)
  · have hdiv := le_grow hμ hs h0 h1 hadd hmul ((Nat.div_le_self r μ).trans hr)
    have hmod := le_grow hμ hs h0 h1 hadd hmul ((Nat.mod_le r μ).trans hr)
    rw [grow, Nat.log_of_lt (Nat.mod_lt r (by omega))] at hmod
    simp only [CharP.cast_eq_zero, zero_add, mul_one, pow_zero] at hmod
    have h4 := hadd (μ * (r / μ)) (r % μ) ((Nat.div_add_mod r μ).symm ▸ hr)
    rw [Nat.div_add_mod] at h4
    rw [grow] at hdiv
    rw [Nat.log_of_one_lt_of_le (by omega) (by omega)]
    push_cast
    calc D r ≤ s * D (r / μ) + D (r % μ) := by
          linarith [hmul (r / μ) ((Nat.mul_div_le r μ).trans hr)]
      _ ≤ s * (μ * (Nat.log μ (r / μ) + 1) * s ^ Nat.log μ (r / μ) * D 1) +
          μ * D 1 * s ^ (Nat.log μ (r / μ) + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hdiv (by linarith))
          (hmod.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hs)))
      _ = _ := by ring
termination_by r
decreasing_by
  · exact Nat.div_lt_self (by omega) (by omega)
  · exact (Nat.mod_lt r (by omega)).trans_le (by omega)

/-- **Lemma F.1** (p. 38): for a homomorphism `τ` from `Mat_k(F₂)` into a group with a
contracting length, `D(r) ≤ μ(j + 1)s^j D(1)`, `j = ⌊log_μ r⌋`, where `D(r)²` is the mean of
`|τ W|²` over rank `r`. -/
private theorem sqrt_rankMean_le {G : Type*} [Group G] (l : Len G) {μ : ℕ} {s : ℝ} (hμ : 2 ≤ μ)
    (hs : 1 ≤ s) (hl : Contr l μ s) {k : ℕ} (τ : Mt k → G) (hτ : ∀ M N, τ (M + N) = τ M * τ N)
    {r : ℕ} (hr : r ≤ k) :
    √(rankMean (fun W => l (τ W)) r) ≤ grow μ s r * √(rankMean (fun W => l (τ W)) 1) := by
  have hgood := good_of_contr l hl τ hτ
  have hg : (0 : ℝ) < Fintype.card (GLM (Fin k)) := by exact_mod_cast Fintype.card_pos
  have hsq : ∀ S : Finset (Fin k), √(DM (fun W => l (τ W)) (dg S)) =
      Fintype.card (GLM (Fin k)) * √(rankMean (fun W => l (τ W)) S.card) := fun S => by
    rw [DM_dg_eq, Real.sqrt_mul (by positivity), Real.sqrt_sq hg.le]
  refine le_grow (D := fun r => √(rankMean (fun W => l (τ W)) r)) hμ hs ?_ (Real.sqrt_nonneg _)
    (fun i j hij => ?_) (fun i hi => ?_) hr
  · have h := hgood.dg_zero
    rw [DM_dg_eq, card_empty, mul_eq_zero] at h
    simp [h.resolve_left (by positivity)]
  · obtain ⟨S, -, T, -, hST, rfl, rfl⟩ :=
      exists_disjoint_card_eq (s := (univ : Finset (Fin k))) (by simpa using hij)
    have h := DM_dg_le _ hgood.nonneg hgood.add hST
    rw [hsq, hsq, hsq, card_union_of_disjoint hST, ← mul_add] at h
    exact le_of_mul_le_mul_left h hg
  · let e : Fin μ × Fin i ↪ Fin k := finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb hi)
    have h := hgood.digit i e ⟨0, by omega⟩
    rw [DM_dg_eq, DM_dg_eq, card_map, card_map, card_univ, card_product, card_singleton,
      card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, one_mul, mul_left_comm,
      mul_le_mul_iff_right₀ (by positivity)] at h
    rw [← Real.sqrt_sq (by linarith : 0 ≤ s), ← Real.sqrt_mul (sq_nonneg s)]
    exact Real.sqrt_le_sqrt h

/-! ### Lemma F.2: elements of rank one -/

/-- **Lemma F.2** (p. 38), in the form of the source: an element `1 + u φᵀ` of `U n` with `u`
supported before `k` and `φ` from `k` on has length at most `18 ∑_j |x_j|`. Let `a` be the last
index with `u a ≠ 0`; Lemma `Flag.lead_le` treats `φ` with `φ (a + 1) = 1`, and otherwise
`φ = (φ + e_{a+1}) + e_{a+1}` gives a product of two such elements. -/
private theorem len_le_of_vecMulVec {n : ℕ} (l : Len (U n)) (k : ℕ) {u φ : Fin n → F2}
    (hu : ∀ i, u i ≠ 0 → i.1 < k) (hφ : ∀ j, φ j ≠ 0 → k ≤ j.1) (A : U n)
    (hA : mat A = 1 + vecMulVec u φ) : l A ≤ 18 * l.S := by
  have f2 : ∀ c : F2, c ≠ 0 → c = 1 := by decide
  have hS := l.S_nonneg
  by_cases h0 : (∃ i, u i ≠ 0) ∧ ∃ j, φ j ≠ 0
  swap
  · have : A = 1 := mat_inj <| by
      ext i j
      rcases not_and_or.1 h0 with h0 | h0 <;> push Not at h0 <;>
        simp [hA, mat_one, vecMulVec_apply, h0]
    rw [this, map_one_eq_zero]
    linarith
  obtain ⟨⟨i0, hi0⟩, j0, hj0⟩ := h0
  obtain ⟨a, ha, hmax⟩ := exists_max_image (univ.filter fun i => u i ≠ 0) id
    ⟨i0, by simpa using hi0⟩
  have ha0 : u a ≠ 0 := (mem_filter.1 ha).2
  have hak := hu a ha0
  have hjk := hφ j0 hj0
  set j : Fin (n - 1) := ⟨a.1, by omega⟩
  have hu' : ∀ i, lo j < i → u i = 0 := fun i hi => by
    by_contra h
    exact absurd (hmax i (by simpa using h)) (not_le.2 hi)
  have hz : ∀ (ψ : Fin n → F2), (∀ i, i < hi j → ψ i = 0) → ∀ i c, c ≤ i → u i * ψ c = 0 :=
    fun ψ hψ i c hci => by
      by_cases h : u i = 0
      · rw [h, zero_mul]
      · rw [hψ c (lt_of_le_of_lt hci ((not_lt.1 fun hi => h (hu' i hi)).trans_lt
          (Cslib.SLTower.lo_lt_hi j))), mul_zero]
  have hφ' : ∀ i, i < hi j → φ i = 0 := fun i hlt => by
    by_contra h
    exact absurd (hφ i h) (by have : i.1 < a.1 + 1 := Fin.lt_def.1 hlt; omega)
  -- `1 + u ψᵀ` is an element of length at most `9 ∑_j |x_j|`
  have key : ∀ ψ : Fin n → F2, (∀ i, i < hi j → ψ i = 0) → ψ (hi j) = 1 →
      ∃ B : U n, mat B = 1 + vecMulVec u ψ ∧ l B ≤ 9 * l.S := fun ψ h1 h2 =>
    ⟨mk (1 + vecMulVec u ψ) (fun i c hci => by
        rw [Matrix.add_apply, one_apply_ne hci.ne', vecMulVec_apply, hz ψ h1 i c hci.le, add_zero])
      (fun i => by
        rw [Matrix.add_apply, one_apply_eq, vecMulVec_apply, hz ψ h1 i i le_rfl, add_zero]),
      rfl, lead_le l j u ψ (f2 _ ha0) hu' h2 h1 _ rfl⟩
  by_cases hb : φ (hi j) = 0
  · have he : ∀ i, i < hi j → (Pi.single (hi j) 1 : Fin n → F2) i = 0 := fun i hi =>
      Pi.single_eq_of_ne hi.ne _
    obtain ⟨B, hB, hlB⟩ := key ((Pi.single (hi j) 1 : Fin n → F2)) he (Pi.single_eq_same _ _)
    obtain ⟨C, hC, hlC⟩ := key (φ + (Pi.single (hi j) 1 : Fin n → F2))
      (fun i hi => by rw [Pi.add_apply, hφ' i hi, he i hi, add_zero])
      (by rw [Pi.add_apply, hb, Pi.single_eq_same, zero_add])
    have hBC : A = B * C := mat_inj <| by
      rw [mat_mul, hA, hB, hC, add_mul, one_mul, mul_add, mul_one, vecMulVec_mul_vecMulVec,
        show (Pi.single (hi j) 1 : Fin n → F2) ⬝ᵥ u = 0 by
          simp [hu' _ (Cslib.SLTower.lo_lt_hi j)],
        zero_smul, vecMulVec_zero, add_zero, add_assoc, ← vecMulVec_add, add_assoc, vadd_self,
        add_zero]
    rw [hBC]
    linarith [map_mul_le_add l B C]
  · linarith [lead_le l j u φ (f2 _ ha0) hu' (f2 _ hb) hφ' A hA]

/-- Lemma F.2 for the elements `up (u φᵀ)` of the upper right block. -/
private theorem len_up_le {a b : ℕ} (l : Len (U (a + b))) (u : Fin a → F2) (φ : Fin b → F2) :
    l (up (vecMulVec u φ)) ≤ 18 * l.S := by
  refine len_le_of_vecMulVec l a (u := wl a b *ᵥ u) (φ := wr a b *ᵥ φ) (fun i hi => ?_)
    (fun i hi => ?_) _ (by rw [mat_up, mul_vecMulVec, vecMulVec_mul, vecMul_transpose])
  all_goals
    by_contra h
    apply hi
    simp only [mulVec, dotProduct]
    refine sum_eq_zero fun c _ => ?_
    simp only [incl_apply, weEmb_apply, we, Fin.ext_iff]
    split_ifs <;> simp_all

/-! ### Lemma F.3: the mean length on `U_n` -/

/-- The constant `ϑ_n` of Lemma F.3: `18 i μ(d + 1)s^d` for `i = ⌈log₂ n⌉` and
`d = ⌊log_μ 2^i⌋`. -/
@[expose] noncomputable def kappa (μ : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  18 * Nat.clog 2 n * grow μ s (2 ^ Nat.clog 2 n)

variable {μ : ℕ} {s : ℝ}

/-- By Lemmas F.1 and F.2, the elements `up M` of the upper right block have mean square length
at most `(18 μ(d + 1)s^d ∑_j |x_j|)²`. -/
private theorem sum_len_up_le {a : ℕ} (l : Len (U (a + a))) (hμ : 2 ≤ μ) (hs : 1 ≤ s)
    (hl : Contr l μ s) :
    ∑ M : Mt a, l (up M) ^ 2 ≤ Fintype.card (Mt a) * (grow μ s a * (18 * l.S)) ^ 2 := by
  have hS := l.S_nonneg
  have h1 : √(rankMean (fun M => l (up M)) 1) ≤ 18 * l.S := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, div_le_of_le_mul₀ (Nat.cast_nonneg _)
      (sq_nonneg _) ?_⟩
    rw [mul_comm, ← nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun W hW => pow_le_pow_left₀ (apply_nonneg l _) ?_ 2
    obtain ⟨p, q, T, rfl⟩ := exists_X W
    obtain ⟨i, rfl⟩ := card_eq_one.1 ((rank_X p q T).symm.trans (mem_filter.1 hW).2)
    rw [X_singleton]
    exact len_up_le l _ _
  have h2 : ∀ r ≤ a, rankMean (fun M => l (up M)) r ≤ (grow μ s a * (18 * l.S)) ^ 2 :=
    fun r hr => by
      rw [← Real.sq_sqrt (rankMean_nonneg _ r)]
      refine pow_le_pow_left₀ (Real.sqrt_nonneg _) ((sqrt_rankMean_le l hμ hs hl _ up_add hr).trans
        ?_) 2
      exact mul_le_mul (grow_mono μ hs hr) h1 (Real.sqrt_nonneg _) (grow_nonneg μ hs a)
  have hmap : ∀ M ∈ (univ : Finset (Mt a)), M.rank ∈ range (a + 1) := fun M _ =>
    mem_range.2 (Nat.lt_succ_of_le ((rank_le_card_width M).trans (Fintype.card_fin a).le))
  rw [← sum_fiberwise_of_maps_to hmap, ← card_univ, card_eq_sum_card_fiberwise hmap,
    Nat.cast_sum, sum_mul]
  refine sum_le_sum fun r hr => ?_
  have h := h2 r (Nat.lt_succ_iff.1 (mem_range.1 hr))
  rcases (#{M : Mt a | M.rank = r}).eq_zero_or_pos with h0 | h0
  · simp [card_eq_zero.1 h0]
  · rwa [rankMean, div_le_iff₀ (by exact_mod_cast h0), mul_comm] at h

/-- The induction step of Lemma F.3: "A uniformly distributed element of `U_n` is the product of
a uniformly distributed element of the abelian upper right block, … and of uniformly distributed
elements of the two diagonal blocks", which use disjoint sets of generators. -/
private theorem bd_add_self (hμ : 2 ≤ μ) (hs : 1 ≤ s) {a : ℕ} {κ : ℝ} (h : Bd μ s a κ)
    (hκ : 0 ≤ κ) : Bd μ s (a + a) (18 * grow μ s a + κ) := by
  intro l hC
  set A := l.comp (win (hl (a := a) (b := a)))
  set B := l.comp (win (hr (a := a) (b := a)))
  have hg := grow_nonneg μ hs a
  have hS0 := l.S_nonneg
  set N : ℝ := (Fintype.card (U a × Mt a × U a) : ℝ)
  have hN : 0 < N := by simp only [N]; exact_mod_cast Fintype.card_pos
  have hcU : (0 : ℝ) < Fintype.card (U a) := by exact_mod_cast Fintype.card_pos
  have key := three_le (fun t => l (blk t)) (fun t => B t.2.2) (fun t => l (up t.2.1))
    (fun t => A t.1) (fun _ => apply_nonneg l _) (fun _ => apply_nonneg l _)
    (fun _ => apply_nonneg A _) fun ⟨A', M, C⟩ =>
      (map_mul_le_add l (win hr C * up M) (win hl A')).trans <| by
        change _ ≤ l (win hr C) + (l (up M) + l (win hl A'))
        linarith [map_mul_le_add l (win hr C) (up M)]
  -- each sum is `N` times a mean square
  have hsq : ∀ (S r : ℝ), 0 ≤ r → S = N * r ^ 2 → √S = √N * r := fun S r hr e => by
    rw [e, Real.sqrt_mul hN.le, Real.sqrt_sq hr]
  have e0 : √(∑ t : U a × Mt a × U a, l (blk t) ^ 2) = √N * l.rms :=
    hsq _ _ (Len.rms_nonneg _) <| by
      rw [blk_bijective.sum_comp (fun g => l g ^ 2), Len.rms_sq,
        ← Fintype.card_of_bijective (blk_bijective (a := a) (b := a))]
      simp only [N]; field_simp
  have eA : √(∑ t : U a × Mt a × U a, A t.1 ^ 2) = √N * Len.rms A :=
    hsq _ _ (Len.rms_nonneg _) <| by
      simp only [Len.rms_sq, Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul,
        ← mul_sum, N, Fintype.card_prod, Nat.cast_mul]; field_simp
  have eB : √(∑ t : U a × Mt a × U a, B t.2.2 ^ 2) = √N * Len.rms B :=
    hsq _ _ (Len.rms_nonneg _) <| by
      simp only [Len.rms_sq, Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul,
        N, Fintype.card_prod, Nat.cast_mul]; field_simp
  have eM : √(∑ t : U a × Mt a × U a, l (up t.2.1) ^ 2) ≤ √N * (grow μ s a * (18 * l.S)) := by
    rw [← hsq _ _ (by positivity) rfl]
    refine Real.sqrt_le_sqrt ?_
    simp only [Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul, N, Fintype.card_prod,
      Nat.cast_mul, ← mul_sum]
    calc _ ≤ (Fintype.card (U a) : ℝ) * ((Fintype.card (U a) : ℝ) *
            (Fintype.card (Mt a) * (grow μ s a * (18 * l.S)) ^ 2)) := by
          gcongr; exact sum_len_up_le l hμ hs hC
      _ = _ := by ring
  rw [e0, eA, eB] at key
  have h1 : l.rms ≤ Len.rms B + (grow μ s a * (18 * l.S) + Len.rms A) :=
    le_of_mul_le_mul_left (by linarith) (Real.sqrt_pos.2 hN)
  have hS := mul_le_mul_of_nonneg_left (S_add_le l) hκ
  rw [mul_add] at hS
  linarith [h A (hC.comp _), h B (hC.comp _)]

/-- **Lemma F.3** (p. 38): every contracting length on `U_n` has root mean square length at most
`kappa μ s n ∑_j |x_j|`. The proof treats `n = 2^i` by induction (`bd_add_self`), and `U_n` is a
quotient of `U_{2^i}`, `n ≤ 2^i`, with generators going to generators or to `1`. -/
theorem bd_kappa (hμ : 2 ≤ μ) (hs : 1 ≤ s) (n : ℕ) : Bd μ s n (kappa μ s n) := by
  have hpow : ∀ i : ℕ, Bd μ s (2 ^ i) (18 * i * grow μ s (2 ^ i)) := fun i => by
    induction i with
    | zero => simpa using bd_one μ s
    | succ i ih =>
      have h := bd_add_self hμ hs ih (by have := grow_nonneg μ hs (2 ^ i); positivity)
      rw [← two_mul, ← pow_succ'] at h
      intro l hl
      refine (h l hl).trans (mul_le_mul_of_nonneg_right ?_ l.S_nonneg)
      have := grow_mono μ hs (Nat.pow_le_pow_right (n := 2) (by norm_num) (Nat.le_succ i))
      have : 18 * (i : ℝ) * grow μ s (2 ^ i) ≤ 18 * i * grow μ s (2 ^ (i + 1)) := by gcongr
      push_cast
      linarith
  exact bd_mono (Nat.le_pow_clog one_lt_two n)
    (by have := grow_nonneg μ hs (2 ^ Nat.clog 2 n); unfold kappa; positivity) (hpow _)

/-- "Since `C(n) = o(n²)`, there is `u ≥ 2` with `4 C(3u) ≤ (u − 1)²/32²`", for
`C(n) = κ_n² n` (proof of Theorem F.6, p. 40). With `ρ = s²/μ < 1` and `d = ⌊log_μ 2^i⌋`,
`κ_n² n ≤ 648 μ⁴ (d + 1)⁴ ρ^d n²`, and `(d + 1)⁴ ρ^d → 0`. -/
theorem exists_kappa_le (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) :
    ∃ u : ℕ, 2 ≤ u ∧
      4 * (kappa μ s (3 * u) ^ 2 * (3 * u : ℕ)) ≤ (1 / 32) ^ 2 * ((u : ℝ) - 1) ^ 2 := by
  have hm0 : (0 : ℝ) < μ := by exact_mod_cast (by omega : 0 < μ)
  set ρ : ℝ := s ^ 2 / μ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := (div_lt_one hm0).2 hsm
  set ε : ℝ := 1 / (2 ^ 30 * μ ^ 4)
  obtain ⟨L₀, hL₀⟩ := exists_log_large hρ0 hρ1 (show 0 < ε by positivity)
  refine ⟨μ ^ L₀ + 2, by omega, ?_⟩
  set n := 3 * (μ ^ L₀ + 2)
  set i := Nat.clog 2 n
  set L := Nat.log μ (2 ^ i)
  have hni : n ≤ 2 ^ i := Nat.le_pow_clog one_lt_two n
  have hi2 : 2 ^ i ≤ 2 * n := by
    have hi0 : 0 < i := Nat.clog_pos one_lt_two (by omega)
    have h : 2 ^ i.pred < n := Nat.pow_pred_clog_lt_self one_lt_two (by omega)
    rw [← Nat.succ_pred_eq_of_pos hi0, pow_succ']; omega
  have hLL : L₀ ≤ L := Nat.le_log_of_pow_le (by omega) (by omega)
  have hiL : (i : ℝ) ≤ μ * ((L : ℝ) + 1) := by
    have h1 : 2 ^ i < 2 ^ (μ * (L + 1)) :=
      calc 2 ^ i < μ ^ (L + 1) := Nat.lt_pow_succ_log_self (by omega) _
        _ ≤ (2 ^ μ) ^ (L + 1) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
        _ = 2 ^ (μ * (L + 1)) := by rw [← pow_mul]
    exact_mod_cast ((Nat.pow_lt_pow_iff_right (by norm_num)).1 h1).le
  have hmL : (μ : ℝ) ^ L ≤ 2 * n := by
    exact_mod_cast (Nat.pow_log_le_self μ (Nat.two_pow_pos i).ne').trans hi2
  have hk : kappa μ s n ^ 2 ≤ 648 / 2 ^ 30 * n := by
    have e0 : (s ^ L) ^ 2 = ρ ^ L * (μ : ℝ) ^ L := by
      rw [← mul_pow, div_mul_cancel₀ _ hm0.ne', ← pow_mul, ← pow_mul, mul_comm]
    have e : kappa μ s n ^ 2 = 324 * (i : ℝ) ^ 2 * ((μ : ℝ) ^ 2 * ((L : ℝ) + 1) ^ 2 *
        (ρ ^ L * (μ : ℝ) ^ L)) := by
      rw [kappa, grow, ← e0]; ring
    calc kappa μ s n ^ 2
        ≤ 324 * ((μ : ℝ) * ((L : ℝ) + 1)) ^ 2 * ((μ : ℝ) ^ 2 * ((L : ℝ) + 1) ^ 2 *
            (ρ ^ L * (2 * n))) := by rw [e]; gcongr
      _ = 648 * (μ : ℝ) ^ 4 * (((L : ℝ) + 1) ^ 4 * ρ ^ L) * n := by ring
      _ ≤ 648 * (μ : ℝ) ^ 4 * ε * n := by gcongr; exact hL₀ L hLL
      _ = 648 / 2 ^ 30 * n := by simp only [ε]; field_simp
  set u : ℝ := ((μ ^ L₀ + 2 : ℕ) : ℝ)
  have hn : (n : ℝ) = 3 * u := by simp [n, u]
  have hu : 2 ≤ u := by simp only [u]; exact_mod_cast (by omega : 2 ≤ μ ^ L₀ + 2)
  calc 4 * (kappa μ s n ^ 2 * (n : ℝ))
      ≤ 4 * (648 / 2 ^ 30 * n * n) := by gcongr
    _ = 23328 / 2 ^ 30 * u ^ 2 := by rw [hn]; ring
    _ ≤ (1 / 32) ^ 2 * (u - 1) ^ 2 := by
      have hsq : 0 ≤ (u - 2) * (3 * u - 2) := mul_nonneg (by linarith) (by linarith)
      have hexp : (u - 2) * (3 * u - 2) = 3 * u ^ 2 - 8 * u + 4 := by ring
      linarith

end Cslib.Circuits.Arithmetic.Separation.Poincare
