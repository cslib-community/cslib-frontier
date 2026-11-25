/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.WindowMean
public import Mathlib.Analysis.Normed.Group.Seminorm
public import Mathlib.Analysis.Subadditive

/-!
# Length functions on `ℤ²` with the crossing inequality

From *VP ≠ VNP over every field* [AnthropicVPVNP2026] (modules `Nc.Cat.Len` and `Nc.Cat.Length`).

A *crossing length* is an even subadditive function `N ≥ 0` on `ℤ²` with the crossing inequality
(Q) of the paper: for all `X, V, Y, U, n, n', k, k'` and `τ > 0`,
`2(N(X−V)² + N(Y−U)²) ≤ N(X−V)(N(X−n) + N(V−n') + N(X−k) + N(V−k'))
  + N(Y−U)(N(Y−n) + N(U−n') + N(U−k) + N(Y−k')) + τ(N(X−V)² + N(Y−U)²)
  + (N(n−n')² + N(k−k')²)/(2τ)`.

Two sources of crossing lengths are proved here. Every crossing length has a homogeneous version,
its
homogenization `h ↦ lim N(S • h)/S` (`Separation.CrossingLength.homogenization`, with
`Separation.CrossingLength.tendsto_homogenization`). And a family of
pseudometrics on `ℤ²`, Lipschitz with one constant and satisfying a pointwise form of (Q)
(`Separation.CrossingMetrics`), gives the crossing length
`h ↦ ‖P ↦ W(P, P + h)‖`, the root mean square over large windows
(`Separation.CrossingMetrics.crossingLength`).

## Main definitions

* `Separation.CrossingLength N`: `N` is a crossing length.
* `Separation.IsHomogeneous N`: `N(m • h) = m N(h)` for natural `m`.
* `Separation.CrossingLength.toAddGroupSeminorm`: the seminorm part, as Mathlib's
  `AddGroupSeminorm`.
* `Separation.CrossingLength.homogenization`: the canonical homogenization `lim N(S • h)/S`.
* `Separation.CrossingMetrics W Λ`: Lipschitz pseudometrics with the pointwise inequality (Q).
* `Separation.meanLength W h`: the root mean square of `W(P, P + h)`.
-/

public section

open Filter Topology Finset

namespace Cslib.Circuits.Arithmetic.Separation

/-- *Crossing lengths*: even subadditive functions `N ≥ 0` on `ℤ²` with `N 0 = 0` and the
crossing inequality (Q). -/
structure CrossingLength (N : ℤ × ℤ → ℝ) : Prop where
  nonneg : ∀ h, 0 ≤ N h
  zero : N 0 = 0
  neg : ∀ h, N (-h) = N h
  add : ∀ h h', N (h + h') ≤ N h + N h'
  crossing : ∀ X V Y U n n' k k' : ℤ × ℤ, ∀ τ : ℝ, 0 < τ →
    2 * (N (X - V) ^ 2 + N (Y - U) ^ 2) ≤
      N (X - V) * (N (X - n) + N (V - n') + N (X - k) + N (V - k'))
      + N (Y - U) * (N (Y - n) + N (U - n') + N (U - k) + N (Y - k'))
      + τ * (N (X - V) ^ 2 + N (Y - U) ^ 2) + (N (n - n') ^ 2 + N (k - k') ^ 2) / (2 * τ)

/-- `N` is homogeneous along the natural numbers. -/
@[expose] def IsHomogeneous (N : ℤ × ℤ → ℝ) : Prop := ∀ (m : ℕ) h, N (m • h) = m * N h

namespace CrossingLength

variable {N : ℤ × ℤ → ℝ}

theorem subadditive (hN : CrossingLength N) (h : ℤ × ℤ) :
    Subadditive fun S : ℕ => N (S • h) := fun m n => by
  simpa only [add_smul] using hN.add _ _

/-- The seminorm part of a crossing length, as Mathlib's `AddGroupSeminorm`. -/
def toAddGroupSeminorm (hN : CrossingLength N) : AddGroupSeminorm (ℤ × ℤ) where
  toFun := N
  map_zero' := hN.zero
  add_le' := hN.add
  neg' := hN.neg

@[simp] theorem coe_toAddGroupSeminorm (hN : CrossingLength N) : ⇑hN.toAddGroupSeminorm = N := by
  rfl

theorem le_sub_add (hN : CrossingLength N) (h h' : ℤ × ℤ) : N h ≤ N (h - h') + N h' := by
  simpa [add_comm] using le_map_add_map_sub hN.toAddGroupSeminorm h h'

theorem sub_le (hN : CrossingLength N) (h h' : ℤ × ℤ) : N (h - h') ≤ N h + N h' := by
  simpa using map_sub_le_add hN.toAddGroupSeminorm h h'

theorem abs_sub_le (hN : CrossingLength N) (h h' : ℤ × ℤ) : |N h - N h'| ≤ N (h - h') := by
  simpa using abs_sub_map_le_sub hN.toAddGroupSeminorm h h'

/-! ### The homogenization -/

/-- `N(S • h)/S ≥ 0`, so the averages are bounded below, as Fekete's lemma needs. -/
private theorem bddBelow_div (hN : CrossingLength N) (h : ℤ × ℤ) :
    BddBelow (Set.range fun S : ℕ => N (S • h) / S) :=
  ⟨0, by rintro _ ⟨S, rfl⟩; exact div_nonneg (hN.nonneg _) (Nat.cast_nonneg _)⟩

/-- The homogenization `h ↦ lim N(S • h)/S` of a crossing length, by Fekete's lemma. -/
noncomputable def homogenization (hN : CrossingLength N) (h : ℤ × ℤ) : ℝ :=
  (hN.subadditive h).lim

/-- `N(S • h)/S` converges to the homogenization. -/
theorem tendsto_homogenization (hN : CrossingLength N) (h : ℤ × ℤ) :
    Tendsto (fun S : ℕ => N (S • h) / S) atTop (𝓝 (hN.homogenization h)) :=
  (hN.subadditive h).tendsto_lim (hN.bddBelow_div h)

/-- The homogenization is homogeneous. -/
theorem isHomogeneous_homogenization (hN : CrossingLength N) :
    IsHomogeneous hN.homogenization := by
  have hT := hN.tendsto_homogenization
  intro m h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h1 := hT ((0 : ℕ) • h)
    simp only [zero_smul, smul_zero, hN.zero, zero_div] at h1
    simpa only [Nat.cast_zero, zero_mul, zero_smul] using tendsto_nhds_unique h1 tendsto_const_nhds
  · have h2 : Tendsto (fun S : ℕ => (m : ℝ) * (N ((S * m) • h) / (S * m : ℕ))) atTop
        (𝓝 (m * hN.homogenization h)) :=
      ((hT h).comp (tendsto_id.atTop_mul_const' hm)).const_mul _
    refine tendsto_nhds_unique (hT (m • h)) (h2.congr fun S => ?_)
    rw [mul_smul, Nat.cast_mul, mul_comm (S : ℝ), ← mul_div_assoc,
      mul_div_mul_left _ _ (by exact_mod_cast hm.ne')]

/-- The homogenization of a crossing length is a crossing length. -/
theorem crossingLength_homogenization (hN : CrossingLength N) :
    CrossingLength hN.homogenization := by
  have hT := hN.tendsto_homogenization
  refine ⟨fun h => ge_of_tendsto' (hT h) fun S => div_nonneg (hN.nonneg _) (Nat.cast_nonneg _),
    by simpa using hN.isHomogeneous_homogenization 0 0,
    fun h => tendsto_nhds_unique (hT (-h)) ((hT h).congr fun S => by rw [smul_neg, hN.neg]),
    fun h h' => le_of_tendsto_of_tendsto' (hT (h + h')) ((hT h).add (hT h')) fun S => by
      rw [smul_add, ← add_div]
      exact div_le_div_of_nonneg_right (hN.add _ _) (Nat.cast_nonneg _),
    fun X V Y U n n' k k' τ hτ => ?_⟩
  -- (Q) for `N(S • ·)/S` is (Q) for `N` at the points `S • ·`, divided by `S²`
  have hl := (((hT (X - V)).pow 2).add ((hT (Y - U)).pow 2)).const_mul 2
  have hr := (((((hT (X - V)).mul ((((hT (X - n)).add (hT (V - n'))).add (hT (X - k))).add
    (hT (V - k')))).add ((hT (Y - U)).mul ((((hT (Y - n)).add (hT (U - n'))).add
    (hT (U - k))).add (hT (Y - k')))))).add ((((hT (X - V)).pow 2).add
    ((hT (Y - U)).pow 2)).const_mul τ)).add ((((hT (n - n')).pow 2).add
    ((hT (k - k')).pow 2)).div_const (2 * τ))
  refine le_of_tendsto_of_tendsto' hl hr fun S => ?_
  have h := hN.crossing (S • X) (S • V) (S • Y) (S • U) (S • n) (S • n') (S • k) (S • k') τ hτ
  simp only [← smul_sub] at h
  rcases Nat.eq_zero_or_pos S with rfl | hS
  · simp
  · have hS' : (0 : ℝ) < S := by exact_mod_cast hS
    have h2 := div_le_div_of_nonneg_right h (sq_nonneg (S : ℝ))
    refine le_trans (le_of_eq ?_) (h2.trans (le_of_eq ?_)) <;> field_simp

/-- The homogenization lies below the crossing length. -/
theorem homogenization_le (hN : CrossingLength N) (h : ℤ × ℤ) : hN.homogenization h ≤ N h := by
  simpa [homogenization] using (hN.subadditive h).lim_le_div (hN.bddBelow_div h) one_ne_zero

/-- The homogenization lies above every `c` with `c S ≤ N(S • h)` for all `S > 0`. -/
theorem le_homogenization (hN : CrossingLength N) {h : ℤ × ℤ} {c : ℝ}
    (hc : ∀ S : ℕ, 0 < S → c * S ≤ N (S • h)) : c ≤ hN.homogenization h :=
  ge_of_tendsto (hN.tendsto_homogenization h) <|
    (eventually_gt_atTop 0).mono fun S hS => (le_div_iff₀ (by exact_mod_cast hS)).2 (hc S hS)

end CrossingLength

/-! ### Crossing lengths from mean squares -/

/-- A family of pseudometrics `W n b` on `ℤ²`, one for every window size `n` and sheet `b`,
Lipschitz with one constant `Λ`, with a pointwise form of the crossing inequality (Q). -/
structure CrossingMetrics (W : ℕ → Bool → ℤ × ℤ → ℤ × ℤ → ℝ) (Λ : ℝ) : Prop where
  nonneg : ∀ n b P P', 0 ≤ W n b P P'
  self : ∀ n b P, W n b P P = 0
  symm : ∀ n b P P', W n b P P' = W n b P' P
  triangle : ∀ n b P P' P'', W n b P P'' ≤ W n b P P' + W n b P' P''
  lipschitz : ∀ n b (P h : ℤ × ℤ), W n b P (P + h) ≤ Λ * (|(h.1 : ℝ)| + |(h.2 : ℝ)|)
  crossing : ∀ n b (X V Y U m m' k k' : ℤ × ℤ) (p q τ : ℝ), 0 ≤ p → 0 ≤ q → 0 < τ →
    2 * (p * W n b X V + q * W n b Y U) ≤
      p * (W n b X m + W n b V m' + W n b X k + W n b V k')
      + q * (W n b Y m + W n b U m' + W n b U k + W n b Y k')
      + τ * (p ^ 2 + q ^ 2) + (W n b m m' ^ 2 + W n b k k' ^ 2) / (2 * τ)

variable {W : ℕ → Bool → ℤ × ℤ → ℤ × ℤ → ℝ} {Λ : ℝ}

/-- The distance of the translates `P + u` and `P + v`, as a window function of `P`. -/
@[expose] def translateDist (W : ℕ → Bool → ℤ × ℤ → ℤ × ℤ → ℝ) (u v : ℤ × ℤ) : WindowFn :=
  fun n b i k => W n b ((i, k) + u) ((i, k) + v)

/-- The root mean square of the distances of `P` and `P + h`. -/
@[expose] noncomputable def meanLength (W : ℕ → Bool → ℤ × ℤ → ℤ × ℤ → ℝ) (h : ℤ × ℤ) : ℝ :=
  (translateDist W 0 h).rms

namespace CrossingMetrics

open WindowFn

variable (H : CrossingMetrics W Λ)
include H

theorem bounded (u v : ℤ × ℤ) : (translateDist W u v).Bounded := by
  refine ⟨Λ * (|((v - u).1 : ℝ)| + |((v - u).2 : ℝ)|), fun n b i k => ?_⟩
  rw [translateDist, abs_of_nonneg (H.nonneg _ _ _ _)]
  simpa only [add_assoc, add_sub_cancel] using H.lipschitz n b ((i, k) + u) (v - u)

theorem rms_translateDist (u v : ℤ × ℤ) : (translateDist W u v).rms = meanLength W (u - v) := by
  have h1 : translateDist W u v =
      fun n b i k => translateDist W 0 (u - v) n b (i + v.1) (k + v.2) := by
    funext n b i k
    rw [translateDist, H.symm, translateDist, add_zero]
    congr 1
    ext <;> simp
  rw [h1, rms_shift (H.bounded _ _)]
  rfl

theorem rms_translateDist' (u v : ℤ × ℤ) :
    (translateDist W u v).rms = meanLength W (v - u) := by
  rw [← H.rms_translateDist v u]
  congr 1
  funext n b i k
  exact H.symm _ _ _ _

theorem meanLength_zero : meanLength W 0 = 0 := by
  have : translateDist W 0 0 * translateDist W 0 0 = fun _ _ _ _ => (0 : ℝ) := by
    funext n b i k
    simp [translateDist, H.self]
  rw [meanLength, rms, this, mean_const, Real.sqrt_zero]

/-- By translation invariance the root mean square is even. -/
theorem meanLength_neg (h : ℤ × ℤ) : meanLength W (-h) = meanLength W h := by
  rw [← zero_sub, ← H.rms_translateDist 0 h]
  rfl

/-- By translation invariance and Minkowski's inequality the root mean square is subadditive. -/
theorem meanLength_add (h h' : ℤ × ℤ) :
    meanLength W (h + h') ≤ meanLength W h + meanLength W h' := by
  refine (rms_mono (H.bounded 0 (h + h')) ((H.bounded 0 h).add (H.bounded h (h + h')))
    (fun _ _ _ _ => H.nonneg _ _ _ _)
    (Eventually.of_forall fun _ _ _ _ _ _ => H.triangle _ _ _ _ _)).trans ?_
  simpa only [meanLength, H.rms_translateDist' h, add_sub_cancel_left] using
    rms_add_le (H.bounded 0 h) (H.bounded h (h + h'))

/-- By the inequality of Cauchy and Schwarz the root mean square satisfies (Q). -/
theorem meanLength_crossing (X V Y U m m' k k' : ℤ × ℤ) (τ : ℝ) (hτ : 0 < τ) :
    2 * (meanLength W (X - V) ^ 2 + meanLength W (Y - U) ^ 2) ≤
      meanLength W (X - V) * (meanLength W (X - m) + meanLength W (V - m')
        + meanLength W (X - k) + meanLength W (V - k'))
      + meanLength W (Y - U) * (meanLength W (Y - m) + meanLength W (U - m')
        + meanLength W (U - k) + meanLength W (Y - k'))
      + τ * (meanLength W (X - V) ^ 2 + meanLength W (Y - U) ^ 2)
      + (meanLength W (m - m') ^ 2 + meanLength W (k - k') ^ 2) / (2 * τ) := by
  have hb := H.bounded
  set d := translateDist W
  have hbm : ∀ a b c e, (d a b * d c e).Bounded := fun _ _ _ _ => (hb _ _).mul (hb _ _)
  have key : mean ((2 : ℝ) • (d X V * d X V + d Y U * d Y U)) ≤
      mean (d X V * d X m + d X V * d V m' + d X V * d X k + d X V * d V k'
        + (d Y U * d Y m + d Y U * d U m' + d Y U * d U k + d Y U * d Y k')
        + τ • (d X V * d X V + d Y U * d Y U)
        + (1 / (2 * τ)) • (d m m' * d m m' + d k k' * d k k')) := by
    refine mean_le ?_ ?_ fun n b i j => ?_
    · repeat' first | exact hbm _ _ _ _ | apply Bounded.smul | apply Bounded.add
    · repeat' first | exact hbm _ _ _ _ | apply Bounded.smul | apply Bounded.add
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, d, translateDist]
    have h := H.crossing n b ((i, j) + X) ((i, j) + V) ((i, j) + Y) ((i, j) + U) ((i, j) + m)
      ((i, j) + m') ((i, j) + k) ((i, j) + k') _ _ τ (H.nonneg n b ((i, j) + X) ((i, j) + V))
      (H.nonneg n b ((i, j) + Y) ((i, j) + U)) hτ
    rw [one_div, inv_mul_eq_div]
    simp only [pow_two] at h
    linarith
  rw [mean_smul, mean_add, mean_add, mean_add, mean_add, mean_add, mean_add, mean_add, mean_add,
    mean_add, mean_add, mean_smul, mean_smul, mean_add, mean_add,
    ← rms_sq (hb X V), ← rms_sq (hb Y U), ← rms_sq (hb m m'), ← rms_sq (hb k k'),
    H.rms_translateDist, H.rms_translateDist, H.rms_translateDist, H.rms_translateDist,
    one_div, inv_mul_eq_div] at key
  · have cs : ∀ a b c e : ℤ × ℤ,
        mean (d a b * d c e) ≤ meanLength W (a - b) * meanLength W (c - e) := fun _ _ _ _ => by
      rw [← H.rms_translateDist, ← H.rms_translateDist]
      exact mean_mul_le (hb _ _) (hb _ _)
    linarith [cs X V X m, cs X V V m', cs X V X k, cs X V V k',
      cs Y U Y m, cs Y U U m', cs Y U U k, cs Y U Y k']
  all_goals repeat' first | exact hbm _ _ _ _ | apply Bounded.smul | apply Bounded.add

/-- The root mean square of a family of crossing metrics is a crossing length. -/
theorem crossingLength : CrossingLength (meanLength W) where
  nonneg _ := rms_nonneg _
  zero := H.meanLength_zero
  neg := H.meanLength_neg
  add := H.meanLength_add
  crossing := H.meanLength_crossing

end CrossingMetrics

end Cslib.Circuits.Arithmetic.Separation
