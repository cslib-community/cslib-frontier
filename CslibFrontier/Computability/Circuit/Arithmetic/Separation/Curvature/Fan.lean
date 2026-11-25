/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Price.Basic
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Means
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Window
import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Price.Random
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Prices are nonpositively curved: the CN inequality

Theorem C.1 of *VP ≠ VNP over every field* [AnthropicVPVNP2026]. Let `x, v, m, z` be points of a
price `w` with `w(x, m), w(v, m) ≤ D` and `w(x, v) = 2D`. Then
`w(z, m)² ≤ ½ w(z, x)² + ½ w(z, v)² - D²` (`isPrice_sq_le_of_mid`).

The proof follows the paper. A *fan* adds to the price two sheets of new points between `x` and
`v`, built with random points (Proposition A.8); its distances form prices `W n` on two sheets of
`ℤ²` that are Lipschitz on each sheet. The mean norm `N` of these prices satisfies the
parallelogram law (Lemma C.2, `meanNorm_parallelogram`), and the four claims (i) to (iv) of the
paper bound `N` at the directions of the fan; letting `θ = 1/T` tend to `0` gives the inequality.
The two sheets are indexed by `Bool`; `x true` and `x false` are the paper's `x` and `v`.

## Main results

* `isPrice_sq_le_of_mid`: Theorem C.1.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem C.1 of the paper; module `Paper.Fan` (`thm_cn`)
-/

namespace Cslib.Circuits.Arithmetic.Separation.Curvature

open Finset Filter Topology Cslib.PartyTensor Cslib.Circuits.Arithmetic.Separation
    Cslib.Circuits.Arithmetic.Separation.WindowFn

variable {K : Type} [Field K] {Y : Type} {w : Y → Y → ℝ}

/-- Points at distance 0 have the same distances from all points. -/
theorem dist_congr_of_zero (hw : IsPrice K w) {a b : Y} (h : w a b = 0) (c : Y) : w a c =
    w b c :=
    by
  have h2 := hw.triangle b a c
  rw [hw.symm b a] at h2
  linarith [hw.triangle a b c]

/-- Steps of length at most c add up. -/
theorem dist_chain_le (hw : IsPrice K w) (p : ℕ → Y)
    {c : ℝ} {M : ℕ} (h : ∀ i < M, w (p i) (p (i + 1)) ≤ c)
    (i i' : ℕ) (hi : i ≤ M) (hi' : i' ≤ M) : w (p i) (p i') ≤ |(i : ℝ) - i'| * c := by
  have key : ∀ i l, i + l ≤ M → w (p i) (p (i + l)) ≤ l * c := fun i l => by
    induction l with
    | zero => intro _; simp [hw.self]
    | succ l ih =>
      intro hl
      rw [← add_assoc]
      push_cast
      linarith [hw.triangle (p i) (p (i + l)) (p (i + l + 1)), h (i + l) (by omega), ih (by omega)]
  rcases le_total i i' with hii | hii
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hii
    simpa [Nat.cast_add, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) l)] using key i l hi'
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hii
    rw [hw.symm]
    simpa [Nat.cast_add, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) l)] using key i' l hi

/-- New points on segments, by Proposition A.8: for every q the point (q, j), 0 ≤ j ≤ M, is
placed at b q with
probability j/M and otherwise at a q, with one random number for all. -/
theorem thm_cn_segments (hw : IsPrice K w) {Q : Type} (a b : Q → Y) {M : ℕ} (hM : 0 < M) :
    ∃ w' : Y ⊕ (Q × ℕ) → Y ⊕ (Q × ℕ) → ℝ, IsPrice K w' ∧
      (∀ y y', w' (Sum.inl y) (Sum.inl y') = w y y') ∧
      (∀ q q' j, j ≤ M → w' (Sum.inr (q, j)) (Sum.inr (q', j)) ≤
        (1 - j / M) * w (a q) (a q') + j / M * w (b q) (b q')) ∧
      (∀ q j j', j ≤ j' → j' ≤ M → w' (Sum.inr (q, j)) (Sum.inr (q, j')) ≤
        ((j' : ℝ) - j) / M * w (a q) (b q)) ∧
      (∀ q j, j ≤ M → w' (Sum.inl (a q)) (Sum.inr (q, j)) ≤ j / M * w (a q) (b q)) ∧
      (∀ q j, j ≤ M → w' (Sum.inl (b q)) (Sum.inr (q, j)) ≤ (1 - j / M) * w (a q) (b q)) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨w', h1, h2, h3⟩ := IsPrice.exists_extend_of_weights hw (Λ := Fin M)
    (fun _ => 1 / (M : ℝ)) (fun _ => by positivity) (by simp [hM'.ne'])
    (fun l (κ : Q × ℕ) => if (l : ℕ) < κ.2 then b κ.1 else a κ.1)
  refine ⟨w', h1, h2, fun q q' j hj => (h3 _ _).trans_eq ?_, fun q j j' hjj hj => (h3 _ _).trans ?_,
    fun q j hj => (h3 _ _).trans_eq ?_, fun q j hj => (h3 _ _).trans_eq ?_⟩
  · simp only [Sum.elim_inr, ← Finset.mul_sum]
    have hEq (l : Fin M) : w (if (l : ℕ) < j then b q else a q)
        (if (l : ℕ) < j then b q' else a q') =
        if (l : ℕ) < j then w (b q) (b q') else w (a q) (a q') := by split_ifs <;> rfl
    simp only [hEq, sum_fin_ite_lt hj]
    field_simp
    ring
  · simp only [Sum.elim_inr, ← Finset.mul_sum]
    have h4 := Finset.sum_le_sum fun (l : Fin M) (_ : l ∈ univ) => show
        w (if (l : ℕ) < j then b q else a q) (if (l : ℕ) < j' then b q else a q) ≤
          (if (l : ℕ) < j' then w (a q) (b q) else 0) -
            if (l : ℕ) < j then w (a q) (b q) else 0 by
      split_ifs <;> first | rw [hw.self, sub_self] | omega | rw [sub_zero]
    rw [Finset.sum_sub_distrib, sum_fin_ite_lt hj, sum_fin_ite_lt (hjj.trans hj)] at h4
    refine (mul_le_mul_of_nonneg_left h4 (by positivity)).trans_eq ?_
    field_simp
    ring
  · simp only [Sum.elim_inl, Sum.elim_inr, id, ← Finset.mul_sum]
    have hEq (l : Fin M) : w (a q) (if (l : ℕ) < j then b q else a q) =
        if (l : ℕ) < j then w (a q) (b q) else 0 := by
          split_ifs
          exacts [rfl, hw.self _]
    simp only [hEq, sum_fin_ite_lt hj]
    field_simp
    ring
  · simp only [Sum.elim_inl, Sum.elim_inr, id, ← Finset.mul_sum]
    have hEq (l : Fin M) : w (b q) (if (l : ℕ) < j then b q else a q) =
        if (l : ℕ) < j then 0 else w (a q) (b q) := by
          split_ifs
          exacts [hw.self _, hw.symm _ _]
    simp only [hEq, sum_fin_ite_lt hj]
    field_simp
    ring

/-! ### The fan -/

/-- The points of the fan: the old points, the points γ_i on both sheets, and the points G(i,j) on
both sheets. -/
abbrev FanPts (Y : Type) : Type := (Y ⊕ (Bool × ℕ)) ⊕ ((Bool × ℕ) × ℕ)

namespace FanPts

/-- An old point. -/
def old (y : Y) : FanPts Y := Sum.inl (Sum.inl y)

/-- The point γ_i on the sheet b. -/
def γ (b : Bool) (i : ℕ) : FanPts Y := Sum.inl (Sum.inr (b, i))

/-- The point G(i,j) on the sheet b. -/
def G (b : Bool) (i j : ℕ) : FanPts Y := Sum.inr ((b, i), j)

end FanPts

open FanPts

/-- The fan for a given n, with θ = 1/T, L_i = |zγ_i| and ρ = 1 − jθ/n²: a price d on the old
points, the γ_i and the
G(i,j) that extends w, with the four estimates of the paper,
|γ_iγ_{i+1}| ≤ D/n², |zG(i,j)| = ρL_i, |G(i,j)G(i,j+1)| ≤ θL_i/n², |G(i,j)G(i+1,j)| ≤ ρD/n²,
and with what the text says on the places: γ_0 is at x (at v on the second sheet), γ_{n²} at m,
|G(i,j)γ_i| ≤ (1−ρ)L_i, and
G(n²,j) has distance 0 from its copy on the other sheet. -/
structure IsFan (K : Type) [Field K] (w : Y → Y → ℝ) (x : Bool → Y) (m z : Y) (D : ℝ) (T n : ℕ)
    (d : FanPts Y → FanPts Y → ℝ) : Prop where
  price : IsPrice K d
  old : ∀ a b, d (old a) (old b) = w a b
  γ_zero : ∀ b, d (γ b 0) (FanPts.old (x b)) = 0
  γ_last : ∀ b, d (γ b (n ^ 2)) (FanPts.old m) = 0
  γ_step : ∀ b i, i < n ^ 2 → d (γ b i) (γ b (i + 1)) ≤ D / n ^ 2
  z_G : ∀ b i j,
      j ≤ n ^ 2 * T → d (FanPts.old z) (G b i j) = (1 - j / (n ^ 2 * T)) * d (FanPts.old z) (γ b i)
  G_step_j : ∀ b i j,
      j < n ^ 2 * T → d (G b i j) (G b i (j + 1)) ≤ 1 / T * d (FanPts.old z) (γ b i) / n ^ 2
  G_step_i : ∀ b i j,
      i < n ^ 2 → j ≤ n ^ 2 * T → d (G b i j) (G b (i + 1) j) ≤ (1 - j / (n ^ 2 * T)) * D / n ^ 2
  G_γ : ∀ b i j, j ≤ n ^ 2 * T → d (G b i j) (γ b i) ≤ j / (n ^ 2 * T) * d (FanPts.old z) (γ b i)
  G_last : ∀ j, j ≤ n ^ 2 * T → d (G true (n ^ 2) j) (G false (n ^ 2) j) = 0

/-- **The fan** of the proof of Theorem C.1. For a given n add, by Proposition A.8,
points γ_i, 0 ≤ i ≤ n²,
placed at m with probability i/n² and otherwise at x on the first sheet, at v on the second, with
one random number for all.
Then, by the same proposition, add points G(i,j), 0 ≤ j ≤ Tn², placed at z with probability j/(Tn²)
and otherwise at γ_i,
again with one random number. Then the four estimates hold. -/
theorem thm_cn_fan (hw : IsPrice K w) (x : Bool → Y) (m z : Y)
    {D : ℝ} (hD : ∀ b, w (x b) m ≤ D)
    {T n : ℕ}
    (hT : 0 < T) (hn : 0 < n) : ∃ d : FanPts Y → FanPts Y → ℝ, IsFan K w x m z D T n d := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  obtain ⟨w1, hw1, e1, -, a2, a3, a4⟩ :=
    thm_cn_segments hw x (fun _ : Bool => m) (by positivity : 0 < n ^ 2)
  obtain ⟨w2, hw2, e2, b1, b2, b3, b4⟩ := thm_cn_segments hw1
    (fun q : Bool × ℕ => (Sum.inr q : Y ⊕ (Bool × ℕ))) (fun _ => Sum.inl z)
    (by positivity : 0 < n ^ 2 * T)
  push_cast at a2 a3 a4 b1 b2 b3 b4
  have hx (b : Bool) : w1 (Sum.inr (b, 0)) (Sum.inl (x b)) = 0 := by
    rw [hw1.symm]
    exact le_antisymm (by simpa using a3 b 0 (Nat.zero_le _)) (hw1.nonneg _ _)
  have hm (b : Bool) : w1 (Sum.inr (b, n ^ 2)) (Sum.inl m) = 0 := by
    have h := a4 b (n ^ 2) le_rfl
    push_cast at h
    rw [div_self (by positivity), sub_self, zero_mul] at h
    rw [hw1.symm]
    exact le_antisymm h (hw1.nonneg _ _)
  have hγ (b : Bool) (i : ℕ) (hi : i < n ^ 2) :
      w1 (Sum.inr (b, i)) (Sum.inr (b, i + 1)) ≤ D / n ^ 2 := by
    have h := a2 b i (i + 1) (Nat.le_succ i) hi
    push_cast at h
    rw [add_sub_cancel_left, one_div_mul_eq_div] at h
    exact h.trans (div_le_div_of_nonneg_right (hD b) (by positivity))
  have hρ (j : ℕ) (hj : j ≤ n ^ 2 * T) : 0 ≤ 1 - (j : ℝ) / (n ^ 2 * T) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact_mod_cast hj
  refine ⟨w2, hw2, fun a b => by rw [old, old, e2, e1], fun b => by rw [γ, old, e2, hx],
    fun b => by rw [γ, old, e2, hm],
    fun b i hi => by
      rw [γ, γ, e2]
      exact hγ b i hi,
    fun b i j hj => ?_, fun b i j hj => ?_, fun b i j hi hj => ?_, fun b i j hj => ?_,
    fun j hj => ?_⟩
  · dsimp only [old, γ, G]
    rw [e2, hw1.symm (Sum.inl z)]
    apply le_antisymm (b4 (b, i) j hj)
    have h2 := hw2.triangle (Sum.inl (Sum.inr (b, i))) (Sum.inr ((b, i), j)) (Sum.inl (Sum.inl z))
    rw [e2, hw2.symm (Sum.inr ((b, i), j))] at h2
    linarith [b3 (b, i) j hj]
  · dsimp only [old, γ, G]
    rw [e2, hw1.symm (Sum.inl z)]
    have h := b2 (b, i) j (j + 1) (Nat.le_succ j) hj
    push_cast at h
    rw [add_sub_cancel_left] at h
    exact h.trans_eq (by field_simp)
  · dsimp only [G]
    have h := b1 (b, i) (b, i + 1) j hj
    rw [hw1.self, mul_zero, add_zero] at h
    rw [mul_div_assoc]
    exact h.trans (mul_le_mul_of_nonneg_left (hγ b i hi) (hρ j hj))
  · dsimp only [old, γ, G]
    rw [e2, hw1.symm (Sum.inl z), hw2.symm]
    exact b3 (b, i) j hj
  · dsimp only [G]
    have h := b1 (true, n ^ 2) (false, n ^ 2) j hj
    have h7 : w1 (Sum.inr (true, n ^ 2)) (Sum.inr (false, n ^ 2)) = 0 := by
      rw [dist_congr_of_zero hw1 (hm true), hw1.symm]
      exact hm false
    rw [hw1.self, mul_zero, add_zero, h7, mul_zero] at h
    exact le_antisymm h (hw2.nonneg _ _)

/-! ### The fan in the coordinates of the windows -/

/-- For `(i, k) ∈ ℤ²` on either sheet let `P(i, k) = G(i', j')`, where `i'` is `i` clamped to
`[0, n²]` and `j'` is `i + k + n` clamped to `[0, T n²]`. -/
def fanPt (T n : ℕ) : Bool × ℤ × ℤ → FanPts Y
  | (b, i, k) => G b (clamp (n ^ 2) i) (clamp (n ^ 2 * T) (i + k + n))

/-- … and let W_n be the pull-back of n² times the distance. -/
def fanDist (d : FanPts Y → FanPts Y → ℝ) (T n : ℕ) (P P' : Bool × ℤ × ℤ) : ℝ :=
  (n : ℝ) ^ 2 * d (fanPt T n P) (fanPt T n P')

/-- L_i = |zγ_i|, as a function on the sheets (i is clamped to [0,n²]). -/
def fanLen (d : FanPts Y → FanPts Y → ℝ) (z : Y) (n : ℕ) (b : Bool) (i : ℤ) : ℝ :=
  d (FanPts.old z) (γ b (clamp (n ^ 2) i))

/-- The distance of P(i,k) from x, respectively v. -/
def fanPot (d : FanPts Y → FanPts Y → ℝ) (x : Bool → Y) (T n : ℕ) (b : Bool) (P : ℤ × ℤ) : ℝ :=
  d (FanPts.old (x b)) (fanPt T n (b, P))

theorem fanPt_mk (T n : ℕ) (b : Bool) (i k : ℤ) :
    (fanPt T n (b, (i, k)) : FanPts Y) = G b (clamp (n ^ 2) i) (clamp (n ^ 2 * T) (i + k + n)) :=
        rfl

namespace IsFan

variable {x : Bool → Y} {m z : Y} {D : ℝ} {T n : ℕ} {d : FanPts Y → FanPts Y → ℝ}

theorem D_nonneg (F : IsFan K w x m z D T n d) (hn : 0 < n) : 0 ≤ D := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := mul_nonneg ((F.price.nonneg _ _).trans (F.γ_step true 0 (by positivity)))
    (sq_nonneg (n : ℝ))
  rwa [div_mul_cancel₀ _ (by positivity)] at h

theorem γ_le (F : IsFan K w x m z D T n d) (hn : 0 < n) (b : Bool) (i i' : ℕ) (hi : i ≤ n ^ 2)
    (hi' : i' ≤ n ^ 2) :
    (n : ℝ) ^ 2 * d (γ b i) (γ b i') ≤ |(i : ℝ) - i'| * D := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine (mul_le_mul_of_nonneg_left (dist_chain_le F.price (γ b) (F.γ_step b) i i' hi hi')
    (by positivity)).trans_eq ?_
  field_simp

theorem G_i_le (F : IsFan K w x m z D T n d) (hn : 0 < n) (b : Bool) (i i' j : ℕ)
    (hi : i ≤ n ^ 2)
    (hi' : i' ≤ n ^ 2)
    (hj : j ≤ n ^ 2 * T) :
    (n : ℝ) ^ 2 * d (G b i j) (G b i' j) ≤ (1 - j / (n ^ 2 * T)) * (|(i : ℝ) - i'| * D) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine (mul_le_mul_of_nonneg_left
    (dist_chain_le F.price (fun i => G b i j) (fun i hi => F.G_step_i b i j hi hj) i i' hi hi')
    (by positivity)).trans_eq ?_
  field_simp

theorem G_j_le (F : IsFan K w x m z D T n d) (hn : 0 < n) (b : Bool) (i j j' : ℕ)
    (hj : j ≤ n ^ 2 * T)
    (hj' : j' ≤ n ^ 2 * T) :
    (n : ℝ) ^ 2 * d (G b i j) (G b i j') ≤ |(j : ℝ) - j'| / T * d (FanPts.old z) (γ b i) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine (mul_le_mul_of_nonneg_left (dist_chain_le F.price (G b i) (F.G_step_j b i) j j' hj hj')
    (by positivity)).trans_eq ?_
  field_simp

theorem z_γ_last (F : IsFan K w x m z D T n d) (b : Bool) : d (FanPts.old z) (γ b (n ^ 2)) =
    w z m := by
  rw [F.price.symm, dist_congr_of_zero F.price (F.γ_last b), F.price.symm, F.old]

theorem z_γ_zero (F : IsFan K w x m z D T n d) (b : Bool) : d (FanPts.old z) (γ b 0) =
    w z (x b) :=
    by
  rw [F.price.symm, dist_congr_of_zero F.price (F.γ_zero b), F.price.symm, F.old]

/-- As L_i ≤ D + |zm| … -/
theorem z_γ_le (F : IsFan K w x m z D T n d) (hn : 0 < n) (b : Bool) (i : ℕ)
    (hi : i ≤ n ^ 2) :
    d (FanPts.old z) (γ b i) ≤ D + w z m := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := F.price.triangle (FanPts.old z) (γ b (n ^ 2)) (γ b i)
  rw [F.z_γ_last] at h1
  have hi' : (i : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hi
  have h4 : |((n ^ 2 : ℕ) : ℝ) - i| ≤ (n : ℝ) ^ 2 := by
    push_cast
    rw [abs_of_nonneg (by linarith)]
    linarith [Nat.cast_nonneg (α := ℝ) i]
  have h5 := (F.γ_le hn b (n ^ 2) i le_rfl hi).trans
    (mul_le_mul_of_nonneg_right h4 (F.D_nonneg hn))
  linarith [le_of_mul_le_mul_left h5 (by positivity)]

/-- W_n is a price on the two sheets. -/
theorem fanDist_price (F : IsFan K w x m z D T n d) : IsPrice K (fanDist d T n) :=
  (F.price.comp (fanPt T n)).smul (by positivity)

/-- … we may take Λ = 2D + |zm|. -/
theorem lipschitz (F : IsFan K w x m z D T n d) (hT : 0 < T) (hn : 0 < n) (b : Bool)
    (P h : ℤ × ℤ) :
    fanDist d T n (b, P) (b, P + h) ≤ (2 * D + w z m) * (|(h.1 : ℝ)| + |(h.2 : ℝ)|) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hD0 := F.D_nonneg hn
  let mid : FanPts Y := G b (clamp (n ^ 2) (P + h).1) (clamp (n ^ 2 * T) (P.1 + P.2 + n))
  have h5 : |((clamp (n ^ 2) P.1 : ℕ) : ℝ) - (clamp (n ^ 2) (P + h).1 : ℕ)| ≤ |(h.1 : ℝ)| := by
    simpa [Prod.fst_add, abs_neg] using abs_clamp_sub_le (n ^ 2) P.1 (P + h).1
  have h8 : |((clamp (n ^ 2 * T) (P.1 + P.2 + n) : ℕ) : ℝ) -
      (clamp (n ^ 2 * T) ((P + h).1 + (P + h).2 + n) : ℕ)| ≤ |(h.1 : ℝ)| + |(h.2 : ℝ)| :=
    (abs_clamp_sub_le _ _ _).trans (by
      rw [Prod.fst_add, Prod.snd_add]
      push_cast
      rw [show ((P.1 : ℝ) + P.2 + n) - (P.1 + h.1 + (P.2 + h.2) + n) = -((h.1 : ℝ) + h.2) by ring,
        abs_neg]
      exact abs_add_le _ _)
  have h9 : (n : ℝ) ^ 2 * d (fanPt T n (b, P)) mid ≤ |(h.1 : ℝ)| * D := by
    refine (F.G_i_le hn b _ _ _ (clamp_le _ _) (clamp_le _ _) (clamp_le _ _)).trans ?_
    have : 0 ≤ ((clamp (n ^ 2 * T) (P.1 + P.2 + n) : ℕ) : ℝ) / (n ^ 2 * T) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h5 hD0,
      mul_nonneg (abs_nonneg (((clamp (n ^ 2) P.1 : ℕ) : ℝ) - (clamp (n ^ 2) (P + h).1 : ℕ))) hD0]
  have h10 : (n : ℝ) ^ 2 * d mid (fanPt T n (b, P + h)) ≤
      (|(h.1 : ℝ)| + |(h.2 : ℝ)|) * (D + w z m) :=
    (F.G_j_le hn b _ _ _ (clamp_le _ _) (clamp_le _ _)).trans
      (mul_le_mul ((div_le_self (abs_nonneg _) hT1).trans h8) (F.z_γ_le hn b _ (clamp_le _ _))
        (F.price.nonneg _ _) (by positivity))
  have h11 := mul_le_mul_of_nonneg_left
    (F.price.triangle (fanPt T n (b, P)) mid (fanPt T n (b, P + h))) (sq_nonneg (n : ℝ))
  have : 0 ≤ |(h.2 : ℝ)| * D := by positivity
  unfold fanDist
  linarith

/-- A step in the direction (1,−1) changes i only: it has length at most ρD. -/
theorem step_ii (F : IsFan K w x m z D T n d) (hT : 0 < T) (hn : 0 < n) (b : Bool) (i k : ℤ)
    (h0 : 0 ≤ i + k + n)
    (h1 : i + k + n ≤ n ^ 2 * T) :
    fanDist d T n (b, (i, k)) (b, (i + 1, k - 1)) ≤ (1 - (i + k + n) / (n ^ 2 * T)) * D := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have h6 := F.G_i_le hn b (clamp (n ^ 2) i) (clamp (n ^ 2) (i + 1))
      (clamp (n ^ 2 * T) (i + k + n)) (clamp_le _ _)
    (clamp_le _ _) (clamp_le _ _)
  rw [clamp_window h0 h1] at h6
  rw [fanDist, fanPt_mk, fanPt_mk, show i + 1 + (k - 1) + n = i + k + n by ring]
  refine h6.trans ?_
  have h8 : 0 ≤ 1 - ((i : ℝ) + k + n) / (n ^ 2 * T) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact_mod_cast h1
  apply mul_le_mul_of_nonneg_left _ h8
  calc _ ≤ 1 * D := mul_le_mul_of_nonneg_right (abs_clamp_sub_clamp_succ_le _ i) (F.D_nonneg hn)
    _ = D := one_mul D

/-- The distance from z gives a lower bound for W_n: n²(ρL_i − ρ′L_i′) ≤ W_n(P(i,k), P(i′,k′)). -/
theorem from_z (F : IsFan K w x m z D T n d) (b : Bool) (i k i' k' : ℤ) (h0 : 0 ≤ i + k + n)
    (h1 : i + k + n ≤ n ^ 2 * T) (h0' : 0 ≤ i' + k' + n) (h1' : i' + k' + n ≤ n ^ 2 * T) :
    (n : ℝ) ^ 2 * ((1 - (i + k + n) / (n ^ 2 * T)) * fanLen d z n b i
      - (1 - (i' + k' + n) / (n ^ 2 * T)) * fanLen d z n b i') ≤ fanDist d T n (b, (i, k))
          (b, (i', k')) := by
  have h6 := F.price.triangle (FanPts.old z) (fanPt T n (b, (i', k'))) (fanPt T n (b, (i, k)))
  rw [fanPt_mk, fanPt_mk, F.z_G _ _ _ (clamp_le _ _), F.z_G _ _ _ (clamp_le _ _),
    clamp_window h0 h1, clamp_window h0' h1'] at h6
  rw [fanDist, fanLen, fanLen, fanPt_mk, fanPt_mk, F.price.symm (G b _ _) (G b _ _)]
  exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)

/-- A step in the direction (0,1) has length at most θL_i. -/
theorem step_iii (F : IsFan K w x m z D T n d) (hn : 0 < n) (b : Bool) (i k : ℤ)
    (h0 : 0 ≤ i + k + n)
    (h1 : i + k + 1 + n ≤ n ^ 2 * T) :
    fanDist d T n (b, (i, k)) (b, (i, k + 1)) ≤ fanLen d z n b i / T := by
  have h6 := F.G_j_le hn b (clamp (n ^ 2) i) (clamp (n ^ 2 * T) (i + k + n))
    (clamp (n ^ 2 * T) (i + (k + 1) + n)) (clamp_le _ _) (clamp_le _ _)
  rw [clamp_window h0 (by linarith), clamp_window (by linarith) (by linarith)] at h6
  rw [fanDist, fanLen, fanPt_mk, fanPt_mk]
  refine h6.trans_eq ?_
  push_cast
  rw [show (i : ℝ) + k + n - (i + (k + 1) + n) = -1 by ring, abs_neg, abs_one]
  ring

theorem fanLen_zero (F : IsFan K w x m z D T n d) (b : Bool) : fanLen d z n b 0 =
    w z (x b) := by
  rw [fanLen, clamp_zero, F.z_γ_zero]

theorem fanLen_last (F : IsFan K w x m z D T n d) (b : Bool) : fanLen d z n b (n ^ 2) =
    w z m := by
  rw [fanLen, clamp_sq, F.z_γ_last]

theorem fanLen_nonneg (F : IsFan K w x m z D T n d) (b : Bool) (i : ℤ) : 0 ≤
    fanLen d z n b i :=
  F.price.nonneg _ _

theorem fanLen_le (F : IsFan K w x m z D T n d) (hn : 0 < n) (b : Bool)
    (i : ℤ) : fanLen d z n b i ≤ D + w z m :=
  F.z_γ_le hn b _ (clamp_le _ _)

theorem fanLen_step (F : IsFan K w x m z D T n d) (hn : 0 < n) (b : Bool) (i : ℤ) :
    |(n : ℝ) ^ 2 * (fanLen d z n b (i + 1) - fanLen d z n b i)| ≤ D := by
  have h1 := F.γ_le hn b (clamp (n ^ 2) i) (clamp (n ^ 2) (i + 1)) (clamp_le _ _) (clamp_le _ _)
  have h2 : |((clamp (n ^ 2) i : ℕ) : ℝ) - (clamp (n ^ 2) (i + 1) : ℕ)| * D ≤ D := by
    calc _ ≤ 1 * D := mul_le_mul_of_nonneg_right (abs_clamp_sub_clamp_succ_le _ i) (F.D_nonneg hn)
      _ = D := one_mul D
  have h3 := F.price.triangle (FanPts.old z) (γ b (clamp (n ^ 2) i)) (γ b (clamp (n ^ 2) (i + 1)))
  have h4 := F.price.triangle (FanPts.old z) (γ b (clamp (n ^ 2) (i + 1))) (γ b (clamp (n ^ 2) i))
  rw [F.price.symm (γ b (clamp (n ^ 2) (i + 1))) (γ b (clamp (n ^ 2) i))] at h4
  have h5 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  unfold fanLen
  rw [abs_le]
  constructor <;> nlinarith

theorem fanPot_sub_le (F : IsFan K w x m z D T n d) (b : Bool) (P P' : ℤ × ℤ) :
    (n : ℝ) ^ 2 * (fanPot d x T n b P - fanPot d x T n b P') ≤ fanDist d T n (b, P) (b, P') := by
  have h := F.price.triangle (FanPts.old (x b)) (fanPt T n (b, P')) (fanPt T n (b, P))
  rw [F.price.symm (fanPt T n (b, P')) (fanPt T n (b, P))] at h
  unfold fanPot fanDist
  exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)

/-- Steps in the direction (1,0) lead to a common end: the two ends have distance 0, so their
distances from x and v add
up to at least |xv|. -/
theorem fanPot_last (F : IsFan K w x m z D T n d) (k : ℤ) :
    w (x true) (x false) ≤ fanPot d x T n true (n ^ 2, k) + fanPot d x T n false (n ^ 2, k) := by
  rw [fanPot, fanPot, fanPt_mk, fanPt_mk, clamp_sq]
  have h10 := F.price.triangle (FanPts.old (x true))
    (G true (n ^ 2) (clamp (n ^ 2 * T) ((n : ℤ) ^ 2 + k + n))) (FanPts.old (x false))
  rwa [F.old, dist_congr_of_zero F.price (F.G_last _ (clamp_le _ _)),
    F.price.symm (G false _ _)] at h10

/-- The steps in the direction (1,0) start from a point within O(1/n) of x, respectively v. -/
theorem fanPot_zero (F : IsFan K w x m z D T n d) (b : Bool) (k : ℤ) (h0 : 0 ≤ k + n)
    (h1 : k + n ≤ n ^ 2 * T) :
    fanPot d x T n b (0, k) ≤ (k + n) / (n ^ 2 * T) * w z (x b) := by
  have h6 := F.G_γ b 0 _ (clamp_le (n ^ 2 * T) (0 + k + n))
  rw [clamp_window (by linarith) (by linarith), F.z_γ_zero] at h6
  have h8 : d (FanPts.old (x b)) (γ b 0) = 0 := by rw [F.price.symm, F.γ_zero]
  rw [fanPot, fanPt_mk, clamp_zero, dist_congr_of_zero F.price h8, F.price.symm]
  exact h6.trans_eq (by push_cast; ring)

end IsFan

/-- The display of claim (iv): Let L′ = L_{i+S}, L = L_i; for n ≥ AS the new j is not negative.
The distance from z gives
W(P, P + S(1,−1−A)) ≥ |n²ρ(L′ − L) + ASθL′|. Here P = P(i,k), j = i + k + n ≥ AS, ρ = 1 − jθ/n²
and θ = 1/T. -/
theorem thm_cn_iv_step {x : Bool → Y} {m z : Y} {D : ℝ} {T n : ℕ}
    {d : FanPts Y → FanPts Y → ℝ}
    (F : IsFan K w x m z D T n d) (hT : 0 < T) (hn : 0 < n) (b : Bool) (i k : ℤ) (A S : ℕ)
    (h0 : ((A * S : ℕ) : ℤ) ≤ i + k + n) (h1 : i + k + n ≤ n ^ 2 * T) :
    |(n : ℝ) ^ 2 * ((1 - (i + k + n) / (n ^ 2 * T)) * (fanLen d z n b (i + S) - fanLen d z n b i))
        + A * S * (1 / T) * fanLen d z n b (i + S)| ≤
      fanDist d T n (b, (i, k)) (b, (i + S, k - S - (A * S : ℕ))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have k0 : 0 ≤ i + k + n := (Int.natCast_nonneg _).trans h0
  have k2 : (0 : ℤ) ≤ (i + S) + (k - S - (A * S : ℕ)) + n := by linarith
  have k3 : (i + S) + (k - S - (A * S : ℕ)) + n ≤ n ^ 2 * T :=
    by linarith [Int.natCast_nonneg (A * S)]
  have g1 := F.from_z b (i + S) (k - S - (A * S : ℕ)) i k k2 k3 k0 h1
  have g2 := F.from_z b i k (i + S) (k - S - (A * S : ℕ)) k0 h1 k2 k3
  rw [F.fanDist_price.symm] at g1
  push_cast at g1 g2
  rw [show 1 - ((i : ℝ) + S + (k - S - A * S) + n) / (n ^ 2 * T) =
      1 - (i + k + n) / (n ^ 2 * T) + A * S / (n ^ 2 * T) by ring] at g1 g2
  rw [abs_le, ← show (n : ℝ) ^ 2 * (A * S / (n ^ 2 * T)) = A * S * (1 / T) by field_simp]
  exact ⟨(neg_le_neg g2).trans_eq (by ring), (le_of_eq (by ring)).trans g1⟩

/-! ### The sequence of fans and its seminorm

Above, fanDist, fanLen and fanPot belong to one fan, for one n. From here on d n is a fan for every
n, and fanW (fanWs on one
sheet), fanL and fanP are the corresponding sequences: the paper's W = (W_n), L = (L_i), and the
distances from x and v. -/

section Claims

variable {x : Bool → Y} {m z : Y} {D : ℝ} {T : ℕ} {d : ℕ → FanPts Y → FanPts Y → ℝ}

/-- The sequence W = (W_n) of the fans d n. (The window for n = 0 is empty; there the fan for n = 1
is used.) -/
def fanW (d : ℕ → FanPts Y → FanPts Y → ℝ) (T n : ℕ) : Bool × ℤ × ℤ → Bool × ℤ × ℤ → ℝ :=
  fanDist (d n) T (max n 1)

/-- W on each sheet. -/
def fanWs (d : ℕ → FanPts Y → FanPts Y → ℝ) (T n : ℕ) (b : Bool) (P P' : ℤ × ℤ) : ℝ :=
    fanW d T n (b, P) (b, P')

/-- The sequence L = (L_i). -/
def fanL (d : ℕ → FanPts Y → FanPts Y → ℝ) (z : Y) (n : ℕ) (b : Bool) (i : ℤ) : ℝ :=
    fanLen (d n) z (max n 1) b i

/-- The distances from x, respectively v. -/
def fanP (d : ℕ → FanPts Y → FanPts Y → ℝ) (x : Bool → Y) (T n : ℕ) (b : Bool) (P : ℤ × ℤ) : ℝ :=
  fanPot (d n) x T (max n 1) b P

/-- Let Λ₂ = E L², over both sheets. -/
noncomputable def fanΛ₂ (d : ℕ → FanPts Y → FanPts Y → ℝ) (z : Y) : ℝ :=
  mean ((fun n b i _ => fanL d z n b i : WindowFn) * (fun n b i _ => fanL d z n b i : WindowFn))

theorem fanW_price (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n))
    (n : ℕ) : IsPrice K (fanW d T n) :=
  (hd n).fanDist_price

/-- As L_i ≤ D + |zm|, we may take Λ = 2D + |zm|. -/
theorem thm_cn_lipschitz (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 0 < T)
    (n : ℕ)
    (b : Bool)
    (P g : ℤ × ℤ) : fanW d T n (b, P) (b, P + g) ≤ (2 * D + w z m) * (|(g.1 : ℝ)| + |(g.2 : ℝ)|) :=
  (hd n).lipschitz hT ((by simp : 0 < max n 1)) b P g

theorem fanWs_lip (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 0 < T) :
    CrossingMetrics (fanWs d T) (2 * D + w z m) :=
  crossingMetrics_sheetMetrics (fanW_price hd) (thm_cn_lipschitz hd hT)

theorem fan_w_nonneg (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (a b : Y) : 0 ≤
    w a b := by
  rw [← (hd 0).old]
  exact (hd 0).price.nonneg _ _

theorem fan_D_nonneg (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) : 0 ≤ D :=
    (hd 0).D_nonneg ((by simp : 0 < max 0 1))

theorem fanP_sub_le (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (n : ℕ) (b : Bool)
    (P P' : ℤ × ℤ) :
    (n : ℝ) ^ 2 * (fanP d x T n b P - fanP d x T n b P') ≤ fanWs d T n b P P' := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : 0 ≤ fanWs d T 0 b P P' := (fanW_price hd 0).nonneg (b, P) (b, P')
    simpa using h0
  · have : ((max n 1 : ℕ) : ℝ) ^ 2 * (fanP d x T n b P - fanP d x T n b P') ≤
        fanWs d T n b P P' := (hd n).fanPot_sub_le b P P'
    rwa [max_eq_left hn] at this

theorem fanL_step (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (n : ℕ) (b : Bool)
    (i : ℤ) :
    |(n : ℝ) ^ 2 * (fanL d z n b (i + 1) - fanL d z n b i)| ≤ D := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using fan_D_nonneg hd
  · have : |((max n 1 : ℕ) : ℝ) ^ 2 * (fanL d z n b (i + 1) - fanL d z n b i)| ≤ D :=
      (hd n).fanLen_step ((by simp : 0 < max n 1)) b i
    rwa [max_eq_left hn] at this

theorem fanL_nonneg (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (n : ℕ) (b : Bool)
    (i : ℤ) :
    0 ≤ fanL d z n b i := (hd n).fanLen_nonneg b i

theorem fanL_le (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (n : ℕ) (b : Bool) (i : ℤ) :
    fanL d z n b i ≤ D + w z m := (hd n).fanLen_le ((by simp : 0 < max n 1)) b i

theorem fanL_bd (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) : WindowFn.Bounded fun
    n b i _ =>
    fanL d z n b i := by
  refine ⟨D + w z m, fun n b i k => ?_⟩
  rw [abs_of_nonneg (fanL_nonneg hd n b i)]
  exact fanL_le hd n b i

/-- … so Λ₂ ≤ (D + |zm|)². -/
theorem thm_cn_Λ₂_le (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) : fanΛ₂ d z ≤
    (D + w z m) ^
    2 := by
  have h1 := mean_le ((fanL_bd hd).mul (fanL_bd hd)) (WindowFn.Bounded.const ((D + w z m) ^ 2))
    fun n b i _ => by
      simp only [Pi.mul_apply, sq]
      exact mul_self_le_mul_self (fanL_nonneg hd n b i) (fanL_le hd n b i)
  rwa [mean_const] at h1

/-- **Claim (i)** of the proof of Theorem C.1: N(1,0) ≥ D. -/
theorem thm_cn_i (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 2 ≤ T)
    (hxx : w (x true) (x false) = 2 * D) : D ≤ meanNorm (fanW d T) (1, 0) := by
  have hT0 : 0 < T := by omega
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT0
  have H := fanWs_lip hd hT0
  have hX : WindowFn.Bounded fun n b i k => (n : ℝ) ^ 2 *
      (fanP d x T n b (i + 1, k) - fanP d x T n b (i, k)) := by
    refine ⟨2 * D + w z m, fun n b i k => ?_⟩
    have h1 := H.lipschitz n b (i, k) (1, 0)
    simp only [Prod.mk_add_mk, Int.cast_one, abs_one, Int.cast_zero, abs_zero, add_zero,
      mul_one] at h1
    have h2 := fanP_sub_le hd n b (i + 1, k) (i, k)
    have h3 := fanP_sub_le hd n b (i, k) (i + 1, k)
    rw [H.symm] at h2
    rw [abs_le]
    constructor <;> linarith
  have h1 : Tendsto (fun n : ℕ => 2 * D - 2 * (w z (x true) + w z (x false)) / T * (1 / (n : ℝ)))
      atTop (𝓝 (2 * D)) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat.const_mul
      (2 * (w z (x true) + w z (x false)) / T)).const_sub (2 * D)
  have h2 := le_mean_tele (F := fun n b i k => fanP d x T n b (i, k)) hX h1 (by
    filter_upwards [eventually_large hT 0] with n hn k hk
    rcases hn with ⟨e, hn1, -, hn2, -⟩
    have g1 : w (x true) (x false) ≤ fanP d x T n true (((max n 1 : ℕ) : ℤ) ^ 2, k)
        + fanP d x T n false (((max n 1 : ℕ) : ℤ) ^ 2, k) := (hd n).fanPot_last (k : ℤ)
    have k2 : (k : ℤ) + max n 1 ≤ (max n 1 : ℕ) ^ 2 * T := by
      rw [e]
      exact_mod_cast (by omega : k + n ≤ n ^ 2 * T)
    have g2 : fanP d x T n true (0, k) ≤ ((k : ℝ) + max n 1) / ((max n 1 : ℕ) ^ 2 * T) *
        w z (x true) := (hd n).fanPot_zero true (k : ℤ) (by rw [e]; positivity) k2
    have g3 : fanP d x T n false (0, k) ≤ ((k : ℝ) + max n 1) / ((max n 1 : ℕ) ^ 2 * T) *
        w z (x false) := (hd n).fanPot_zero false (k : ℤ) (by rw [e]; positivity) k2
    rw [e, hxx] at g1
    rw [e] at g2 g3
    rw [Fintype.sum_bool]
    push_cast at g1 g2 g3 ⊢
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk.le
    have g4 : ((k : ℝ) + n) / (n ^ 2 * T) ≤ 2 / T * (1 / n) := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hT'.le (Nat.cast_nonneg (α := ℝ) n)]
    linarith [mul_le_mul_of_nonneg_right g4 (fan_w_nonneg hd z (x true)),
      mul_le_mul_of_nonneg_right g4 (fan_w_nonneg hd z (x false)),
      show 2 * (w z (x true) + w z (x false)) / T * (1 / (n : ℝ)) =
        2 / T * (1 / n) * w z (x true) + 2 / T * (1 / n) * w z (x false) by ring])
  refine le_meanNorm _ _ fun S _ => ?_
  obtain ⟨h3, h4⟩ := mean_steps (F := fun n b i k => fanP d x T n b (i, k)) hX S
  have h5 :
      mean (fun n b i k => (n : ℝ) ^ 2 * (fanP d x T n b (i + S, k) - fanP d x T n b (i, k))) ≤
      mean (translateDist (fanWs d T) 0 (S • (1, 0))) :=
    mean_le h3 (H.bounded _ _) fun n b i k => by
      have h6 := fanP_sub_le hd n b (i + S, k) (i, k)
      rw [H.symm] at h6
      simpa [translateDist, Prod.mk_add_mk] using h6
  rw [mul_comm]
  exact ((mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg S)).trans
    (h4.symm.le.trans h5)).trans (mean_le_rms (H.bounded 0 (S • (1, 0))))

/-- **Claim (ii)** of the proof of Theorem C.1: N(1,−1)² ≤ D²(1 − θ + θ²). -/
theorem thm_cn_ii (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 2 ≤ T) :
    meanNorm (fanW d T) (1, -1) ^ 2 ≤ D ^ 2 * (1 - 1 / T + (1 / T : ℝ) ^ 2) := by
  have hT0 : 0 < T := by omega
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT0
  have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hD0 := fan_D_nonneg hd
  have H := fanWs_lip hd hT0
  set θ : ℝ := 1 / T with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hT']; linarith
  have hpos (n b i k) : 0 ≤ 1 - θ * windowPlace n b i k := by
    nlinarith [windowPlace_nonneg n b i k, windowPlace_le_one n b i k]
  have hg : WindowFn.Bounded fun n b i k => D * (1 - θ * windowPlace n b i k) :=
    ⟨D, fun n b i k => by
      rw [abs_of_nonneg (mul_nonneg hD0 (hpos n b i k))]
      nlinarith [mul_nonneg hθ0.le (windowPlace_nonneg n b i k)]⟩
  have h1 :
      meanLength (fanW d T) (1, -1) ≤ rms fun n b i k => D * (1 - θ * windowPlace n b i k) := by
    apply rms_mono (H.bounded _ _) hg (fun _ _ _ _ => H.nonneg _ _ _ _)
    filter_upwards [eventually_large hT 0] with n hn b i hi k hk
    rcases hn with ⟨e, hn1, -, hn2, -⟩
    have g : _ → _ → fanWs d T n b (i, k) (i + 1, k - 1) ≤ _ :=
      (hd n).step_ii hT0 ((by simp : 0 < max n 1)) b i k
    rw [e] at g
    have g := g (by positivity) (by exact_mod_cast (by omega : i + k + n ≤ n ^ 2 * T))
    push_cast at g
    have h2 :
        translateDist (fanWs d T) 0 (1, -1) n b i k = fanWs d T n b (i, k) (i + 1, k - 1) := by
      simp [translateDist, sub_eq_add_neg]
    rw [h2]
    refine g.trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hD0
    have h4 : θ * ((i : ℝ) / n ^ 2) = i / (n ^ 2 * T) := by rw [hθ]; field_simp
    rw [windowPlace_natCast hi.le b k, h4]
    linarith [div_le_div_of_nonneg_right
      (show (i : ℝ) ≤ i + k + n by linarith [Nat.cast_nonneg (α := ℝ) k])
      (show (0 : ℝ) ≤ n ^ 2 * T by positivity)]
  have h2 :
      rms (fun n b i k => D * (1 - θ * windowPlace n b i k)) ^ 2 ≤ D ^ 2 * (1 - θ + θ ^ 2) := by
    rw [rms_sq hg]
    have h3 : mean ((fun n b i k => D * (1 - θ * windowPlace n b i k)) *
        fun n b i k => D * (1 - θ * windowPlace n b i k)) ≤
        mean ((fun _ _ _ _ => D ^ 2 * (1 + θ ^ 2)) + (-(2 * θ * D ^ 2)) • windowPlace) :=
      mean_le (hg.mul hg) ((WindowFn.Bounded.const _).add (bounded_windowPlace.smul _))
        fun n b i k => by
          simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          have := mul_le_mul_of_nonneg_left
            (show windowPlace n b i k ^ 2 ≤ 1 by
              nlinarith [windowPlace_nonneg n b i k, windowPlace_le_one n b i k])
            (show 0 ≤ θ ^ 2 * D ^ 2 by positivity)
          nlinarith
    rw [mean_add (WindowFn.Bounded.const _) (bounded_windowPlace.smul _), mean_const,
      mean_smul bounded_windowPlace, mean_windowPlace] at h3
    linarith
  exact (pow_le_pow_left₀ (meanNorm_nonneg _ _) ((meanNorm_le_meanLength _ _).trans h1) 2).trans h2

/-- **Claim (iii)** of the proof of Theorem C.1: N(0,1)² ≤ θ²Λ₂. -/
theorem thm_cn_iii (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 2 ≤ T) :
    meanNorm (fanW d T) (0, 1) ^ 2 ≤ (1 / T : ℝ) ^ 2 * fanΛ₂ d z := by
  have hT0 : 0 < T := by omega
  have H := fanWs_lip hd hT0
  have hLf := fanL_bd hd
  set θ : ℝ := 1 / T with hθ
  have h1 :
      meanLength (fanW d T) (0, 1) ≤ rms (θ • (fun n b i _ => fanL d z n b i : WindowFn)) := by
    apply rms_mono (H.bounded _ _) (hLf.smul θ) (fun _ _ _ _ => H.nonneg _ _ _ _)
    filter_upwards [eventually_large hT 1] with n hn b i hi k hk
    rcases hn with ⟨e, hn1, hn3, hn2, -⟩
    have g : _ → _ → fanWs d T n b (i, k) (i, k + 1) ≤ fanL d z n b i / T :=
      (hd n).step_iii ((by simp : 0 < max n 1)) b i k
    rw [e] at g
    have h2 : translateDist (fanWs d T) 0 (0, 1) n b i k = fanWs d T n b (i, k) (i, k + 1) := by
      simp [translateDist]
    rw [h2]
    exact (g (by positivity) (by exact_mod_cast (by omega : i + k + 1 + n ≤ n ^ 2 * T))).trans_eq
      (by simp only [Pi.smul_apply, smul_eq_mul, hθ]; ring)
  have h2 : rms (θ • (fun n b i _ => fanL d z n b i : WindowFn)) ^ 2 = θ ^ 2 * fanΛ₂ d z := by
    have hsmul : (θ • (fun n b i _ => fanL d z n b i : WindowFn) : WindowFn) *
        (θ • (fun n b i _ => fanL d z n b i : WindowFn)) =
        (θ ^ 2) •
            ((fun n b i _ => fanL d z n b i : WindowFn) *
                (fun n b i _ => fanL d z n b i : WindowFn)) := by
      funext n b i k
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [rms_sq (hLf.smul θ), hsmul, mean_smul (hLf.mul hLf), fanΛ₂]
  rw [← h2]
  exact pow_le_pow_left₀ (meanNorm_nonneg _ _) ((meanNorm_le_meanLength _ _).trans h1) 2

/-- n²|L′² − L²| ≤ 2SD(D + |zm|), for L′ = L_{i+S} and L = L_i. -/
theorem thm_cn_iv_bound (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (n : ℕ) (b : Bool)
    (i : ℤ)
    (S : ℕ) :
    |(n : ℝ) ^ 2 * (fanL d z n b (i + S) ^ 2 - fanL d z n b i ^ 2)| ≤ 2 * (D + w z m) * (S * D) :=
        by
  have hD0 := fan_D_nonneg hd
  have hB0 := fan_w_nonneg hd z m
  have hLs : ∀ S : ℕ, |(n : ℝ) ^ 2 * (fanL d z n b (i + S) - fanL d z n b i)| ≤ S * D := fun S => by
    induction S with
    | zero => simp
    | succ S ih =>
      have e : (n : ℝ) ^ 2 * (fanL d z n b (i + (S + 1 : ℕ)) - fanL d z n b i) =
          n ^ 2 * (fanL d z n b (i + S + 1) - fanL d z n b (i + S))
            + n ^ 2 * (fanL d z n b (i + S) - fanL d z n b i) := by
        push_cast
        rw [← add_assoc]
        ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      push_cast
      linarith [fanL_step hd n b (i + S)]
  rw [show (n : ℝ) ^ 2 * (fanL d z n b (i + S) ^ 2 - fanL d z n b i ^ 2) =
      (fanL d z n b (i + S) + fanL d z n b i) *
        (n ^ 2 * (fanL d z n b (i + S) - fanL d z n b i)) by ring, abs_mul]
  refine mul_le_mul ?_ (hLs S) (abs_nonneg _) (by positivity)
  rw [abs_of_nonneg (add_nonneg (fanL_nonneg hd n b _) (fanL_nonneg hd n b _))]
  linarith [fanL_le hd n b (i + S), fanL_le hd n b i]

theorem fanL_sq_bd (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) :
    WindowFn.Bounded fun n b i _ => (n : ℝ) ^ 2 * (fanL d z n b (i + 1) ^ 2 - fanL d z n b i ^ 2) :=
  ⟨2 * (D + w z m) * ((1 : ℕ) * D), fun n b i _ => by simpa using thm_cn_iv_bound hd n b i 1⟩

/-- n²(L′² − L²) telescopes along i to the mean SΓ, with Γ = |mz|² − ½|xz|² − ½|vz|²: here for S
= 1, and only that the mean
is at least Γ, which is what claim (iv) uses. (WindowFn.mean_steps passes from S = 1 to any S.) -/
theorem thm_cn_iv_telescope (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 2 ≤ T) :
    w z m ^ 2 - (w z (x true) ^ 2 + w z (x false) ^ 2) / 2 ≤
      mean (fun n b i _ => (n : ℝ) ^ 2 * (fanL d z n b (i + 1) ^ 2 - fanL d z n b i ^ 2)) := by
  have h := le_mean_tele (F := fun n b i _ => fanL d z n b i ^ 2) (fanL_sq_bd hd)
    (c := fun _ => 2 * (w z m ^ 2 - (w z (x true) ^ 2 + w z (x false) ^ 2) / 2)) tendsto_const_nhds
    (by
      filter_upwards [eventually_large hT 0] with n hn _ _
      rcases hn with ⟨e, -⟩
      have g1 : fanL d z n true (((max n 1 : ℕ) : ℤ) ^ 2) = w z m := (hd n).fanLen_last true
      have g2 : fanL d z n false (((max n 1 : ℕ) : ℤ) ^ 2) = w z m := (hd n).fanLen_last false
      have z1 : fanL d z n true 0 = w z (x true) := (hd n).fanLen_zero true
      have z2 : fanL d z n false 0 = w z (x false) := (hd n).fanLen_zero false
      rw [e] at g1 g2
      rw [Fintype.sum_bool, z1, z2]
      push_cast
      rw [g1, g2]
      linarith)
  linarith

/-- The next sentence of claim (iv): Square this, use 2L′(L′ − L) ≥ L′² − L², and note that … 1 −
ρ ≤ 2θ … and
n²|L′² − L²| ≤ 2SD(D + |zm|). So for large n, at the points P = P(i,k) of the window,
W(P, P + S(1,−1−A))² ≥ (ASθ)²L′² + ASθ·n²(L′² − L²) − 4Aθ²S²D(D + |zm|). -/
theorem thm_cn_iv_square (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 2 ≤ T)
    (A S : ℕ)
    {n : ℕ}
    (hnn : max n 1 = n ∧ (1 : ℝ) ≤ n ∧ A * S ≤ n ∧ n ^ 2 + 2 * n ≤ n ^ 2 * T ∧ n ^ 2 + 2 * n ≤ 2 *
        n ^ 2)
    (b : Bool) {i k : ℕ} (hi : i < n ^ 2) (hk : k < n) :
    (A * S * (1 / T : ℝ)) ^ 2 * (fanL d z n b (i + S) * fanL d z n b (i + S))
      + A * S * (1 / T : ℝ) * ((n : ℝ) ^ 2 * (fanL d z n b (i + S) ^ 2 - fanL d z n b i ^ 2))
      - 4 * A * (1 / T : ℝ) ^ 2 * S ^ 2 * D * (D + w z m) ≤
      fanWs d T n b (i, k) (i + S, k - S - (A * S : ℕ)) * fanWs d T n b (i, k)
          (i + S, k - S - (A * S : ℕ)) := by
  obtain ⟨e, hn1, hAS, hn2, hn3⟩ := hnn
  have hT' : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hn0 : (0 : ℝ) < n := by linarith
  have hD0 := fan_D_nonneg hd
  have hB0 := fan_w_nonneg hd z m
  have k0 : ((A * S : ℕ) : ℤ) ≤ (i : ℤ) + k + n := by
    linarith [show ((A * S : ℕ) : ℤ) ≤ n by exact_mod_cast hAS,
      Int.natCast_nonneg i, Int.natCast_nonneg k]
  have k1 : (i : ℤ) + k + n ≤ n ^ 2 * T := by exact_mod_cast (by omega : i + k + n ≤ n ^ 2 * T)
  have g : _ → _ → |((max n 1 : ℕ) : ℝ) ^ 2 * (_ * (fanL d z n b (i + S) - fanL d z n b i))
      + A * S * (1 / T) * fanL d z n b (i + S)| ≤ fanWs d T n b (i, k)
          (i + S, k - S - (A * S : ℕ)) :=
    thm_cn_iv_step (hd n) (by omega) ((by simp : 0 < max n 1)) b i k A S
  rw [e] at g
  have g := abs_le.1 (g k0 k1)
  push_cast at g
  set r : ℝ := 1 - (i + k + n) / (n ^ 2 * T) with hr
  have hr0 : 0 ≤ r := by
    rw [hr, sub_nonneg, div_le_one (by positivity)]
    exact_mod_cast k1
  have hr1 : 1 - r ≤ 2 * (1 / T) := by
    rw [hr, sub_sub_cancel, div_le_iff₀ (by positivity)]
    exact (by exact_mod_cast (by omega : i + k + n ≤ 2 * n ^ 2) :
      (i : ℝ) + k + n ≤ 2 * n ^ 2).trans_eq (by field_simp)
  have hr2 : 0 ≤ 1 - r := by rw [hr, sub_sub_cancel]; positivity
  refine (le_of_eq (by ring)).trans
    (sq_le_of_abs_le hr0 hr2 hr1 (a := A * S * (1 / T)) (by positivity)
      (by positivity : 0 ≤ 2 * (D + w z m) * (S * D)) (abs_le.1 (thm_cn_iv_bound hd n b i S)).2
      (W := fanWs d T n b (i, k) (i + S, k - S - (A * S : ℕ)))
      ((le_of_eq (by ring)).trans g.2) ((le_of_eq (by ring)).trans (neg_le.1 g.1)))

/-- The end of claim (iv), for ν: n²(L′² − L²) telescopes along i to the mean SΓ, while … the mean
of L′² is Λ₂: so
ν(S(1,−1−A))² ≥ S²(A²θ²Λ₂ + AθΓ − 4Aθ²D(D + |zm|)) for every S. -/
theorem thm_cn_iv_mean (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 2 ≤ T)
    (A S : ℕ) :
    ((A : ℝ) ^ 2 * ((1 / T : ℝ) ^ 2 * fanΛ₂ d z)
      + A * (1 / T * (w z m ^ 2 - (w z (x true) ^ 2 + w z (x false) ^ 2) / 2)
        - 4 * (1 / T : ℝ) ^ 2 * D * (D + w z m))) * S ^ 2 ≤
      meanLength (fanW d T) (S • (1, -1 - (A : ℤ))) ^ 2 := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have H := fanWs_lip hd (by omega : 0 < T)
  have hLf := fanL_bd hd
  set θ : ℝ := 1 / T
  have hθ0 : 0 < θ := by positivity
  change _ ≤ rms (translateDist (fanWs d T) 0 (S • (1, -1 - (A : ℤ)))) ^ 2
  rw [rms_sq (H.bounded _ _)]
  obtain ⟨hZb, hZm⟩ := mean_steps (F := fun n b i _ => fanL d z n b i ^ 2) (fanL_sq_bd hd) S
  have hsh := hLf.shift S 0
  have h4 : mean
      ((fun n b i _ => fanL d z n b (i + S) : WindowFn) *
          (fun n b i _ => fanL d z n b (i + S) : WindowFn)) =
      fanΛ₂ d z := mean_shift_left (hLf.mul hLf) S
  have h3 : mean ((A * S * θ) ^ 2 • ((fun n b i _ => fanL d z n b (i + S) : WindowFn) *
        (fun n b i _ => fanL d z n b (i + S) : WindowFn))
      + ((A * S * θ) •
          (fun n b i _ => (n : ℝ) ^ 2 * (fanL d z n b (i + S) ^ 2 - fanL d z n b i ^ 2) : WindowFn)
      + (fun _ _ _ _ => -(4 * A * θ ^ 2 * S ^ 2 * D * (D + w z m)) : WindowFn))) ≤
      mean (translateDist (fanWs d T) 0 (S • (1, -1 - (A : ℤ))) *
          translateDist (fanWs d T) 0 (S • (1, -1 - (A : ℤ)))) := by
    apply mean_mono (((hsh.mul hsh).smul _).add ((hZb.smul _).add (WindowFn.Bounded.const _)))
      ((H.bounded _ _).mul (H.bounded _ _))
    filter_upwards [eventually_large hT (A * S)] with n hnn b i hi k hk
    have e0 : translateDist (fanWs d T) 0 (S • (1, -1 - (A : ℤ))) n b i k =
        fanWs d T n b (i, k) (i + S, k - S - (A * S : ℕ)) := by
      simp only [translateDist, add_zero, Prod.smul_mk, Prod.mk_add_mk, nsmul_eq_mul]
      refine congrArg (fanWs d T n b (i, k)) (Prod.ext (by ring) ?_)
      push_cast
      ring
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, e0]
    linarith [thm_cn_iv_square hd hT A S hnn b hi hk]
  rw [mean_add ((hsh.mul hsh).smul _) ((hZb.smul _).add (WindowFn.Bounded.const _)),
    mean_smul (hsh.mul hsh), mean_add (hZb.smul _) (WindowFn.Bounded.const _), mean_smul hZb,
    mean_const, hZm, h4] at h3
  have h5 := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (thm_cn_iv_telescope hd hT) (Nat.cast_nonneg S))
    (show 0 ≤ A * S * θ by positivity)
  exact (by nlinarith : _ ≤ _).trans h3

/-- **Claim (iv)** of the proof of Theorem C.1: N(1,−1−A)² ≥ A²θ²Λ₂ + AθΓ − O(Aθ²), with
Γ = |mz|² − ½|xz|² − ½|vz|² and with 4D(D + |zm|) for the constant in O, which depends on neither A
nor θ. (Divide by S²;
for lower bounds it is enough to prove them for ν(Sg)/S for every S.) -/
theorem thm_cn_iv (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 2 ≤ T) (A : ℕ) :
    (A : ℝ) ^ 2 * ((1 / T : ℝ) ^ 2 * fanΛ₂ d z)
      + A * (1 / T * (w z m ^ 2 - (w z (x true) ^ 2 + w z (x false) ^ 2) / 2) - 4 * (1 / T : ℝ) ^
          2 * D * (D + w z m)) ≤
      meanNorm (fanW d T) (1, -1 - (A : ℤ)) ^ 2 := by
  set Q := (A : ℝ) ^ 2 * ((1 / T : ℝ) ^ 2 * fanΛ₂ d z)
    + A * (1 / T * (w z m ^ 2 - (w z (x true) ^ 2 + w z (x false) ^ 2) / 2) - 4 * (1 / T : ℝ) ^ 2 *
        D * (D + w z m))
    with hQdef
  rcases lt_or_ge Q 0 with h | hQ
  · exact h.le.trans (sq_nonneg _)
  have h1 : √Q ≤ meanNorm (fanW d T) (1, -1 - (A : ℤ)) := by
    refine le_meanNorm _ _ fun S _ => (abs_le_of_sq_le_sq' ?_ (meanLength_nonneg _ _)).2
    rw [mul_pow, Real.sq_sqrt hQ]
    exact thm_cn_iv_mean hd hT A S
  calc Q = √Q ^ 2 := (Real.sq_sqrt hQ).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2

/-- **The end** of the proof of Theorem C.1. By Lemma C.2 the second differences of l ↦
N(1,−1−l)² are 2N(0,1)², so
by (iii) ψ(l) = N(1,−1−l)² − l²θ²Λ₂ is concave on l = −1, 0, 1, …, so ψ(A) ≤ ψ(0) + A(ψ(0) −
ψ(−1)). Insert (i), (ii), (iv),
divide by A and let A → ∞: θΓ − O(θ²) ≤ D²(−θ + θ²) + θ²Λ₂. -/
theorem thm_cn_end (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 2 ≤ T)
    (hxx : w (x true) (x false) = 2 * D) :
    1 / T * (w z m ^ 2 - (w z (x true) ^ 2 + w z (x false) ^ 2) / 2) - 4 * (1 / T : ℝ) ^ 2 * D *
        (D + w z m) ≤
      D ^ 2 * (-(1 / T) + (1 / T : ℝ) ^ 2) + (1 / T : ℝ) ^ 2 * fanΛ₂ d z := by
  have par := meanNorm_parallelogram (fanW_price hd) (thm_cn_lipschitz hd (by omega))
  have s2 := thm_cn_ii hd hT
  have s3 := thm_cn_iii hd hT
  set N := meanNorm (fanW d T)
  set θ : ℝ := 1 / T
  set Λ₂ := fanΛ₂ d z
  set Gc := w z m ^ 2 - (w z (x true) ^ 2 + w z (x false) ^ 2) / 2
  have c0 : N (1, -1 - ((1 : ℕ) : ℤ)) ^ 2 + N (1, 0) ^ 2 ≤
      2 * N (1, -1 - ((0 : ℕ) : ℤ)) ^ 2 + 2 * (θ ^ 2 * Λ₂) := by
    have h := par (1, -1) (0, 1)
    norm_num at h ⊢
    linarith
  have c1 (j : ℕ) : N (1, -1 - ((j + 2 : ℕ) : ℤ)) ^ 2 + N (1, -1 - (j : ℤ)) ^ 2 ≤
      2 * N (1, -1 - ((j + 1 : ℕ) : ℤ)) ^ 2 + 2 * (θ ^ 2 * Λ₂) := by
    have h := par (1, -1 - ((j + 1 : ℕ) : ℤ)) (0, 1)
    have e1 : ((1, -1 - ((j + 1 : ℕ) : ℤ)) : ℤ × ℤ) + (0, 1) = (1, -1 - (j : ℤ)) :=
      Prod.ext (by simp)
        (by simp; ring)
    have e2 : ((1, -1 - ((j + 1 : ℕ) : ℤ)) : ℤ × ℤ) - (0, 1) = (1, -1 - ((j + 2 : ℕ) : ℤ)) :=
      Prod.ext (by simp)
        (by simp; ring)
    rw [e1, e2] at h
    linarith
  have c2 := le_of_second_diff_le (f := fun j : ℕ => N (1, -1 - (j : ℤ)) ^ 2)
    (φ := N (1, 0) ^ 2) c0 c1
  simp only [Nat.cast_zero, sub_zero] at c2
  have hφ : D ^ 2 ≤ N (1, 0) ^ 2 := pow_le_pow_left₀ (fan_D_nonneg hd) (thm_cn_i hd hT hxx) 2
  set Δ :=
    θ * Gc - 4 * θ ^ 2 * D * (D + w z m) - (N (1, -1) ^ 2 - N (1, 0) ^ 2 + θ ^ 2 * Λ₂) with hΔ
  have hΔ0 : Δ ≤ 0 := by
    by_contra! h
    obtain ⟨A, hA'⟩ := exists_nat_gt (N (1, -1) ^ 2 / Δ)
    rw [div_lt_iff₀ h] at hA'
    have h1 : (A : ℝ) ^ 2 * (θ ^ 2 * Λ₂) + A * (θ * Gc - 4 * θ ^ 2 * D * (D + w z m)) ≤
        N (1, -1 - (A : ℤ)) ^ 2 := thm_cn_iv hd hT A
    have h2 := c2 A
    rw [hΔ] at hA'
    linarith
  linarith

end Claims

public section

/-- **Paper: Theorem C.1.** Let `x, v, m, z` be points of a price `w` with `w(x, m), w(v, m) ≤ D`
and `w(x, v) = 2D`. Then `w(z, m)² ≤ ½ w(z, x)² + ½ w(z, v)² - D²`. -/
theorem isPrice_sq_le_of_mid {Y : Type} {w : Y → Y → ℝ} (hw : IsPrice K w) (x v m z : Y)
    {D : ℝ} (h1 : w x m ≤ D)
    (h2 : w v m ≤ D)
    (h3 : w x v = 2 * D) : w z m ^ 2 ≤ 1 / 2 * w z x ^ 2 + 1 / 2 * w z v ^ 2 - D ^ 2 := by
  have hD0 : 0 ≤ D := (hw.nonneg _ _).trans h1
  have hB0 : 0 ≤ w z m := hw.nonneg _ _
  -- for θ = 1/T: divide by θ
  have key (T : ℕ) (hT : 2 ≤ T) : w z m ^ 2 - (w z x ^ 2 + w z v ^ 2) / 2 + D ^ 2 ≤
      1 / T * (D ^ 2 + (D + w z m) ^ 2 + 4 * D * (D + w z m)) := by
    have hT0 : 0 < T := by omega
    have hθ0 : (0 : ℝ) < 1 / T := one_div_pos.2 (Nat.cast_pos.2 hT0)
    choose d hd using fun n : ℕ => thm_cn_fan hw (fun b => cond b x v) m z
      (by rintro (_ | _) <;> assumption) hT0
      ((by simp : 0 < max n 1))
    have h4 := thm_cn_end hd hT h3
    simp only [Bool.cond_true, Bool.cond_false] at h4
    exact le_of_mul_le_mul_left
      (by nlinarith [mul_le_mul_of_nonneg_left (thm_cn_Λ₂_le hd) (sq_nonneg (1 / T : ℝ))]) hθ0
  -- let θ → 0
  have hT : Tendsto (fun T : ℕ => 1 / (T : ℝ) * (D ^ 2 + (D + w z m) ^ 2 + 4 * D * (D + w z m)))
      atTop (𝓝 0) := by
    rw [← zero_mul (D ^ 2 + (D + w z m) ^ 2 + 4 * D * (D + w z m))]
    exact tendsto_one_div_atTop_nhds_zero_nat.mul_const _
  have h4 := ge_of_tendsto hT <| by
    filter_upwards [eventually_ge_atTop 2] with T hT
    exact key T hT
  linarith

end

end Cslib.Circuits.Arithmetic.Separation.Curvature
