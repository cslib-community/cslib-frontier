/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Length
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Price.Basic
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Crossing
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Means of prices on two sheets of `ℤ²`, and the parallelogram law

Lemma C.2 of *VP ≠ VNP over every field* [AnthropicVPVNP2026]. For `n = 1, 2, …` (in Lean
`W : ℕ → …` is indexed from `n = 0`; the window means do not see finitely many terms) let `W n` be
a price on two sheets of `ℤ²` with `W n (P, P + g) ≤ Λ |g|` on each sheet. The mean length
`ν(g) = (E W(P, P + g)²)^(1/2)` (`meanLength`, built on `Separation.meanLength` of the sheet
metrics) is a crossing length (`crossingLength_meanLength`), and `N(g) = inf ν(S g)/S`
(`meanNorm`) is its homogenization (`meanNorm_eq_homogenization`), the limit of `ν(S g)/S`
(`tendsto_meanLength_div`). The lemma is the parallelogram law for `N`
(`meanNorm_parallelogram`), which holds for every homogeneous crossing length
(`Separation.CrossingLength.parallelogram`).

The proof follows the paper. Of `N` it uses only that it is a homogeneous crossing length: the
inequality (Q) (display (B.2)) at well-chosen points, convexity along lines, a telescoping sum and
averaging give `N(a + b)² + N(a - b)² ≤ 2 N(a)² + 2 N(b)²`, and applying this to `a + b, a - b`
gives equality.

## Main definitions

* `sheetMetrics`, `meanLength`, `meanNorm`.

## Main results

* `crossingMetrics_sheetMetrics`, `crossingLength_meanLength`, `meanNorm_eq_homogenization`,
  `tendsto_meanLength_div`.
* `Separation.CrossingLength.parallelogram`: the parallelogram law for a homogeneous crossing
  length.
* `meanNorm_parallelogram`: Lemma C.2.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma C.2 of the paper (§C.2); module `Paper.Means` (`lem_means`)
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Curvature

open Finset Filter Topology Cslib.PartyTensor

variable {K : Type} [Field K]

/-- The prices `W n` on two sheets of `ℤ²` (the type `Bool × ℤ × ℤ`), as metrics on each sheet. -/
@[expose] def sheetMetrics (W : ℕ → Bool × ℤ × ℤ → Bool × ℤ × ℤ → ℝ) :
    ℕ → Bool → ℤ × ℤ → ℤ × ℤ → ℝ :=
  fun n b P P' => W n (b, P) (b, P')

/-- The paper's `ν(g) = (E W(P, P + g)²)^(1/2)`: the mean length of the sheet metrics. -/
@[expose] noncomputable def meanLength (W : ℕ → Bool × ℤ × ℤ → Bool × ℤ × ℤ → ℝ) (g : ℤ × ℤ) : ℝ :=
  Separation.meanLength (sheetMetrics W) g

/-- The paper's `N(g) = inf ν(S g)/S` over the integers `S ≥ 1`. -/
noncomputable def meanNorm (W : ℕ → Bool × ℤ × ℤ → Bool × ℤ × ℤ → ℝ) (g : ℤ × ℤ) : ℝ :=
  sInf {r : ℝ | ∃ S : ℕ, 0 < S ∧ r = meanLength W (S • g) / S}

section Norm

variable (W : ℕ → Bool × ℤ × ℤ → Bool × ℤ × ℤ → ℝ) (g : ℤ × ℤ)

theorem meanLength_nonneg : 0 ≤ meanLength W g := WindowFn.rms_nonneg _

/-- `N(g)` is the greatest lower bound of the `ν(S g)/S`, `S ≥ 1`. -/
theorem meanNorm_isGLB :
    IsGLB {r : ℝ | ∃ S : ℕ, 0 < S ∧ r = meanLength W (S • g) / S} (meanNorm W g) :=
  isGLB_csInf ⟨_, 1, one_pos, rfl⟩
    ⟨0, by rintro _ ⟨S, -, rfl⟩; exact div_nonneg (meanLength_nonneg _ _) (Nat.cast_nonneg _)⟩

/-- An upper bound on `N` needs one `S`. -/
theorem meanNorm_le {S : ℕ} (hS : 0 < S) : meanNorm W g ≤ meanLength W (S • g) / S :=
  (meanNorm_isGLB W g).1 ⟨S, hS, rfl⟩

theorem meanNorm_le_meanLength : meanNorm W g ≤ meanLength W g := by
  simpa using meanNorm_le W g one_pos

/-- A lower bound on `N` needs all `S`. -/
theorem le_meanNorm {c : ℝ} (h : ∀ S : ℕ, 0 < S → c * S ≤ meanLength W (S • g)) :
    c ≤ meanNorm W g :=
  (meanNorm_isGLB W g).2 <| by
    rintro _ ⟨S, hS, rfl⟩
    exact (le_div_iff₀ (Nat.cast_pos.2 hS)).2 (h S hS)

theorem meanNorm_nonneg : 0 ≤ meanNorm W g :=
  le_meanNorm W g fun S _ => by rw [zero_mul]; exact meanLength_nonneg _ _

end Norm

variable {W : ℕ → Bool × ℤ × ℤ → Bool × ℤ × ℤ → ℝ} {Λ : ℝ}

/-- What is used of the prices `W n`: they are pseudometrics, Lipschitz on each sheet, and satisfy
display (B.2) of Proposition B.3. -/
theorem crossingMetrics_sheetMetrics (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) :
    CrossingMetrics (sheetMetrics W) Λ where
  nonneg n _ _ _ := (hW n).nonneg _ _
  self n _ _ := (hW n).self _
  symm n _ _ _ := (hW n).symm _ _
  triangle n _ _ _ _ := (hW n).triangle _ _ _
  lipschitz := hΛ
  crossing n b x v y u o o' w w' _ _ τ hp hq hτ :=
    isPrice_crossing_two_mul_le (hW n) (b, x) (b, v) (b, y) (b, u) (b, o) (b, o') (b, w)
        (b, w') hp hq τ hτ

/-- `ν` is a crossing length: even, subadditive, and with the inequality (Q). -/
theorem crossingLength_meanLength (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) :
    CrossingLength (meanLength W) :=
  (crossingMetrics_sheetMetrics hW hΛ).crossingLength

/-- `N` is the homogenization of `ν`: the limit of `ν(S g)/S` is also its infimum. -/
theorem meanNorm_eq_homogenization (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) :
    meanNorm W = (crossingLength_meanLength hW hΛ).homogenization := by
  set hν := crossingLength_meanLength hW hΛ
  funext g
  exact le_antisymm
    (hν.le_homogenization fun S hS => (le_div_iff₀ (Nat.cast_pos.2 hS)).1 (meanNorm_le W g hS))
    (le_meanNorm W g fun S _ =>
      (mul_comm _ (S : ℝ)).trans_le (hν.isHomogeneous_homogenization S g ▸ hν.homogenization_le _))

/-! ### The proof of Lemma C.2

The steps use of `N` only that it is a homogeneous crossing length (`CrossingLength N`,
`IsHomogeneous N`). As in the paper `c = a + b`, `e = a - b`, `f = N(c)` and `f' = N(e)`. -/

section Parallelogram

/-- The paper's `∂p = 2 N(p) - N(p - a) - N(p - b)`; its `∂'q = 2 N(q) - N(q - a) - N(q + b)` is the
same with `-b` for `b`. -/
private def meansDiff (N : ℤ × ℤ → ℝ) (a b p : ℤ × ℤ) : ℝ := 2 * N p - N (p - a) - N (p - b)

/-- The paper's points `A_i = M c + i e`; with `-b` for `b` this is `M e + i c`. -/
private def meansPt (a b : ℤ × ℤ) (M i : ℕ) : ℤ × ℤ := M • (a + b) + i • (a - b)

/-- The paper's `δ_i = N(A_i - a) - N(A_i - 2a)`. -/
private def meansDelta (N : ℤ × ℤ → ℝ) (a b : ℤ × ℤ) (M i : ℕ) : ℝ :=
  N (meansPt a b M i - a) - N (meansPt a b M i - a - a)

variable {N : ℤ × ℤ → ℝ}

/-- The inequality (Q) at `(x, v, y, u) = (p, -p, q, -q)` and `(o, o', w, w') = (a, -a, b, -b)`,
divided by `4`: `N(p) ∂p + N(q) ∂'q ≤ τ (N(p)² + N(q)²) + (N(a)² + N(b)²)/(2τ)`. -/
private theorem lem_means_display (hN : CrossingLength N) (hh : IsHomogeneous N) (a b p q : ℤ × ℤ)
    {τ : ℝ} (hτ : 0 < τ) :
    N p * meansDiff N a b p + N q * meansDiff N a (-b) q ≤
      τ * (N p ^ 2 + N q ^ 2) + (N a ^ 2 + N b ^ 2) / (2 * τ) := by
  unfold meansDiff
  have h := hN.crossing p (-p) q (-q) a (-a) b (-b) τ hτ
  have e1 (Z : ℤ × ℤ) : N (Z - -Z) = 2 * N Z := by
    rw [show Z - -Z = 2 • Z by module, hh]
    norm_num
  have en (X Y : ℤ × ℤ) : N (-X - Y) = N (X - -Y) :=
    (congrArg N (by module : -X - Y = -(X - -Y))).trans (hN.neg _)
  have e6 : ((2 * N a) ^ 2 + (2 * N b) ^ 2) / (2 * τ) = 4 * ((N a ^ 2 + N b ^ 2) / (2 * τ)) := by
    ring
  rw [e1 p, e1 q, e1 a, e1 b, en p (-a), en p (-b), en q (-a), en q b, neg_neg, neg_neg, e6] at h
  linarith

/-- `∂A_i + ∂(A_i - a) = 2 (N(A_i) - N(A_i - c)) + δ_i - δ_{i+1}`, for every function `N`. -/
private theorem lem_means_identity (a b : ℤ × ℤ) (M i : ℕ) :
    meansDiff N a b (meansPt a b M i) + meansDiff N a b (meansPt a b M i - a) =
      2 * (N (meansPt a b M i) - N (meansPt a b M i - (a + b)))
        + (meansDelta N a b M i - meansDelta N a b M (i + 1)) := by
  simp only [meansDiff, meansDelta, meansPt,
    show M • (a + b) + (i + 1) • (a - b) - a = M • (a + b) + i • (a - b) - b by module,
    show M • (a + b) + i • (a - b) - b - a = M • (a + b) + i • (a - b) - (a + b) by module,
    show M • (a + b) + i • (a - b) - a - b = M • (a + b) + i • (a - b) - (a + b) by module]
  ring

/-- Since `t ↦ N(t c + i e)` is convex, the first difference on the right is at least
`f - 2 N(i e)/M`. Here `s` stands for `i e`, and convexity is used at the integers `t ≥ 0`: the
differences `N((t + 1) c + s) - N(t c + s)` do not decrease. -/
private theorem lem_means_convex (hN : CrossingLength N) (hh : IsHomogeneous N) (s c : ℤ × ℤ)
    (M : ℕ) (hM : 0 < M) :
    N c - 2 * N s / M ≤ N (M • c + s) - N (M • c + s - c) := by
  have hmono : Monotone fun t : ℕ => N ((t + 1) • c + s) - N (t • c + s) := by
    refine monotone_nat_of_le_succ fun t => ?_
    have h1 := hN.add ((t + 1 + 1) • c + s) (t • c + s)
    rw [show (t + 1 + 1) • c + s + (t • c + s) = 2 • ((t + 1) • c + s) by module, hh] at h1
    push_cast at h1
    linarith
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have h1 := Finset.sum_range_sub (fun t : ℕ => N (t • c + s)) (M + 1)
  have h2 : ∑ t ∈ range (M + 1), (N ((t + 1) • c + s) - N (t • c + s)) ≤
      ∑ t ∈ range (M + 1), (N ((M + 1) • c + s) - N (M • c + s)) :=
    Finset.sum_le_sum fun t ht => hmono (by simpa [Nat.lt_succ_iff] using ht)
  rw [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul (α := ℝ), zero_smul, zero_add] at h2
  have h3 := hN.sub_le ((M + 1) • c + s) s
  rw [add_sub_cancel_right, hh] at h3
  rw [show (M + 1) • c + s - c = M • c + s by module]
  have h5 : N c - 2 * N s / ((M + 1 : ℕ) : ℝ) =
      (((M + 1 : ℕ) : ℝ) * N c - 2 * N s) / ((M + 1 : ℕ) : ℝ) := by field_simp
  rw [h5, div_le_iff₀ (by positivity)]
  linarith

/-- The `δ_i` are bounded and telescope: the sum of `∂A_i + ∂(A_i - a)` over `0 ≤ i < R` is at least
`2R (f - 2R f'/M) - 2 N(a)`. -/
private theorem lem_means_telescope (hN : CrossingLength N) (hh : IsHomogeneous N) (a b : ℤ × ℤ)
    {M : ℕ} (hM : 0 < M) (R : ℕ) :
    2 * R * (N (a + b) - 2 * R * N (a - b) / M) - 2 * N a ≤
      ∑ i ∈ range R,
          (meansDiff N a b (meansPt a b M i) + meansDiff N a b (meansPt a b M i - a)) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have h2 : ∀ i ∈ range R, 2 * (N (a + b) - 2 * R * N (a - b) / M)
      + (meansDelta N a b M i - meansDelta N a b M (i + 1)) ≤
        meansDiff N a b (meansPt a b M i) + meansDiff N a b (meansPt a b M i - a) := by
    intro i hi
    rw [lem_means_identity]
    have h3 := lem_means_convex hN hh (i • (a - b)) (a + b) M hM
    rw [hh] at h3
    have h4 : 2 * ((i : ℝ) * N (a - b)) / M ≤ 2 * R * N (a - b) / M := by
      apply div_le_div_of_nonneg_right _ hM'.le
      have : (i : ℝ) ≤ R := by exact_mod_cast (Finset.mem_range.1 hi).le
      nlinarith [hN.nonneg (a - b)]
    simp only [meansPt]
    linarith
  have h5 := Finset.sum_le_sum h2
  rw [Finset.sum_add_distrib, Finset.sum_range_sub', Finset.sum_const, Finset.card_range,
    nsmul_eq_mul (α := ℝ)] at h5
  unfold meansDelta at h5
  linarith [hN.le_sub_add (meansPt a b M R - a) a, hN.sub_le (meansPt a b M 0 - a) a]

/-- `N(p) = M f + O(R)` at the points `p = M c + i e` and `p = M c + i e - a` with `i < R`: the
error is at most `2 R κ` if `N(a), N(e) ≤ κ`. -/
private theorem lem_means_near (hN : CrossingLength N) (hh : IsHomogeneous N)
    {a c e : ℤ × ℤ} {κ : ℝ} (ha : N a ≤ κ) (he : N e ≤ κ)
    (M : ℕ) {R i : ℕ} (hi : i < R) :
    |N (M • c + i • e) - M * N c| ≤ 2 * R * κ ∧ |N (M • c + i • e - a) - M * N c| ≤ 2 * R * κ := by
  have hi' : (i : ℝ) + 1 ≤ R := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  rw [← hh]
  constructor
  · have h1 := hN.abs_sub_le (M • c + i • e) (M • c)
    rw [add_sub_cancel_left, hh i e] at h1
    nlinarith [hN.nonneg e]
  · have h1 := hN.abs_sub_le (M • c + i • e - a) (M • c)
    rw [show M • c + i • e - a - M • c = i • e - a by module] at h1
    have h3 := hh i e ▸ hN.sub_le (i • e) a
    nlinarith [hN.nonneg e]

/-- `∂` is bounded by `N(a) + N(b)`, so `N(p) ∂p = M f ∂p + O(R)`, and the same for `∂'` at `q` with
`f'`. With `τ = 1/(2M)` the display becomes
`M f ∂p + M f' ∂'q ≤ M (½ (f² + f'²) + N(a)² + N(b)²) + O(R)`. Here the points `p, q` have
`N(p) = M f + O(R)` and `N(q) = M f' + O(R)` with errors at most `2Rκ`, and the last `O(R)` is
`12 R κ²`. -/
private theorem lem_means_estimate (hN : CrossingLength N) (hh : IsHomogeneous N)
    (a b p q c e : ℤ × ℤ) {M R : ℕ} {κ : ℝ} (hM : 0 < M)
    (hR : R ≤ M) (hκ : N a + N b ≤ κ) (hc : N c ≤ κ) (he : N e ≤ κ)
    (hp : |N p - M * N c| ≤ 2 * R * κ) (hq : |N q - M * N e| ≤ 2 * R * κ) :
    M * N c * meansDiff N a b p + M * N e * meansDiff N a (-b) q ≤
      M * ((N c ^ 2 + N e ^ 2) / 2 + (N a ^ 2 + N b ^ 2)) + 12 * R * κ ^ 2 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hR' : (R : ℝ) ≤ M := by exact_mod_cast hR
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hκ0 : 0 ≤ κ := (hN.nonneg c).trans hc
  have h1 := lem_means_display hN hh a b p q (τ := 1 / (2 * M)) (by positivity)
  have e1 : (N a ^ 2 + N b ^ 2) / (2 * (1 / (2 * (M : ℝ)))) = M * (N a ^ 2 + N b ^ 2) := by
    field_simp
  rw [e1] at h1
  have hdiff (u z : ℤ × ℤ) (hz : N a + N z ≤ κ) : |meansDiff N a z u| ≤ κ := by
    unfold meansDiff
    have h2 := hN.abs_sub_le u (u - a)
    have h3 := hN.abs_sub_le u (u - z)
    rw [sub_sub_cancel, abs_le] at h2 h3
    rw [abs_le]
    constructor <;> linarith
  have low (A B x : ℝ) (hA : |A - B| ≤ 2 * R * κ) (hx : |x| ≤ κ) :
      B * x - 2 * R * κ ^ 2 ≤ A * x := by
    have h2 := (abs_le.1 (abs_mul (A - B) x ▸
      mul_le_mul hA hx (abs_nonneg _) (by positivity))).1
    nlinarith
  have sq (Z c : ℤ × ℤ) (hc : N c ≤ κ) (hZ : |N Z - M * N c| ≤ 2 * R * κ) :
      1 / (2 * M) * N Z ^ 2 ≤ M * N c ^ 2 / 2 + 4 * R * κ ^ 2 := by
    have h3 : N Z ^ 2 ≤ (M * N c + 2 * R * κ) ^ 2 :=
      pow_le_pow_left₀ (hN.nonneg Z) (by linarith [(abs_le.1 hZ).2]) 2
    have h5 : (M : ℝ) * R * (N c * κ) ≤ M * R * (κ * κ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hκ0) (by positivity)
    have h6 : (R : ℝ) * R * κ ^ 2 ≤ M * R * κ ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hR' hR0) (sq_nonneg _)
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  linarith [low _ _ _ hp (hdiff p b hκ), low _ _ _ hq (hdiff q (-b) (by rwa [hN.neg])),
    sq _ _ hc hp, sq _ _ he hq]

/-- The arithmetic of averaging over `i` and dividing by `2M`, with `M = m²`, `f, f', n = N(a)` at
most `κ`, and `Q = N(a)² + N(b)²`. -/
private theorem means_arith {m f f' n Q κ : ℝ} (hm : 0 < m) (hf0 : 0 ≤ f) (hf : f ≤ κ)
    (hf0' : 0 ≤ f') (hf' : f' ≤ κ)
    (hn0 : 0 ≤ n) (hn : n ≤ κ)
    (h : m ^ 2 * f * (2 * m * (f - 2 * m * f' / m ^ 2) - 2 * n)
        + m ^ 2 * f' * (2 * m * (f' - 2 * m * f / m ^ 2) - 2 * n) ≤
      m * (m ^ 2 * ((f ^ 2 + f' ^ 2) / 2 + Q) + 12 * m * κ ^ 2
        + (m ^ 2 * ((f ^ 2 + f' ^ 2) / 2 + Q) + 12 * m * κ ^ 2))) :
    f ^ 2 + f' ^ 2 ≤ 2 * Q + 36 * κ ^ 2 * (1 / m) := by
  have hκ0 : 0 ≤ κ := hf0.trans hf
  have el (x y : ℝ) : m ^ 2 * x * (2 * m * (x - 2 * m * y / m ^ 2) - 2 * n) =
      2 * m ^ 3 * x ^ 2 - 4 * (x * y) * m ^ 2 - 2 * (x * n) * m ^ 2 := by
    field_simp
    ring
  rw [el f f', el f' f, mul_comm f' f] at h
  refine le_of_mul_le_mul_left (a := m ^ 3) ?_ (by positivity)
  have e5 : m ^ 3 * (2 * Q + 36 * κ ^ 2 * (1 / m)) = 2 * m ^ 3 * Q + 36 * κ ^ 2 * m ^ 2 := by
    field_simp
  rw [e5]
  nlinarith [mul_le_mul hf hf' hf0' hκ0, mul_le_mul hf hn hn0 hκ0, mul_le_mul hf' hn hn0 hκ0,
    sq_nonneg m]

/-- With `τ = 1/(2M)`, adding the two inequalities, averaging over `i` and dividing by `2M` gives
`f² + f'² ≤ ½ (f² + f'²) + N(a)² + N(b)² + O(1/R)`, where `M = R²`. Here the inequality is doubled
and `½ (f² + f'²)` is subtracted, and the `O(1/R)` is `36 (N(a) + N(b))²/R`. -/
private theorem lem_means_average (hN : CrossingLength N) (hh : IsHomogeneous N) (a b : ℤ × ℤ)
    {R : ℕ} (hR : 0 < R) :
    N (a + b) ^ 2 + N (a - b) ^ 2 ≤ 2 * (N a ^ 2 + N b ^ 2) + 36 * (N a + N b) ^ 2 *
        (1 / (R : ℝ)) := by
  set κ := N a + N b with hκ
  have hc : N (a + b) ≤ κ := hN.add a b
  have he : N (a - b) ≤ κ := hN.sub_le a b
  have ha : N a ≤ κ := by linarith [hN.nonneg b]
  have hM : 0 < R ^ 2 := by positivity
  have hRM : R ≤ R ^ 2 := by nlinarith
  have s1 := lem_means_telescope hN hh a b hM R
  have s2 := lem_means_telescope hN hh a (-b) hM R
  simp only [meansPt] at s1 s2
  rw [sub_neg_eq_add, ← sub_eq_add_neg] at s2
  have p : ∀ i ∈ range R, _ := fun i hi => add_le_add
    (lem_means_estimate hN hh a b _ _ (a + b) (a - b) hM hRM le_rfl hc he
      (lem_means_near hN hh ha he _ (Finset.mem_range.1 hi)).1
          (lem_means_near hN hh ha hc _ (Finset.mem_range.1 hi)).1)
    (lem_means_estimate hN hh a b _ _ (a + b) (a - b) hM hRM le_rfl hc he
      (lem_means_near hN hh ha he _ (Finset.mem_range.1 hi)).2
          (lem_means_near hN hh ha hc _ (Finset.mem_range.1 hi)).2)
  have hp := Finset.sum_le_sum p
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul (α := ℝ)] at hp
  have hp2 : ((R ^ 2 : ℕ) : ℝ) * N (a + b) *
        (2 * R * (N (a + b) - 2 * R * N (a - b) / (R ^ 2 : ℕ)) - 2 * N a)
      + ((R ^ 2 : ℕ) : ℝ) * N (a - b) *
        (2 * R * (N (a - b) - 2 * R * N (a + b) / (R ^ 2 : ℕ)) - 2 * N a) ≤
      R * (((R ^ 2 : ℕ) : ℝ) * ((N (a + b) ^ 2 + N (a - b) ^ 2) / 2 + (N a ^ 2 + N b ^ 2))
        + 12 * R * κ ^ 2 + (((R ^ 2 : ℕ) : ℝ) * ((N (a + b) ^ 2 + N (a - b) ^ 2) / 2
        + (N a ^ 2 + N b ^ 2)) + 12 * R * κ ^ 2)) := by
    refine le_trans ?_ hp
    refine le_trans (add_le_add
      (mul_le_mul_of_nonneg_left s1 (mul_nonneg (Nat.cast_nonneg _) (hN.nonneg _)))
      (mul_le_mul_of_nonneg_left s2 (mul_nonneg (Nat.cast_nonneg _) (hN.nonneg _)))) ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => le_of_eq (by ring)
  push_cast at hp2
  exact means_arith (by exact_mod_cast hR) (hN.nonneg _) hc (hN.nonneg _) he (hN.nonneg _) ha hp2

/-- Hence `N(a + b)² + N(a - b)² ≤ 2 N(a)² + 2 N(b)²`. -/
private theorem lem_means_parallelogram_le (hN : CrossingLength N) (hh : IsHomogeneous N)
    (a b : ℤ × ℤ) :
    N (a + b) ^ 2 + N (a - b) ^ 2 ≤ 2 * (N a ^ 2 + N b ^ 2) := by
  have h1 := (tendsto_one_div_atTop_nhds_zero_nat.const_mul (36 * (N a + N b) ^ 2)).const_add
    (2 * (N a ^ 2 + N b ^ 2))
  rw [mul_zero, add_zero] at h1
  exact ge_of_tendsto h1 ((eventually_gt_atTop 0).mono fun R => lem_means_average hN hh a b)

end Parallelogram

/-- The parallelogram law `N(a + b)² + N(a - b)² = 2 N(a)² + 2 N(b)²` for a homogeneous crossing
length: the inequality applied to `a + b, a - b` gives the converse. -/
theorem _root_.Cslib.Circuits.Arithmetic.Separation.CrossingLength.parallelogram
    {N : ℤ × ℤ → ℝ} (hN : CrossingLength N) (hh : IsHomogeneous N) (a b : ℤ × ℤ) :
    N (a + b) ^ 2 + N (a - b) ^ 2 = 2 * N a ^ 2 + 2 * N b ^ 2 := by
  refine le_antisymm (by linarith [lem_means_parallelogram_le hN hh a b]) ?_
  have h := lem_means_parallelogram_le hN hh (a + b) (a - b)
  rw [show a + b + (a - b) = (2 : ℕ) • a by rw [two_nsmul]; abel,
    show a + b - (a - b) = (2 : ℕ) • b by rw [two_nsmul]; abel, hh, hh] at h
  push_cast at h
  linarith

/-- **Paper: Lemma C.2.** For prices `W n` on two sheets of `ℤ²` with
`W n (P, P + g) ≤ Λ |g|` for points of one sheet, and `N(g) = inf ν(S g)/S`, which is also the limit
of `ν(S g)/S`, the parallelogram law `N(a + b)² + N(a - b)² = 2 N(a)² + 2 N(b)²` holds for all
`a, b ∈ ℤ²`. -/
theorem meanNorm_parallelogram (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|))
    (a b : ℤ × ℤ) :
    meanNorm W (a + b) ^ 2 + meanNorm W (a - b) ^ 2 = 2 * meanNorm W a ^ 2 + 2 * meanNorm W b ^
        2 := by
  rw [meanNorm_eq_homogenization hW hΛ]
  set hν := crossingLength_meanLength hW hΛ
  exact hν.crossingLength_homogenization.parallelogram hν.isHomogeneous_homogenization a b

/-- `ν(S g)/S` converges to `N(g)`. -/
theorem tendsto_meanLength_div (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|))
    (g : ℤ × ℤ) :
    Tendsto (fun S : ℕ => meanLength W (S • g) / S) atTop (𝓝 (meanNorm W g)) :=
  meanNorm_eq_homogenization hW hΛ ▸ (crossingLength_meanLength hW hΛ).tendsto_homogenization g

end Cslib.Circuits.Arithmetic.Separation.Curvature
