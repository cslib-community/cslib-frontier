/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The perceptron mistake bound

The **perceptron** [Novikoff1962] [Block1962] [ShalevShwartzBenDavid2014, §21.4] is an online
learner on a real inner product space `E`. It keeps a weight vector `w`, starting at `0`, predicts
`true` on `x` iff `0 < ⟪w, x⟫`, and on a mistake on the example `(x, y)` updates
`w ← w + s(y) • x`, where `s(y) = ±1` is the signed label (`signedLabel`). The weight vector is a
function of the history (`perceptronWeight`), so the perceptron is an `OnlineLearner E Bool`.

**Novikoff's theorem.** Suppose that some `u : E` separates the sequence with margin `γ ≥ 0`, that
is, `γ ≤ s(y) ⟪u, x⟫` for every example, and that every instance has norm at most `R`. Then the
number `M` of mistakes satisfies `M γ² ≤ R² ‖u‖²` (`mistakes_perceptron_mul_sq_le`). For a unit
separator and `γ > 0`, this is `M ≤ (R / γ)²` (`mistakes_perceptron_le`), independent of the length
of the sequence and of the dimension of `E`. The proof tracks two quantities over the mistakes:
`⟪u, w⟫` grows by at least `γ` per mistake, while `‖w‖²` grows by at most `R²` because the
prediction was wrong; Cauchy–Schwarz combines them.

The hypothesis `0 ≤ γ` is needed: with `u = 0` and `γ < 0` the margin condition holds for every
sequence, while the bound `M γ² ≤ 0` fails as soon as the perceptron errs. A positive margin makes
the sequence realizable by the halfspace `x ↦ decide (0 < ⟪u, x⟫)` (`realizable_of_margin`). The
bound is stated per sequence: the margin is a property of the instances presented, not only of the
target concept.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.signedLabel`: the `±1` encoding of labels.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.perceptronWeight`: the weight vector after a
  history.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.perceptron`: the perceptron as an online
  learner.

## Main results

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.mistakes_perceptron_mul_sq_le`: Novikoff's
  bound `M γ² ≤ R² ‖u‖²`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.mistakes_perceptron_le`: `M ≤ (R / γ)²` for
  a unit separator.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.realizable_of_margin`: a positive margin makes
  the sequence realizable by a halfspace.

## References

* [H. D. Block, *The perceptron: a model for brain functioning. I*][Block1962]
* [A. B. J. Novikoff, *On convergence proofs on perceptrons*][Novikoff1962]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.MistakeBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open RealInnerProductSpace

/-- The `±1` encoding of a Boolean label: `true ↦ 1`, `false ↦ -1`. -/
def signedLabel (y : Bool) : ℝ := if y then 1 else -1

@[simp] theorem signedLabel_true : signedLabel true = 1 := by
  simp [signedLabel]

@[simp] theorem signedLabel_false : signedLabel false = -1 := by
  simp [signedLabel]

theorem signedLabel_sq (y : Bool) : signedLabel y ^ 2 = 1 := by cases y <;> norm_num

/-- One step of the perceptron on the example `p = (x, y)`: keep `w` if its prediction
`0 < ⟪w, x⟫` is correct, and otherwise add `s(y) • x`. -/
@[expose] noncomputable def perceptronStep (w : E) (p : E × Bool) : E :=
  if decide (0 < ⟪w, p.1⟫) = p.2 then w else w + signedLabel p.2 • p.1

/-- The perceptron's weight vector after the history `h`, starting from `0`. -/
@[expose] noncomputable def perceptronWeight (h : List (E × Bool)) : E := h.foldl perceptronStep 0

/-- The perceptron [Novikoff1962] [ShalevShwartzBenDavid2014, §21.4]: predict `true` on `x` iff
`0 < ⟪w, x⟫` for the current weight vector `w`. -/
@[expose] noncomputable def perceptron : OnlineLearner E Bool := fun h x =>
  decide (0 < ⟪perceptronWeight h, x⟫)

@[simp] theorem perceptronWeight_nil : perceptronWeight ([] : List (E × Bool)) = 0 := rfl

theorem perceptronWeight_append_singleton (h : List (E × Bool)) (p : E × Bool) :
    perceptronWeight (h ++ [p]) = perceptronStep (perceptronWeight h) p := by
  simp [perceptronWeight, List.foldl_append]

/-- The two invariants of the perceptron after the history `h`, over the rounds `S`: each mistake
increases `⟪u, w⟫` by at least `γ` and `‖w‖²` by at most `R²`. -/
theorem perceptron_invariant (u : E) {γ R : ℝ} (h S : List (E × Bool))
    (hmargin : ∀ p ∈ S, γ ≤ signedLabel p.2 * ⟪u, p.1⟫) (hR : ∀ p ∈ S, ‖p.1‖ ≤ R) :
    ⟪u, perceptronWeight h⟫ + mistakesFrom perceptron h S * γ ≤
        ⟪u, perceptronWeight (h ++ S)⟫ ∧
      ‖perceptronWeight (h ++ S)‖ ^ 2 ≤
        ‖perceptronWeight h‖ ^ 2 + mistakesFrom perceptron h S * R ^ 2 := by
  induction S generalizing h with
  | nil => simp
  | cons p S ih =>
    obtain ⟨x, y⟩ := p
    obtain ⟨ih1, ih2⟩ := ih (h ++ [(x, y)]) (fun p hp => hmargin p (List.mem_cons_of_mem _ hp))
      (fun p hp => hR p (List.mem_cons_of_mem _ hp))
    have hm := hmargin (x, y) List.mem_cons_self
    have hx := hR (x, y) List.mem_cons_self
    rw [show h ++ (x, y) :: S = (h ++ [(x, y)]) ++ S by simp, mistakesFrom_cons]
    simp only [perceptronWeight_append_singleton, perceptronStep] at ih1 ih2
    by_cases hc : perceptron h x = y
    · have hc' : (decide (0 < ⟪perceptronWeight h, x⟫) = y) := hc
      rw [ite_eq_left hc'] at ih1 ih2
      simpa only [hc, ↓reduceIte, zero_add] using And.intro ih1 ih2
    · -- the update increases `⟪u, w⟫` by `s(y) ⟪u, x⟫ ≥ γ`
      have hc' : ¬(decide (0 < ⟪perceptronWeight h, x⟫) = y) := hc
      rw [ite_eq_right hc', inner_add_right, real_inner_smul_right] at ih1
      rw [ite_eq_right hc'] at ih2
      simp only [hc, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      -- the cross term is nonpositive on a mistake
      have hcross : signedLabel y * ⟪perceptronWeight h, x⟫ ≤ 0 := by
        cases y <;> simp only [perceptron, decide_eq_true_eq, decide_eq_false_iff_not,
          not_lt, signedLabel_true, signedLabel_false] at hc ⊢
        · linarith
        · linarith
      have hnorm : ‖perceptronWeight h + signedLabel y • x‖ ^ 2 ≤
          ‖perceptronWeight h‖ ^ 2 + R ^ 2 := by
        rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
          sq_abs, signedLabel_sq, one_mul]
        nlinarith [pow_le_pow_left₀ (norm_nonneg x) hx 2]
      exact ⟨by nlinarith, by nlinarith⟩

/-- **Novikoff's perceptron convergence theorem** [Novikoff1962] [Block1962]
[ShalevShwartzBenDavid2014, §21.4]: if `u` separates the sequence `S` with margin `γ ≥ 0` and all
instances have norm at most `R`, then the perceptron makes `M` mistakes on `S` with
`M γ² ≤ R² ‖u‖²`. -/
theorem mistakes_perceptron_mul_sq_le (u : E) {γ R : ℝ} (hγ : 0 ≤ γ) (S : List (E × Bool))
    (hmargin : ∀ p ∈ S, γ ≤ signedLabel p.2 * ⟪u, p.1⟫) (hR : ∀ p ∈ S, ‖p.1‖ ≤ R) :
    mistakes perceptron S * γ ^ 2 ≤ R ^ 2 * ‖u‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := perceptron_invariant u [] S hmargin hR
  simp only [List.nil_append, perceptronWeight_nil, inner_zero_right, zero_add,
    norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h1 h2
  change (mistakes perceptron S : ℝ) * γ ≤ _ at h1
  change _ ≤ (mistakes perceptron S : ℝ) * R ^ 2 at h2
  set m : ℝ := (mistakes perceptron S : ℝ)
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hsq : (m * γ) ^ 2 ≤ ‖u‖ ^ 2 * ‖perceptronWeight S‖ ^ 2 :=
    mul_pow ‖u‖ _ 2 ▸ pow_le_pow_left₀ (mul_nonneg hm0 hγ)
      (h1.trans (real_inner_le_norm u _)) 2
  rcases hm0.lt_or_eq with hpos | hzero
  · refine le_of_mul_le_mul_left ?_ hpos
    rw [mul_pow] at hsq
    nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg ‖u‖)]
  · rw [← hzero, zero_mul]
    positivity

/-- The perceptron bound for a separator of norm at most `1` and margin `γ > 0`: at most
`(R / γ)²` mistakes [ShalevShwartzBenDavid2014, §21.4]. -/
theorem mistakes_perceptron_le (u : E) (hu : ‖u‖ ≤ 1) {γ R : ℝ} (hγ : 0 < γ)
    (S : List (E × Bool)) (hmargin : ∀ p ∈ S, γ ≤ signedLabel p.2 * ⟪u, p.1⟫)
    (hR : ∀ p ∈ S, ‖p.1‖ ≤ R) :
    (mistakes perceptron S : ℝ) ≤ (R / γ) ^ 2 := by
  rw [div_pow, le_div_iff₀ (by positivity)]
  nlinarith [mistakes_perceptron_mul_sq_le u hγ.le S hmargin hR,
    pow_le_pow_left₀ (norm_nonneg u) hu 2, sq_nonneg R]

/-- A sequence separated by `u` with a positive margin is realizable by the halfspace
`x ↦ decide (0 < ⟪u, x⟫)`. -/
theorem realizable_of_margin (u : E) {γ : ℝ} (hγ : 0 < γ) (S : List (E × Bool))
    (hmargin : ∀ p ∈ S, γ ≤ signedLabel p.2 * ⟪u, p.1⟫) :
    Realizable {fun x => decide (0 < ⟪u, x⟫)} S := by
  refine realizable_iff.mpr ⟨_, rfl, fun ⟨x, y⟩ hp => ?_⟩
  have h := hmargin (x, y) hp
  cases y <;> simp only [signedLabel_false, signedLabel_true, neg_one_mul, one_mul,
    decide_eq_false_iff_not, decide_eq_true_eq, not_lt] at h ⊢
  · linarith
  · linarith

end Cslib.MachineLearning.OnlineLearning.MistakeBound
