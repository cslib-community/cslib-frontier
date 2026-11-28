/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, with `Mathlib/Analysis/LaplaceTransform.lean`)

public import CslibFrontier.Foundations.Analysis.LaplaceTransform.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Convolution

/-!
# The convolution theorem for the Laplace transform

For a continuous bilinear pairing `L : E →L[ℂ] F →L[ℂ] G` the **causal convolution** of
`f : ℝ → E` and `g : ℝ → F` is `causalConvolution L f g t = ∫ τ in 0..t, L (f (t - τ)) (g τ)`
(`causalConvolution`). The pairing lets a matrix kernel act on a vector input, as in the output
formula `y = D u + ∫ τ in 0..t, h (t - τ) u τ` of an LTI system.

**The convolution theorem** (`laplace_causalConvolution`): wherever the Laplace transforms of `f`
and `g` both converge (absolutely, as always here), so does that of the causal convolution, and
`laplace (causalConvolution L f g) s = L (laplace f s) (laplace g s)`. No continuity or growth
hypothesis is needed beyond convergence at `s`.

The proof reduces to Mathlib's convolution over `ℝ` (`MeasureTheory.convolution`) of the causal
extensions `(Ioi 0).indicator (exp (-s t) • f t)` and `(Ioi 0).indicator (exp (-s t) • g t)`, and
Mathlib's `MeasureTheory.integral_convolution` (Fubini).

## Main definitions

* `causalConvolution L f g t = ∫ τ in 0..t, L (f (t - τ)) (g τ)`.

## Main results

* `laplaceConvergent_causalConvolution`, `laplace_causalConvolution`.

## References

* [Widder1941], Chapter II, §12, Definition 12 and Theorem 12.1a, pp. 91–92: for scalar
  `a`, `b` integrable on every `(0, R)`, the resultant `c(t) = ∫₀^t a(t - u) b(u) du` satisfies
  `∫₀^∞ e^{-s₀t} a(t) dt · ∫₀^∞ e^{-s₀t} b(t) dt = ∫₀^∞ e^{-s₀t} c(t) dt` when both factors
  converge absolutely, and then the right side converges absolutely. Compare
  `laplace_causalConvolution` and `laplaceConvergent_causalConvolution`, which pair
  vector-valued functions by a bilinear map and use Bochner integrals. Widder derives it from the
  Laplace–Stieltjes product theorem (§11, Theorem 11.5, p. 88); Theorems 12.1b and 12.1c, p. 92,
  weaken absolute convergence, which is not done here.
* S. Boyd, *EE263: Introduction to Linear Dynamical Systems*, Stanford, lecture notes
  "Linear dynamical systems with inputs & outputs" (Stanford Engineering Everywhere handout
  `13-lin-sys.pdf`), slide 13–8: with zero initial state `Y(s) = H(s) U(s)` and `y = h ∗ u`, the
  convolution theorem for the matrix-valued kernel of an LTI system.
-/

public section

open MeasureTheory Set

open scoped Convolution

noncomputable section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The **causal convolution** `t ↦ ∫ τ in 0..t, L (f (t - τ)) (g τ)` of `f` and `g` with respect
to a continuous bilinear pairing `L`. For `t ≥ 0` it uses only the values of `f` and `g` on
`[0, t]`. -/
@[expose] def causalConvolution (L : E →L[ℂ] F →L[ℂ] G) (f : ℝ → E) (g : ℝ → F) (t : ℝ) : G :=
  ∫ τ in 0..t, L (f (t - τ)) (g τ)

variable (L : E →L[ℂ] F →L[ℂ] G) {f : ℝ → E} {g : ℝ → F} {s : ℂ}

/-- The causal convolution in terms of the convolution over `ℝ` of the damped causal
extensions. -/
private theorem convolution_indicator_eq (t : ℝ) :
    (((Ioi (0 : ℝ)).indicator fun τ => Complex.exp (-s * τ) • g τ) ⋆[L.flip, volume]
        (Ioi (0 : ℝ)).indicator fun τ => Complex.exp (-s * τ) • f τ) t =
      (Ioi (0 : ℝ)).indicator
        (fun t => Complex.exp (-s * t) • causalConvolution L f g t) t := by
  rw [convolution_def]
  have h : (fun τ => L.flip ((Ioi (0 : ℝ)).indicator (fun τ => Complex.exp (-s * τ) • g τ) τ)
      ((Ioi (0 : ℝ)).indicator (fun τ => Complex.exp (-s * τ) • f τ) (t - τ))) =
      (Ioo 0 t).indicator fun τ => Complex.exp (-s * t) • L (f (t - τ)) (g τ) := by
    funext τ
    have key : ∀ X : G, Complex.exp (-(s * (t - τ))) • Complex.exp (-(s * τ)) • X =
        Complex.exp (-(s * t)) • X := fun X => by
      rw [smul_smul, ← Complex.exp_add]
      congr 2
      ring
    simp only [indicator_apply, mem_Ioi, mem_Ioo, sub_pos]
    split_ifs <;> simp_all
  rw [h, integral_indicator measurableSet_Ioo, integral_smul]
  by_cases ht : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht), causalConvolution,
      intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo]
  · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht), Ioo_eq_empty (by simpa using ht),
      Measure.restrict_empty, integral_zero_measure, smul_zero]

/-- **Convergence of the transform of a causal convolution.** If the Laplace transforms of `f`
and `g` converge at `s`, so does that of their causal convolution. -/
theorem laplaceConvergent_causalConvolution (hf : LaplaceConvergent f s)
    (hg : LaplaceConvergent g s) : LaplaceConvergent (causalConvolution L f g) s := by
  have hf' := (integrable_indicator_iff measurableSet_Ioi).2 hf
  have hg' := (integrable_indicator_iff measurableSet_Ioi).2 hg
  have h := hg'.integrable_convolution L.flip hf'
  rw [LaplaceConvergent, ← integrable_indicator_iff measurableSet_Ioi]
  exact h.congr (ae_of_all _ (convolution_indicator_eq L))

/-- **The convolution theorem.** If the Laplace transforms of `f` and `g` converge at `s`, then
`laplace (causalConvolution L f g) s = L (laplace f s) (laplace g s)`. -/
theorem laplace_causalConvolution [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    laplace (causalConvolution L f g) s = L (laplace f s) (laplace g s) := by
  have hf' := (integrable_indicator_iff measurableSet_Ioi).2 hf
  have hg' := (integrable_indicator_iff measurableSet_Ioi).2 hg
  have h := integral_convolution (L := L.flip) (μ := volume) (ν := volume) hg' hf'
  simp_rw [convolution_indicator_eq, integral_indicator measurableSet_Ioi] at h
  exact h

end
