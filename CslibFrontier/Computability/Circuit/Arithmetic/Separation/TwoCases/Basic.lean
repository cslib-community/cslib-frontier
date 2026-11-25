/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Para
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Price.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The two cases: Definition D.1

For a function `w` on the pairs of `μ × μ` matrices over `F₂`, `TwoCases.distAtRank w r` is the
paper's `D(r)`: the root mean square of `w a (a + W)` over all matrices `a` and all matrices `W`
of rank `r`. Its square `TwoCases.meanSq w r` is the mean over `a` of `TwoCases.rankMean`, the
mean square of a function over the matrices of one rank. A field `K` is in the *flat case*
(`TwoCases.FlatCase`) if the metrics of all finite families of points of Euclidean spaces are
prices, and in the *contracting case* (`TwoCases.ContractingCase`) if `D(μ) ≤ s D(1)` for all
prices on `Mat_μ(F₂)`, for some `μ ≥ 2` and `1 ≤ s` with `s² < μ`.

The matrices `p · dg S · q`, for uniform invertible `p` and `q`, are uniform among the matrices of
rank `|S|`: the sum `Flag.DM f (dg S)` over all `p` and `q` is `|GL_μ(F₂)|²` times the mean
(`TwoCases.DM_dg_eq`).

## Main definitions

* `TwoCases.rankMean`, `TwoCases.meanSq`, `TwoCases.distAtRank`: `D(r)` and its square.
* `TwoCases.FlatCase`, `TwoCases.ContractingCase`: Definition D.1.

## Main results

* `TwoCases.DM_dg_eq`: sums over the frames are means over a rank.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Section D.1 and Definition D.1, pp. 29–30; modules `Paper.Alternative` and `Nc.Flag.Cases`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TwoCases

open Finset Matrix Cslib.PartyTensor Cslib.Circuits.Arithmetic.Separation.Flag

variable {μ : ℕ}

/-- The mean of `f W ^ 2` over the matrices `W` of rank `r` (`0` if there are none). -/
@[expose] noncomputable def rankMean (f : Mt μ → ℝ) (r : ℕ) : ℝ :=
  (∑ W : Mt μ with W.rank = r, f W ^ 2) / #{W : Mt μ | W.rank = r}

/-- The square of the paper's `D(r)`: the mean of `w a (a + W) ^ 2` over all matrices `a` and all
matrices `W` of rank `r`. -/
@[expose] noncomputable def meanSq (w : Mt μ → Mt μ → ℝ) (r : ℕ) : ℝ :=
  (∑ a, rankMean (fun W => w a (a + W)) r) / Fintype.card (Mt μ)

/-- The paper's `D(r)` (Section D.1, p. 29): the root mean square of `w a (a + W)` over all
matrices `a` and all matrices `W` of rank `r`. -/
@[expose] noncomputable def distAtRank (w : Mt μ → Mt μ → ℝ) (r : ℕ) : ℝ := √(meanSq w r)

/-- **Paper: Definition D.1, the flat hypothesis** (p. 30): all finite subsets of all Euclidean
spaces, with their metrics, are prices. Stated for finite families of points, repetitions
allowed, which is the same. -/
@[expose] def FlatCase (K : Type) [Field K] : Prop :=
  ∀ (k : ℕ) (V : Type) [Finite V] (E : V → EuclideanSpace ℝ (Fin k)),
    IsPrice K fun a b => dist (E a) (E b)

/-- **Paper: Definition D.1, the contracting hypothesis** (p. 30): there are an integer `μ ≥ 2`
and a real `s` with `1 ≤ s` and `s² < μ` such that `D(μ) ≤ s D(1)` for all prices on
`Mat_μ(F₂)`. -/
@[expose] def ContractingCase (K : Type) [Field K] : Prop :=
  ∃ (μ : ℕ) (s : ℝ), 2 ≤ μ ∧ 1 ≤ s ∧ s ^ 2 < μ ∧
    ∀ w : Mt μ → Mt μ → ℝ, IsPrice K w → distAtRank w μ ≤ s * distAtRank w 1

theorem rankMean_nonneg (f : Mt μ → ℝ) (r : ℕ) : 0 ≤ rankMean f r := by
  unfold rankMean
  positivity

theorem meanSq_nonneg (w : Mt μ → Mt μ → ℝ) (r : ℕ) : 0 ≤ meanSq w r :=
  div_nonneg (sum_nonneg fun _ _ => rankMean_nonneg _ _) (Nat.cast_nonneg _)

theorem distAtRank_sq (w : Mt μ → Mt μ → ℝ) (r : ℕ) : distAtRank w r ^ 2 = meanSq w r :=
  Real.sq_sqrt (meanSq_nonneg w r)

/-- The matrix of a set of indices in a frame has the rank of the size of the set. -/
theorem rank_X (p q : GLM (Fin μ)) (S : Finset (Fin μ)) : (X p q S).rank = S.card := by
  rw [X, rank_mul_eq_left_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1 q.isUnit),
    rank_mul_eq_right_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1 p.isUnit), dg,
    rank_diagonal, Fintype.card_subtype]
  congr 1
  ext i
  simp

/-- For uniform invertible `p` and `q`, the matrix `p · dg S · q` is uniform among the matrices
of rank `|S|`: the sum of `f (p · dg S · q) ^ 2` over all `p` and `q` is `|GL_μ(F₂)|²` times
`rankMean f |S|`. -/
theorem DM_dg_eq (f : Mt μ → ℝ) (S : Finset (Fin μ)) :
    DM f (dg S) = (Fintype.card (GLM (Fin μ)) : ℝ) ^ 2 * rankMean f S.card := by
  have hne : (#{W : Mt μ | W.rank = S.card} : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (card_ne_zero.2 ⟨X 1 1 S, by simp [rank_X]⟩)
  rw [rankMean, mul_div_assoc', eq_div_iff hne]
  calc DM f (dg S) * #{W : Mt μ | W.rank = S.card}
      = ∑ W : Mt μ with W.rank = S.card, DM f W := by
        rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
        refine sum_congr rfl fun W hW => ?_
        obtain ⟨p, q, T, rfl⟩ := exists_X W
        rw [mem_filter, rank_X] at hW
        rw [X, DM_mul, DM_dg_congr f hW.2.symm]
    _ = ∑ p : GLM (Fin μ), ∑ q : GLM (Fin μ), ∑ W : Mt μ with W.rank = S.card, f W ^ 2 := by
        unfold DM
        rw [sum_comm]
        refine sum_congr rfl fun p _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun q _ => ?_
        simp only [sum_filter]
        refine Fintype.sum_equiv ((Units.mulLeft p).trans (Units.mulRight q)) _ _ fun W => ?_
        simp only [Equiv.trans_apply, Units.mulLeft_apply, Units.mulRight_apply,
          rank_mul_eq_left_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1 q.isUnit),
          rank_mul_eq_right_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1 p.isUnit)]
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]; ring

end Cslib.Circuits.Arithmetic.Separation.TwoCases
