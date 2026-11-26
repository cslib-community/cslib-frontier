/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Copositive
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Motzkin–Straus theorem

For a finite simple graph `G` on a nonempty vertex type `V` with clique number `ω(G)`, the
maximum of the quadratic form `x ⬝ᵥ G.adjMatrix K *ᵥ x` over the standard simplex
`Convexity.StdSimplex K V` equals `1 - 1 / ω(G)` (note that [MotzkinStraus1965] sums over
unordered edges `∑_{ij ∈ E} x_i x_j = (1 / 2) * (x ⬝ᵥ G.adjMatrix K *ᵥ x)`, differing by a factor
of `2`). This generalizes the real Motzkin–Straus theorem (attributed to [MotzkinStraus1965], cited
from bibliographic metadata only without inspecting the published text) to any linearly ordered
field `K` (including `ℚ` and `ℝ`); the `K`-generalization and the
`SimpleGraph.copositiveCliqueMatrix` packaging below are original formulations of this library:

* **Upper bound** (`SimpleGraph.quadraticForm_adjMatrix_le_stdSimplex`): by strong induction on
  the support size of `x : Convexity.StdSimplex K V`. Whenever two distinct vertices `u, v` in the
  support of `x` are nonadjacent, shifting weight along `e_u - e_v` changes
  `x ⬝ᵥ G.adjMatrix K *ᵥ x` linearly; moving all weight of `v` onto `u` or vice versa strictly
  shrinks the support without decreasing the quadratic form. Once the support is a clique `S`,
  Cauchy–Schwarz gives
  `x ⬝ᵥ G.adjMatrix K *ᵥ x = 1 - ∑ v ∈ S, x v ^ 2 ≤ 1 - 1 / #S ≤ 1 - 1 / ω(G)`.
* **Attainment** (`SimpleGraph.exists_stdSimplex_quadraticForm_adjMatrix_eq_of_isNClique`): the
  uniform distribution on a maximum clique achieves `1 - 1 / ω(G)`.

We also record the integer matrix `SimpleGraph.copositiveCliqueMatrix G k` with entries `-1` on
edges and `k - 2` on non-edges and the diagonal, which is non-copositive iff `k ≤ G.cliqueNum`
(`SimpleGraph.exists_nonneg_dotProduct_copositiveCliqueMatrix_lt_zero_iff`) for `k ≥ 2` on a
nonempty finite graph.

## Main definitions

* `SimpleGraph.copositiveCliqueMatrix`: the integer symmetric matrix `(k - 2) J - (k - 1) A_G`.

## Main results

* `SimpleGraph.quadraticForm_adjMatrix_le_stdSimplex`: Motzkin–Straus upper bound over any
  linearly ordered field.
* `SimpleGraph.isGreatest_quadraticForm_adjMatrix`: Motzkin–Straus identity
  `max_{x : StdSimplex K V} xᵀ A_G x = 1 - 1 / ω(G)` over any linearly ordered field.
* `SimpleGraph.sSup_quadraticForm_adjMatrix`: the real `sSup` form.
* `SimpleGraph.exists_nonneg_dotProduct_copositiveCliqueMatrix_lt_zero_iff`: non-copositivity of
  `copositiveCliqueMatrix G k` characterizes `k ≤ G.cliqueNum` for `2 ≤ k`.

## References

* [T. S. Motzkin, E. G. Straus, *Maxima for graphs and a new proof of a theorem of Turán*,
  Canadian Journal of Mathematics 17 (1965), 533–540][MotzkinStraus1965] (bibliographic metadata
  only; the published article text is uninspected, and no internal theorem numbers are claimed).
-/

public section

open Finset Matrix

namespace SimpleGraph

section MotzkinStraus

variable {V K : Type*}

/-- Expanding `x ⬝ᵥ G.adjMatrix K *ᵥ x` as a double sum over adjacent pairs. -/
private theorem dotProduct_adjMatrix_eq_sum [Fintype V] [CommSemiring K]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → K) :
    x ⬝ᵥ G.adjMatrix K *ᵥ x = ∑ u : V, ∑ v : V, if G.Adj u v then x u * x v else 0 := by
  simp only [dotProduct, mulVec, adjMatrix_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> ring

/-- On a clique, the adjacency quadratic form of a vector supported inside it is
`(∑ x_v)^2 - ∑ x_v^2`. -/
private theorem dotProduct_adjMatrix_eq_of_isClique [Fintype V] [CommRing K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} (hS : G.IsClique (S : Set V)) {x : V → K} (hx : ∀ v, v ∉ S → x v = 0) :
    x ⬝ᵥ G.adjMatrix K *ᵥ x = (∑ v ∈ S, x v) ^ 2 - ∑ v ∈ S, x v ^ 2 := by
  classical
  -- On the support, adjacency is exactly `u ≠ v`.
  have key (u v : V) :
      (if G.Adj u v then x u * x v else 0) = x u * x v - if u = v then x u * x v else 0 := by
    by_cases hmem : u ∈ S ∧ v ∈ S
    · by_cases huv : u = v <;> simp [huv, @hS u hmem.1 v hmem.2]
    · rcases not_and_or.mp hmem with h | h <;> simp [hx _ h]
  rw [dotProduct_adjMatrix_eq_sum, Finset.sum_subset (Finset.subset_univ S) fun v _ hv => hx v hv,
    Finset.sum_subset (f := fun v => x v ^ 2) (Finset.subset_univ S) fun v _ hv => by
      simp [hx v hv]]
  simp only [key, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    ← Finset.mul_sum, ← Finset.sum_mul, sq]

/-- Linear variation along `Pi.single u 1 - Pi.single v 1` when `u ≠ v` are nonadjacent. -/
private theorem dotProduct_adjMatrix_add_smul [Fintype V] [DecidableEq V] [CommRing K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (hadj : ¬G.Adj u v) (x : V → K) (t : K) :
    let d : V → K := Pi.single u 1 - Pi.single v 1
    (x + t • d) ⬝ᵥ G.adjMatrix K *ᵥ (x + t • d) =
      x ⬝ᵥ G.adjMatrix K *ᵥ x + 2 * t * ((G.adjMatrix K *ᵥ x) u - (G.adjMatrix K *ᵥ x) v) := by
  intro d
  set A := G.adjMatrix K
  have hd (y : V → K) : d ⬝ᵥ y = y u - y v := by
    simp only [d, Pi.sub_apply, dotProduct, Pi.single_apply, sub_mul, Finset.sum_sub_distrib,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hdAd : d ⬝ᵥ (A *ᵥ d) = 0 := by
    have hrow (w : V) : (A *ᵥ d) w = A w u - A w v := by
      simp only [d, mulVec, dotProduct, Pi.sub_apply, Pi.single_apply, mul_sub,
        Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
    rw [hd, hrow u, hrow v]
    simp only [A, adjMatrix_apply, G.loopless.irrefl, hadj, adj_comm (G := G) v u, ↓reduceIte,
      sub_self]
  rw [Matrix.dotProduct_add_smul_symm G.transpose_adjMatrix x d t, hd, hdAd, mul_zero, add_zero]

private theorem quadraticForm_adjMatrix_le_aux [Fintype V]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x : V → K} (hx0 : ∀ v, 0 ≤ x v) (hx1 : ∑ v, x v = 1) :
    x ⬝ᵥ G.adjMatrix K *ᵥ x ≤ 1 - 1 / (G.cliqueNum : K) := by
  classical
  set S : Finset V := {v | x v ≠ 0}
  have hxout : ∀ v, v ∉ S → x v = 0 := fun v hv => by
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hv
  have hsum : ∑ v ∈ S, x v = 1 :=
    (Finset.sum_subset (Finset.subset_univ S) fun v _ hv => hxout v hv).trans hx1
  have hSne : S.Nonempty := Finset.nonempty_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
  by_cases hclique : G.IsClique (S : Set V)
  · -- On a clique support the form is `1 - ∑ x_v ^ 2`, and Cauchy–Schwarz bounds `∑ x_v ^ 2`.
    have hcs : (1 : K) ≤ (S.card : K) * ∑ v ∈ S, x v ^ 2 := by
      simpa only [hsum, one_pow] using (sq_sum_le_card_mul_sum_sq (s := S) (f := x))
    have hScardK : (0 : K) < S.card := by exact_mod_cast Finset.card_pos.2 hSne
    have homegaK : (S.card : K) ≤ G.cliqueNum := by exact_mod_cast hclique.card_le_cliqueNum
    rw [dotProduct_adjMatrix_eq_of_isClique G hclique hxout, hsum, one_pow]
    linarith [one_div_le_one_div_of_le hScardK homegaK, (div_le_iff₀' hScardK).2 hcs]
  · simp only [SimpleGraph.IsClique, Set.Pairwise, Finset.mem_coe, not_forall] at hclique
    obtain ⟨u, huS, v, hvS, huv, hadj⟩ := hclique
    have hxu_pos : 0 < x u := lt_of_le_of_ne (hx0 u) (Ne.symm (by simpa [S] using huS))
    have hxv_pos : 0 < x v := lt_of_le_of_ne (hx0 v) (Ne.symm (by simpa [S] using hvS))
    let d : V → K := Pi.single u 1 - Pi.single v 1
    have hstep (t : K) (ht1 : 0 ≤ x u + t) (ht2 : 0 ≤ x v - t) :
        (∀ w, 0 ≤ (x + t • d) w) ∧ ∑ w, (x + t • d) w = 1 := by
      refine ⟨fun w => ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, d, Pi.sub_apply, Pi.single_apply]
        split_ifs with hwu hwv hwv
        · exact absurd (hwu.symm.trans hwv) huv
        · subst hwu; linarith
        · subst hwv; linarith
        · linarith [hx0 w]
      · simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, d, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, ← Finset.mul_sum, hx1]
    have hlt_supp (t : K) (hzero : (x + t • d) u = 0 ∨ (x + t • d) v = 0) :
        #{w | (x + t • d) w ≠ 0} < #S := by
      refine Finset.card_lt_card ⟨fun w hw => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        by_contra hxw
        have hxw := hxout w hxw
        have hwu : w ≠ u := by rintro rfl; exact hxu_pos.ne' hxw
        have hwv : w ≠ v := by rintro rfl; exact hxv_pos.ne' hxw
        exact hw (by simp [d, hxw, hwu, hwv])
      · rcases hzero with h | h
        exacts [(Finset.mem_filter.mp (hsub huS)).2 h, (Finset.mem_filter.mp (hsub hvS)).2 h]
    rcases le_total ((G.adjMatrix K *ᵥ x) v) ((G.adjMatrix K *ᵥ x) u) with hle | hle
    · have ht := hstep (x v) (by linarith) (by linarith)
      have hlt := hlt_supp (x v) (Or.inr (by simp [d, Ne.symm huv]))
      have hih := quadraticForm_adjMatrix_le_aux G ht.1 ht.2
      have hlin : _ = _ := dotProduct_adjMatrix_add_smul G hadj x (x v)
      linarith [mul_nonneg hxv_pos.le (sub_nonneg.2 hle)]
    · have ht := hstep (-x u) (by linarith) (by linarith)
      have hlt := hlt_supp (-x u) (Or.inl (by simp [d, huv]))
      have hih := quadraticForm_adjMatrix_le_aux G ht.1 ht.2
      have hlin : _ = _ := dotProduct_adjMatrix_add_smul G hadj x (-x u)
      linarith [mul_nonneg hxu_pos.le (sub_nonneg.2 hle)]
termination_by #{v | x v ≠ 0}
decreasing_by all_goals assumption

/-- **Motzkin–Straus upper bound**: on `Convexity.StdSimplex K V`, `x ⬝ᵥ G.adjMatrix K *ᵥ x`
is at most `1 - 1 / G.cliqueNum` (library generalization over arbitrary linearly ordered fields `K`;
[MotzkinStraus1965] was not inspected directly). -/
theorem quadraticForm_adjMatrix_le_stdSimplex [Fintype V]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : Convexity.StdSimplex K V) :
    (x.weights : V → K) ⬝ᵥ G.adjMatrix K *ᵥ (x.weights : V → K) ≤ 1 - 1 / (G.cliqueNum : K) :=
  quadraticForm_adjMatrix_le_aux G x.weights_nonneg x.total_of_fintype

/-- The uniform weight vector on a `k`-clique (`1 ≤ k`) gives a point of
`Convexity.StdSimplex K V` achieving `1 - 1 / k`. -/
theorem exists_stdSimplex_quadraticForm_adjMatrix_eq_of_isNClique [Fintype V]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (G : SimpleGraph V) [DecidableRel G.Adj] {S : Finset V} {k : ℕ} (hk : 1 ≤ k)
    (hS : G.IsNClique k S) :
    ∃ x : Convexity.StdSimplex K V,
      (x.weights : V → K) ⬝ᵥ G.adjMatrix K *ᵥ (x.weights : V → K) = 1 - 1 / (k : K) := by
  classical
  let xVec : V → K := fun v => if v ∈ S then 1 / (k : K) else 0
  have hk_ne : (k : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hx0 : ∀ v, 0 ≤ xVec v := fun v => by dsimp only [xVec]; split_ifs <;> positivity
  have hxout : ∀ v, v ∉ S → xVec v = 0 := fun v hv => by simp [xVec, hv]
  have hval : ∀ v ∈ S, xVec v = 1 / (k : K) := fun v hv => by simp [xVec, hv]
  have hs1 : ∑ v ∈ S, xVec v = 1 := by
    rw [Finset.sum_congr rfl hval, Finset.sum_const, hS.card_eq, nsmul_eq_mul,
      mul_one_div_cancel hk_ne]
  have hx1 : ∑ v : V, xVec v = 1 := by
    rw [← Finset.sum_subset (Finset.subset_univ S) fun v _ hv => hxout v hv, hs1]
  refine ⟨⟨Finsupp.equivFunOnFinite.symm xVec, fun v => by simpa using hx0 v,
      by simpa [Finsupp.sum_fintype] using hx1⟩, ?_⟩
  rw [Finsupp.coe_equivFunOnFinite_symm, dotProduct_adjMatrix_eq_of_isClique G hS.isClique hxout,
    hs1, one_pow, Finset.sum_congr rfl fun v hv => congrArg (· ^ 2) (hval v hv),
    Finset.sum_const, hS.card_eq, nsmul_eq_mul, sq, ← mul_assoc, mul_one_div_cancel hk_ne,
    one_mul]

/-- **The Motzkin–Straus theorem** (library generalization to arbitrary linearly ordered fields `K`;
[MotzkinStraus1965] is cited at paper level without inspecting the published text): on a nonempty
finite graph, the maximum of `x ⬝ᵥ G.adjMatrix K *ᵥ x` over `Convexity.StdSimplex K V` equals
`1 - 1 / G.cliqueNum`. Note that [MotzkinStraus1965] maximizes
`∑_{ij ∈ E} x_i x_j = (1 / 2) * (x ⬝ᵥ G.adjMatrix K *ᵥ x)`, giving `(1 / 2) * (1 - 1 / ω(G))`
(differing by a factor of `2`). -/
theorem isGreatest_quadraticForm_adjMatrix [Fintype V]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (G : SimpleGraph V) [Nonempty V] [DecidableRel G.Adj] :
    IsGreatest
      (Set.range fun x : Convexity.StdSimplex K V =>
        (x.weights : V → K) ⬝ᵥ G.adjMatrix K *ᵥ (x.weights : V → K))
      (1 - 1 / (G.cliqueNum : K)) := by
  refine ⟨?_, fun _ ⟨x, hx⟩ => hx ▸ quadraticForm_adjMatrix_le_stdSimplex G x⟩
  obtain ⟨S, hS⟩ := G.exists_isNClique_cliqueNum
  exact exists_stdSimplex_quadraticForm_adjMatrix_eq_of_isNClique G
    (Nat.one_le_iff_ne_zero.2 G.cliqueNum_ne_zero_of_finite) hS

/-- **The Motzkin–Straus theorem** over `ℝ` in `sSup` form (attributed to [MotzkinStraus1965];
the published text is uninspected, and [MotzkinStraus1965] includes a factor of `1 / 2` from
summing over unordered edges). -/
theorem sSup_quadraticForm_adjMatrix [Fintype V]
    (G : SimpleGraph V) [Nonempty V] [DecidableRel G.Adj] :
    sSup
        (Set.range fun x : Convexity.StdSimplex ℝ V =>
          (x.weights : V → ℝ) ⬝ᵥ G.adjMatrix ℝ *ᵥ (x.weights : V → ℝ)) =
      1 - 1 / (G.cliqueNum : ℝ) :=
  (isGreatest_quadraticForm_adjMatrix G).csSup_eq

/-! ### Copositive matrix characterization of the clique number -/

/-- The symmetric integer matrix `(k - 2) J - (k - 1) A_G` (library packaging for the clique
reduction): entries are `-1` on edges of `G` and `k - 2` on non-edges and the diagonal. For
`k ≥ 2` on a nonempty finite graph, this matrix fails to be copositive iff `G` has a `k`-clique. -/
@[expose] def copositiveCliqueMatrix (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    Matrix V V ℤ :=
  of fun u v => if G.Adj u v then (-1 : ℤ) else (k : ℤ) - 2

@[simp]
theorem copositiveCliqueMatrix_apply (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (u v : V) :
    G.copositiveCliqueMatrix k u v = if G.Adj u v then (-1 : ℤ) else (k : ℤ) - 2 :=
  rfl

theorem isSymm_copositiveCliqueMatrix (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    (G.copositiveCliqueMatrix k).IsSymm := by
  ext u v
  simp only [transpose_apply, copositiveCliqueMatrix_apply, adj_comm]

/-- On any vector, `x ⬝ᵥ M *ᵥ x = (k - 2) * (∑ x_v)^2 - (k - 1) * (x ⬝ᵥ A_G *ᵥ x)`. -/
theorem dotProduct_copositiveCliqueMatrix [Fintype V] [CommRing K]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (x : V → K) :
    x ⬝ᵥ ((G.copositiveCliqueMatrix k).map (Int.cast : ℤ → K) *ᵥ x) =
      ((k : K) - 2) * (∑ v, x v) ^ 2 - ((k : K) - 1) * (x ⬝ᵥ G.adjMatrix K *ᵥ x) := by
  rw [dotProduct_adjMatrix_eq_sum]
  simp only [dotProduct, mulVec, map_apply, copositiveCliqueMatrix_apply, sq, Finset.sum_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> push_cast <;> ring

/-- For `k ≥ 2` on a nonempty finite graph, `copositiveCliqueMatrix G k` is non-copositive iff
`G` has a clique of size `k`. -/
theorem exists_nonneg_dotProduct_copositiveCliqueMatrix_lt_zero_iff [Fintype V]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (G : SimpleGraph V) [Nonempty V] [DecidableRel G.Adj] {k : ℕ} (hk : 2 ≤ k) :
    (∃ x : V → K, (∀ v, 0 ≤ x v) ∧
        x ⬝ᵥ ((G.copositiveCliqueMatrix k).map (Int.cast : ℤ → K) *ᵥ x) < 0) ↔
      k ≤ G.cliqueNum := by
  have hωK : (0 : K) < G.cliqueNum := mod_cast Nat.pos_of_ne_zero G.cliqueNum_ne_zero_of_finite
  constructor
  · intro h
    obtain ⟨y, hylt⟩ := (Matrix.exists_nonneg_dotProduct_lt_zero_iff_stdSimplex _).1 h
    rw [dotProduct_copositiveCliqueMatrix, y.total_of_fintype, one_pow, mul_one] at hylt
    have hms := quadraticForm_adjMatrix_le_stdSimplex G y
    -- If `ω < k`, then `(k - 1) * (1 - 1 / ω) ≤ k - 2`, contradicting `hylt`.
    by_contra hlt
    have hωk : (G.cliqueNum : K) + 1 ≤ k := mod_cast Nat.not_le.mp hlt
    have hk1 : (1 : K) ≤ k := mod_cast le_trans (by decide : 1 ≤ 2) hk
    have h1 : 1 ≤ ((k : K) - 1) / G.cliqueNum := (le_div_iff₀ hωK).2 (by linarith)
    linarith [mul_one_div ((k : K) - 1) (G.cliqueNum : K),
      mul_le_mul_of_nonneg_left hms (sub_nonneg.2 hk1)]
  · intro hle
    obtain ⟨y, hy⟩ := (isGreatest_quadraticForm_adjMatrix (K := K) G).1
    dsimp only at hy
    refine (Matrix.exists_nonneg_dotProduct_lt_zero_iff_stdSimplex _).2 ⟨y, ?_⟩
    rw [dotProduct_copositiveCliqueMatrix, y.total_of_fintype, one_pow, mul_one, hy]
    have hleK : (k : K) ≤ G.cliqueNum := mod_cast hle
    have hlt1 : ((k : K) - 1) / G.cliqueNum < 1 := (div_lt_one hωK).2 (by linarith)
    linarith [mul_one_div ((k : K) - 1) (G.cliqueNum : K)]

end MotzkinStraus

end SimpleGraph
