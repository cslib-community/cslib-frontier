/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Evolutionary.Basic
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Clique
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MotzkinStraus
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The clique–ESS reduction game (Etessami–Lochbihler / Nisan)

This module formalizes the symmetric two-player payoff matrix `cliqueESSGame G k` attached to a
finite simple graph `G` on vertex type `V` and parameter `k : ℕ`, following Suri [Suri2007],
Section 29.2 (pp. 720–723; attributed there to Nisan 2006 extending Etessami–Lochbihler 2004).

The pure strategy set is `Option V`, where `none` plays the role of pure strategy `0` and
`some v` represents vertex `v ∈ V`:

* `payoff (some u) (some v) = 1` if `G.Adj u v`, `0` otherwise for `u ≠ v`;
* `payoff (some u) (some u) = 1 / 2`;
* `payoff none _ = payoff _ none = 1 - 1 / (2 * k)`.

The `1 / 2` diagonal modifies the classical Motzkin–Straus adjacency quadratic form by
`+ (1 / 2) * ∑ v, x v ^ 2`, which strictly increases whenever probability mass is shifted across
a non-edge. This gives the exact upper bound and equality characterization (**Lemma 29.3**):
for every mixed strategy `s` supported on `V` (`s none = 0`),
`F(s | s) ≤ 1 - 1 / (2 * ω(G))`, with equality if and only if `s` is the uniform distribution on
a maximum clique of `G`.

For `k ≥ 1`, combining Lemmas 29.4–29.7 gives the two-sided characterizations used for hardness in
`CslibFrontier.GameTheory.Evolutionary.Complexity`:

* Pure strategy `0` (`none`) is an ESS if and only if `G.cliqueNum < k` (**Lemmas 29.5–29.6**).
* `cliqueESSGame G k` possesses an ESS if and only if `G.cliqueNum ≠ k` (**Lemmas 29.4–29.7**).

## Main definitions

* `Cslib.GameTheory.cliqueESSGame`: the doubly symmetric two-player payoff matrix on `Option V`
  built from a simple graph `G` and parameter `k : ℕ`.
* `Cslib.GameTheory.cliqueUniform`: the uniform mixed strategy supported on a `Finset V`.
* `Cslib.GameTheory.zeroPureStrategy`: the pure strategy placing weight `1` on `none` (strategy `0`).

## Main results

* `Cslib.GameTheory.fitness_cliqueESSGame_le`: **Lemma 29.3** upper bound ([Suri2007], p. 721):
  if `s none = 0`, then `F(s | s) ≤ 1 - 1 / (2 * G.cliqueNum)`.
* `Cslib.GameTheory.fitness_cliqueESSGame_eq_iff`: **Lemma 29.3** equality characterization:
  `F(s | s) = 1 - 1 / (2 * G.cliqueNum)` iff `s = cliqueUniform C` for a maximum clique `C`.
* `Cslib.GameTheory.isESS_cliqueUniform_of_maximal`: **Lemma 29.4** ([Suri2007], p. 722): the
  uniform distribution on any maximal clique of size `> k` is an ESS.
* `Cslib.GameTheory.isESS_zeroPureStrategy_of_cliqueNum_lt`: **Lemma 29.5** ([Suri2007], p. 722):
  if `G.cliqueNum < k`, then pure strategy `0` is an ESS.
* `Cslib.GameTheory.not_isESS_zeroPureStrategy_of_le_cliqueNum`: **Lemma 29.6** ([Suri2007],
  p. 722): if `k ≤ G.cliqueNum`, then pure strategy `0` is not an ESS.
* `Cslib.GameTheory.not_isESS_of_cliqueNum_le`: **Lemma 29.7 / Exercise 29.5** ([Suri2007],
  pp. 722–723, 735): if `G.cliqueNum ≤ k`, then no strategy other than pure strategy `0` is an ESS.
* `Cslib.GameTheory.isESS_zeroPureStrategy_iff`: `e₀` is an ESS of `cliqueESSGame G k` iff
  `G.cliqueNum < k` (for `0 < k`).
* `Cslib.GameTheory.hasESS_cliqueESSGame_iff`: `cliqueESSGame G k` has an ESS iff
  `G.cliqueNum ≠ k` (for `0 < k`).

## References

* [S. Suri, *Computational Evolutionary Game Theory*, Ch. 29 of *Algorithmic Game Theory*,
  pp. 717–736][Suri2007]
* [T. S. Motzkin, E. G. Straus, *Maxima for graphs and a new proof of a theorem of Turán*,
  Can. J. Math. 17 (1965), 533–540][MotzkinStraus1965] (bibliographic reference as cited in
  [Suri2007]).
-/

public section

open Finset Matrix

namespace Cslib.GameTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Entry `(a, b)` of the Etessami–Lochbihler / Nisan symmetric payoff matrix ([Suri2007],
Section 29.2, p. 721) on `Option V`. -/
@[expose] def cliqueESSPayoff (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    Matrix (Option V) (Option V) ℝ :=
  Matrix.of fun a b =>
    match a, b with
    | none, _ => 1 - 1 / (2 * (k : ℝ))
    | _, none => 1 - 1 / (2 * (k : ℝ))
    | some u, some v =>
      if u = v then (1 : ℝ) / 2
      else if G.Adj u v then 1
      else 0

/-- The doubly symmetric two-player game attached to `G` and parameter `k : ℕ`
([Suri2007], Section 29.2, p. 721). -/
@[expose] def cliqueESSGame (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    SymmetricGame (Option V) :=
  ⟨cliqueESSPayoff G k⟩

/-- Pure strategy `0` (index `none : Option V`). -/
@[expose] noncomputable def zeroPureStrategy (V : Type*) : Option V → ℝ :=
  Pi.single (none : Option V) (1 : ℝ)

/-- The uniform distribution supported on a finite vertex set `C : Finset V`, putting weight `0` on
strategy `none` and `1 / C.card` on each `some v` with `v ∈ C`. -/
@[expose] noncomputable def cliqueUniform (C : Finset V) : Option V → ℝ
  | none => 0
  | some v => if v ∈ C then 1 / (C.card : ℝ) else 0

theorem cliqueESSPayoff_isSymm (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    (cliqueESSPayoff G k).IsSymm := by
  ext a b
  simp only [Matrix.transpose_apply, cliqueESSPayoff, Matrix.of_apply]
  cases a with
  | none =>
    cases b <;> rfl
  | some u =>
    cases b with
    | none => rfl
    | some v =>
      by_cases huv : u = v
      · subst huv; simp
      · have hvu : v ≠ u := huv.symm
        simp only [huv, hvu, ↓reduceIte, G.adj_comm v u]

theorem isMixedStrategy_zeroPureStrategy : IsMixedStrategy (zeroPureStrategy V) :=
  isMixedStrategy_single (none : Option V)

theorem isMixedStrategy_cliqueUniform {C : Finset V} (hC : C.Nonempty) :
    IsMixedStrategy (cliqueUniform C) := by
  have hcard_pos : (0 : ℝ) < C.card := Nat.cast_pos.2 (Finset.card_pos.2 hC)
  refine ⟨fun o => ?_, ?_⟩
  · cases o with
    | none => simp [cliqueUniform]
    | some v =>
      dsimp only [cliqueUniform]
      split_ifs
      · positivity
      · exact le_rfl
  · rw [Fintype.sum_option]
    have hsum : ∑ v : V, cliqueUniform C (some v) = 1 := by
      simp only [cliqueUniform, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
        nsmul_eq_mul]
      exact mul_one_div_cancel hcard_pos.ne'
    simp only [cliqueUniform, zero_add, hsum]

theorem cliqueUniform_ne_zeroPureStrategy (C : Finset V) :
    cliqueUniform C ≠ zeroPureStrategy V := by
  intro h
  have := congrFun h none
  simp only [cliqueUniform, zeroPureStrategy, Pi.single_eq_same] at this
  exact zero_ne_one this

/-! ### Row/column identities for pure strategy `none` -/

theorem cliqueESSGame_mulVec_none (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    {t : Option V → ℝ} (ht : ∑ o, t o = 1) :
    ((cliqueESSGame G k).payoff *ᵥ t) none = 1 - 1 / (2 * (k : ℝ)) := by
  simp only [mulVec, dotProduct, cliqueESSGame, cliqueESSPayoff, Matrix.of_apply]
  have hterm : ∀ o : Option V,
      (match (none : Option V), o with
        | none, _ => 1 - 1 / (2 * (k : ℝ))
        | _, none => 1 - 1 / (2 * (k : ℝ))
        | some u, some v => if u = v then 1 / 2 else if G.Adj u v then 1 else 0) * t o =
      (1 - 1 / (2 * (k : ℝ))) * t o := fun o => by cases o <;> rfl
  simp_rw [hterm, ← Finset.mul_sum, ht, mul_one]

theorem fitness_zeroPureStrategy_left (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    {t : Option V → ℝ} (ht : ∑ o, t o = 1) :
    (cliqueESSGame G k).fitness (zeroPureStrategy V) t = 1 - 1 / (2 * (k : ℝ)) := by
  rw [zeroPureStrategy, SymmetricGame.fitness_single_left]
  exact cliqueESSGame_mulVec_none G k ht

theorem fitness_zeroPureStrategy_right (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    {s : Option V → ℝ} (hs : ∑ o, s o = 1) :
    (cliqueESSGame G k).fitness s (zeroPureStrategy V) = 1 - 1 / (2 * (k : ℝ)) := by
  rw [SymmetricGame.fitness_symm _ (cliqueESSPayoff_isSymm G k)]
  exact fitness_zeroPureStrategy_left G k hs

/-- Quadratic form expansion of `cliqueESSGame G k` on a vector supported on `V`. -/
private def vertexQuad (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) : ℝ :=
  (x ⬝ᵥ G.adjMatrix ℝ *ᵥ x) + (1 / 2) * ∑ v : V, x v ^ 2

private theorem fitness_cliqueESSGame_of_none_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) {s : Option V → ℝ} (hs0 : s none = 0) :
    (cliqueESSGame G k).fitness s s = vertexQuad G (fun v => s (some v)) := by
  let x : V → ℝ := fun v => s (some v)
  have h1 : (cliqueESSGame G k).fitness s s =
      ∑ u : V, ∑ v : V,
        x u * (if u = v then (1 : ℝ) / 2 else if G.Adj u v then 1 else 0) * x v := by
    rw [SymmetricGame.fitness_eq_sum, Fintype.sum_option]
    have hnone : ∑ j : Option V, s none * (cliqueESSGame G k).payoff none j * s j = 0 := by
      simp [hs0]
    rw [hnone, zero_add]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Fintype.sum_option]
    simp only [hs0, mul_zero, zero_add, x, cliqueESSGame, cliqueESSPayoff, Matrix.of_apply]
  have h2 : ∑ u : V, ∑ v : V,
      x u * (if u = v then (1 : ℝ) / 2 else if G.Adj u v then 1 else 0) * x v =
      (∑ u : V, ∑ v : V, if G.Adj u v then x u * x v else 0) +
        (1 / 2) * ∑ u : V, x u ^ 2 := by
    have hsplit : ∀ u v : V,
        x u * (if u = v then (1 : ℝ) / 2 else if G.Adj u v then 1 else 0) * x v =
        (if G.Adj u v then x u * x v else 0) +
          (if u = v then (1 / 2) * (x u * x v) else 0) := by
      intro u v
      by_cases huv : u = v
      · subst huv
        simp only [G.loopless.irrefl u, ↓reduceIte, zero_add]
        ring
      · by_cases hadj : G.Adj u v
        · simp only [huv, hadj, ↓reduceIte, add_zero]; ring
        · simp only [huv, hadj, ↓reduceIte, mul_zero, zero_mul, add_zero]
    simp_rw [hsplit, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, sq]
  have hadj : x ⬝ᵥ G.adjMatrix ℝ *ᵥ x =
      ∑ u : V, ∑ v : V, if G.Adj u v then x u * x v else 0 := by
    simp only [dotProduct, mulVec, SimpleGraph.adjMatrix_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> ring
  rw [h1, h2, vertexQuad, hadj]

/-- On a clique `C`, the vertex quadratic form `vertexQuad` is `1 - (1/2) * ∑_{v ∈ C} x_v^2`. -/
private theorem vertexQuad_eq_of_isClique (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Finset V} (hC : G.IsClique (C : Set V)) {x : V → ℝ}
    (hx : ∀ v, v ∉ C → x v = 0) (hx1 : ∑ v : V, x v = 1) :
    vertexQuad G x = 1 - (1 / 2) * ∑ v ∈ C, x v ^ 2 := by
  have hsumC : ∑ v ∈ C, x v = 1 := by
    rw [← hx1]
    exact Finset.sum_subset (Finset.subset_univ C) fun v _ hv => hx v hv
  have hsqC : ∑ v : V, x v ^ 2 = ∑ v ∈ C, x v ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ C) fun v _ hv => by rw [hx v hv, zero_pow two_ne_zero]).symm
  have hadj : x ⬝ᵥ G.adjMatrix ℝ *ᵥ x = (∑ v ∈ C, x v) ^ 2 - ∑ v ∈ C, x v ^ 2 := by
    have hdot : x ⬝ᵥ G.adjMatrix ℝ *ᵥ x =
        ∑ u : V, ∑ v : V, if G.Adj u v then x u * x v else 0 := by
      simp only [dotProduct, mulVec, SimpleGraph.adjMatrix_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      split_ifs <;> ring
    rw [hdot]
    have hzero : ∀ u, u ∉ C → ∑ v : V, (if G.Adj u v then x u * x v else 0) = 0 := fun u hu =>
      Finset.sum_eq_zero fun v _ => by split_ifs <;> simp only [hx u hu, zero_mul]
    rw [← Finset.sum_subset (Finset.subset_univ C) fun u _ hu => hzero u hu]
    have hinner : ∀ u ∈ C, ∑ v : V, (if G.Adj u v then x u * x v else 0) =
        (∑ v ∈ C, x u * x v) - x u ^ 2 := fun u hu => by
      have hsub : ∀ v, v ∉ C → (if G.Adj u v then x u * x v else 0) = 0 := fun v hv => by
        split_ifs <;> simp only [hx v hv, mul_zero]
      rw [← Finset.sum_subset (Finset.subset_univ C) fun v _ hv => hsub v hv]
      have heq : (∑ v ∈ C, if G.Adj u v then x u * x v else 0) + x u ^ 2 =
          ∑ v ∈ C, x u * x v := by
        have hdiag : x u ^ 2 = ∑ v ∈ C, if u = v then x u * x v else 0 := by
          rw [Finset.sum_ite_eq C u (fun v => x u * x v), if_pos hu, sq]
        rw [hdiag, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v hv => ?_
        by_cases huv : u = v
        · subst huv; simp [G.loopless.irrefl u]
        · simp [huv, hC hu hv huv]
      linarith
    rw [Finset.sum_congr rfl hinner, Finset.sum_sub_distrib]
    congr 1
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, sq]
  rw [vertexQuad, hadj, hsumC, one_pow, hsqC]
  ring

/-- Exact Cauchy–Schwarz identity on the simplex over a nonempty finite set `C`. -/
private theorem sum_sq_sub_one_div_card {C : Finset V} (hC : C.Nonempty) {x : V → ℝ}
    (hx1 : ∑ v ∈ C, x v = 1) :
    (∑ v ∈ C, x v ^ 2) - 1 / (C.card : ℝ) =
      ∑ v ∈ C, (x v - 1 / (C.card : ℝ)) ^ 2 := by
  have hcpos : (0 : ℝ) < C.card := Nat.cast_pos.2 (Finset.card_pos.2 hC)
  have hexp : ∀ v ∈ C, (x v - 1 / (C.card : ℝ)) ^ 2 =
      x v ^ 2 - (2 / (C.card : ℝ)) * x v + (1 / (C.card : ℝ)) ^ 2 := by
    intro v _; ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hx1, Finset.sum_const, nsmul_eq_mul]
  field_simp [hcpos.ne']
  ring

/-- Moving all weight from `v` to `u` across a non-edge `(u, v)` **strictly** changes `vertexQuad`
by `2 * x v * ((A_G *ᵥ x) u - (A_G *ᵥ x) v) + x u * x v`. -/
private theorem vertexQuad_shift_nonadj (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : u ≠ v) (hnot : ¬ G.Adj u v) (x : V → ℝ) :
    let x' : V → ℝ := fun w => if w = u then x u + x v else if w = v then 0 else x w
    vertexQuad G x' - vertexQuad G x =
      2 * x v * ((G.adjMatrix ℝ *ᵥ x) u - (G.adjMatrix ℝ *ᵥ x) v) + x u * x v := by
  intro x'
  let d : V → ℝ := Pi.single u 1 - Pi.single v 1
  have hx'eq : x' = x + x v • d := by
    ext w
    simp only [x', d, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.single_apply]
    by_cases hwu : w = u
    · subst hwu; simp [huv]
    · by_cases hwv : w = v
      · subst hwv; simp [huv.symm]
      · simp [hwu, hwv]
  have hdAx : d ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) =
      (G.adjMatrix ℝ *ᵥ x) u - (G.adjMatrix ℝ *ᵥ x) v := by
    simp only [d, sub_dotProduct, single_dotProduct, one_mul]
  have hdAd : d ⬝ᵥ (G.adjMatrix ℝ *ᵥ d) = 0 := by
    have hrow : ∀ w : V, (G.adjMatrix ℝ *ᵥ d) w =
        (G.adjMatrix ℝ w u - G.adjMatrix ℝ w v) := fun w => by
      simp only [d, mulVec_sub, mulVec_single, mul_one, Matrix.col_apply, Pi.sub_apply]
    simp only [d, sub_dotProduct, single_dotProduct, one_mul, hrow]
    have hvu : ¬ G.Adj v u := fun h => hnot h.symm
    simp [SimpleGraph.adjMatrix_apply, hnot, hvu, G.loopless.irrefl]
  have hadj_diff : x' ⬝ᵥ G.adjMatrix ℝ *ᵥ x' - x ⬝ᵥ G.adjMatrix ℝ *ᵥ x =
      2 * x v * ((G.adjMatrix ℝ *ᵥ x) u - (G.adjMatrix ℝ *ᵥ x) v) := by
    rw [hx'eq, Matrix.dotProduct_add_smul_symm G.transpose_adjMatrix x d (x v), hdAx, hdAd]
    ring
  have hsq_diff : ∑ w : V, x' w ^ 2 - ∑ w : V, x w ^ 2 = 2 * (x u * x v) := by
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ w : V, w ≠ u → w ≠ v → x' w ^ 2 - x w ^ 2 = 0 := by
      intro w hwu hwv
      simp [x', hwu, hwv]
    have hsplit : ∑ w : V, (x' w ^ 2 - x w ^ 2) =
        (x' u ^ 2 - x u ^ 2) + (x' v ^ 2 - x v ^ 2) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u),
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨huv.symm, Finset.mem_univ v⟩)]
      have hrest : ∑ w ∈ (Finset.univ.erase u).erase v, (x' w ^ 2 - x w ^ 2) = 0 :=
        Finset.sum_eq_zero fun w hw => by
          rw [Finset.mem_erase, Finset.mem_erase] at hw
          exact hterm w hw.2.1 hw.1
      rw [hrest, add_zero, add_assoc]
    rw [hsplit]
    simp only [x', ↓reduceIte, huv.symm]
    ring
  simp only [vertexQuad]
  linarith

/-- Strong-induction worker proving **both** the upper bound and strict inequality outside
maximal cliques for `vertexQuad`. -/
private theorem vertexQuad_le_aux (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ m (x : V → ℝ), #{v : V | x v ≠ 0} = m →
      (∀ v, 0 ≤ x v) → ∑ v : V, x v = 1 →
        vertexQuad G x ≤ 1 - 1 / (2 * (G.cliqueNum : ℝ)) ∧
          (vertexQuad G x = 1 - 1 / (2 * (G.cliqueNum : ℝ)) →
            G.IsClique ({v : V | x v ≠ 0} : Set V) ∧
              #{v : V | x v ≠ 0} = G.cliqueNum ∧
              ∀ v, x v ≠ 0 → x v = 1 / (G.cliqueNum : ℝ)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro x hm hx0 hx1
  set S : Finset V := Finset.univ.filter fun v => x v ≠ 0
  have hSne : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h0 : ∑ v : V, x v = 0 := Finset.sum_eq_zero fun v _ => by
      by_contra hne
      have : v ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ v, hne⟩
      rw [hemp] at this
      exact Finset.notMem_empty v this
    linarith
  have hxout : ∀ v, v ∉ S → x v = 0 := fun v hv => by
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hv
  have hsumS : ∑ v ∈ S, x v = 1 := by
    rw [← hx1]
    exact Finset.sum_subset (Finset.subset_univ S) fun v _ hv => hxout v hv
  by_cases hclique : G.IsClique (S : Set V)
  · have hq := vertexQuad_eq_of_isClique G hclique hxout hx1
    have hcs := sum_sq_sub_one_div_card hSne hsumS
    have hcard_pos : 0 < S.card := Finset.card_pos.2 hSne
    have hcard_le : S.card ≤ G.cliqueNum := hclique.card_le_cliqueNum
    have hSpos : (0 : ℝ) < S.card := Nat.cast_pos.2 hcard_pos
    have hSle : (S.card : ℝ) ≤ G.cliqueNum := Nat.cast_le.2 hcard_le
    have hdiv_le : 1 / (2 * (G.cliqueNum : ℝ)) ≤ 1 / (2 * (S.card : ℝ)) := by
      gcongr
    have hss_nonneg : 0 ≤ ∑ v ∈ S, (x v - 1 / (S.card : ℝ)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hle : vertexQuad G x ≤ 1 - 1 / (2 * (G.cliqueNum : ℝ)) := by
      rw [hq]
      linarith
    refine ⟨hle, fun heq => ?_⟩
    have hss_eq : ∑ v ∈ S, (x v - 1 / (S.card : ℝ)) ^ 2 = 0 := by linarith
    have hdiv_eq : 1 / (2 * (G.cliqueNum : ℝ)) = 1 / (2 * (S.card : ℝ)) := by linarith
    have hcard_eqR : (S.card : ℝ) = (G.cliqueNum : ℝ) := by
      have hGpos : (0 : ℝ) < G.cliqueNum := lt_of_lt_of_le hSpos hSle
      field_simp [hSpos.ne', hGpos.ne'] at hdiv_eq
      linarith
    have hcard_eq : S.card = G.cliqueNum := Nat.cast_injective hcard_eqR
    refine ⟨hclique, hcard_eq, fun v hv => ?_⟩
    have hvS : v ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ v, hv⟩
    have hsq0 : (x v - 1 / (S.card : ℝ)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun w _ => sq_nonneg (x w - 1 / (S.card : ℝ))).1 hss_eq
        v hvS
    have hxveq : x v = 1 / (S.card : ℝ) := sub_eq_zero.1 (sq_eq_zero_iff.1 hsq0)
    rw [hxveq, hcard_eq]
  · simp only [SimpleGraph.IsClique, Set.Pairwise, Finset.mem_coe, not_forall] at hclique
    obtain ⟨u, huS, v, hvS, huv, hnotadj⟩ := hclique
    have hxu : 0 < x u := lt_of_le_of_ne (hx0 u)
      (Ne.symm (by simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using huS))
    have hxv : 0 < x v := lt_of_le_of_ne (hx0 v)
      (Ne.symm (by simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hvS))
    have hshift : ∀ a b : V, a ≠ b → ¬ G.Adj a b → 0 < x a → 0 < x b →
        (G.adjMatrix ℝ *ᵥ x) b ≤ (G.adjMatrix ℝ *ᵥ x) a →
        vertexQuad G x < 1 - 1 / (2 * (G.cliqueNum : ℝ)) := by
      intro a b hab hnab hxa hxb hle
      let x' : V → ℝ := fun w => if w = a then x a + x b else if w = b then 0 else x w
      have hx'0 : ∀ w, 0 ≤ x' w := fun w => by
        dsimp only [x']; split_ifs <;> linarith [hx0 w]
      have hx'1 : ∑ w : V, x' w = 1 := by
        have hdiff : ∑ w : V, (x' w - x w) = 0 := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
            ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩)]
          have hrest : ∑ w ∈ (Finset.univ.erase a).erase b, (x' w - x w) = 0 :=
            Finset.sum_eq_zero fun w hw => by
              rw [Finset.mem_erase, Finset.mem_erase] at hw
              simp [x', hw.1, hw.2.1]
          simp [x', hab.symm, hrest]
        rw [Finset.sum_sub_distrib] at hdiff
        linarith
      have hsub : Finset.univ.filter (fun w => x' w ≠ 0) ⊂ S := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨fun w hw => ?_, fun heq => ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hw ⊢
          by_contra hxw
          have hwa : w ≠ a := fun h => by subst h; exact hxa.ne' hxw
          have hwb : w ≠ b := fun h => by subst h; exact hxb.ne' hxw
          apply hw
          simp [x', hwa, hwb, hxw]
        · have hbmem : b ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ b, hxb.ne'⟩
          rw [← heq, Finset.mem_filter] at hbmem
          exact hbmem.2 (by simp [x', hab.symm])
      have hcard_lt : (Finset.univ.filter fun w => x' w ≠ 0).card < m := by
        rw [← hm]; exact Finset.card_lt_card hsub
      have hih := (ih _ hcard_lt x' rfl hx'0 hx'1).1
      have hgain := vertexQuad_shift_nonadj G hab hnab x
      dsimp only at hgain
      have hterm1 : 0 ≤ 2 * x b * ((G.adjMatrix ℝ *ᵥ x) a - (G.adjMatrix ℝ *ᵥ x) b) :=
        mul_nonneg (mul_nonneg (by norm_num) hxb.le) (sub_nonneg.2 hle)
      have hterm2 : 0 < x a * x b := mul_pos hxa hxb
      linarith
    have hlt : vertexQuad G x < 1 - 1 / (2 * (G.cliqueNum : ℝ)) := by
      rcases le_total ((G.adjMatrix ℝ *ᵥ x) v) ((G.adjMatrix ℝ *ᵥ x) u) with hle | hle
      · exact hshift u v huv hnotadj hxu hxv hle
      · exact hshift v u huv.symm (fun h => hnotadj h.symm) hxv hxu hle
    exact ⟨hlt.le, fun heq => absurd heq hlt.ne⟩

/-- The fitness of the uniform strategy on a clique `C` against itself is `1 - 1 / (2 * #C)`. -/
theorem fitness_cliqueUniform_self (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    {C : Finset V} (hCne : C.Nonempty) (hC : G.IsClique (C : Set V)) :
    (cliqueESSGame G k).fitness (cliqueUniform C) (cliqueUniform C) =
      1 - 1 / (2 * (C.card : ℝ)) := by
  have hmix := isMixedStrategy_cliqueUniform hCne
  have hsumV : ∑ v : V, cliqueUniform C (some v) = 1 := by
    have := hmix.sum_eq_one
    rw [Fintype.sum_option] at this
    simpa only [cliqueUniform, zero_add] using this
  have hcard_pos : (0 : ℝ) < C.card := Nat.cast_pos.2 (Finset.card_pos.2 hCne)
  rw [fitness_cliqueESSGame_of_none_eq_zero G k rfl,
    vertexQuad_eq_of_isClique G hC (fun v hv => by simp [cliqueUniform, hv]) hsumV]
  have hsq : ∑ v ∈ C, (cliqueUniform C (some v)) ^ 2 = 1 / (C.card : ℝ) := by
    have heq : ∑ v ∈ C, (cliqueUniform C (some v)) ^ 2 =
        ∑ _v ∈ C, (1 / (C.card : ℝ)) ^ 2 :=
      Finset.sum_congr rfl fun v hv => by simp [cliqueUniform, hv]
    rw [heq, Finset.sum_const, nsmul_eq_mul]
    field_simp [hcard_pos.ne']
  rw [hsq]
  ring

/-- **Lemma 29.3 (upper bound)** ([Suri2007], p. 721): if a mixed strategy `s` puts zero weight
on pure strategy `0` (`none`), then `F(s | s) ≤ 1 - 1 / (2 * G.cliqueNum)`. -/
theorem fitness_cliqueESSGame_le (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    {s : Option V → ℝ} (hs : IsMixedStrategy s) (hs0 : s none = 0) :
    (cliqueESSGame G k).fitness s s ≤ 1 - 1 / (2 * (G.cliqueNum : ℝ)) := by
  rw [fitness_cliqueESSGame_of_none_eq_zero G k hs0]
  have hsum : ∑ v : V, s (some v) = 1 := by
    have := hs.sum_eq_one
    rw [Fintype.sum_option, hs0, zero_add] at this
    exact this
  exact (vertexQuad_le_aux G _ (fun v => s (some v)) rfl (fun v => hs.nonneg (some v)) hsum).1

/-- **Lemma 29.3 (equality characterization)** ([Suri2007], p. 721): for a mixed strategy `s` with
`s none = 0`, `F(s | s) = 1 - 1 / (2 * G.cliqueNum)` if and only if `s` is the uniform
distribution on a maximum clique of `G`. -/
theorem fitness_cliqueESSGame_eq_iff (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    {s : Option V → ℝ} (hs : IsMixedStrategy s) (hs0 : s none = 0) :
    (cliqueESSGame G k).fitness s s = 1 - 1 / (2 * (G.cliqueNum : ℝ)) ↔
      ∃ C : Finset V, G.IsNClique G.cliqueNum C ∧ s = cliqueUniform C := by
  constructor
  · intro heq
    rw [fitness_cliqueESSGame_of_none_eq_zero G k hs0] at heq
    have hsum : ∑ v : V, s (some v) = 1 := by
      have := hs.sum_eq_one
      rw [Fintype.sum_option, hs0, zero_add] at this
      exact this
    obtain ⟨hclique, hcard, hval⟩ :=
      (vertexQuad_le_aux G _ (fun v => s (some v)) rfl (fun v => hs.nonneg (some v)) hsum).2 heq
    refine ⟨Finset.univ.filter fun v => s (some v) ≠ 0, ⟨hclique, hcard⟩, ?_⟩
    ext o
    cases o with
    | none => simpa only [cliqueUniform] using hs0
    | some v =>
      dsimp only [cliqueUniform]
      by_cases hv : s (some v) = 0
      · simp [hv]
      · have hmem : v ∈ Finset.univ.filter fun w => s (some w) ≠ 0 :=
          Finset.mem_filter.2 ⟨Finset.mem_univ v, hv⟩
        rw [if_pos hmem, hcard]
        exact hval v hv
  · rintro ⟨C, hC, rfl⟩
    have hsum : ∑ v : V, cliqueUniform C (some v) = 1 := by
      have := hs.sum_eq_one
      rw [Fintype.sum_option] at this
      simpa only [cliqueUniform, zero_add] using this
    have hCne : C.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      subst hemp
      simp [cliqueUniform] at hsum
    rw [fitness_cliqueUniform_self G k hCne hC.isClique, hC.card_eq]

/-- A strategy putting weight `0` on `none` forces `V` to be nonempty and `1 ≤ G.cliqueNum`. -/
private theorem cliqueNum_pos_of_isMixedStrategy_none_zero (G : SimpleGraph V)
    {s : Option V → ℝ} (hs : IsMixedStrategy s) (hs0 : s none = 0) :
    0 < G.cliqueNum := by
  obtain ⟨o, ho⟩ := hs.exists_pos
  cases o with
  | none => linarith
  | some v =>
    have : Nonempty V := ⟨v⟩
    exact Nat.pos_of_ne_zero G.cliqueNum_ne_zero_of_finite

/-- Convex decomposition identity ([Suri2007], p. 722): splitting off the `none` weight
`α = t none < 1` writes `t = α • e₀ + (1 - α) • t*` with `t* none = 0`, and
`F(t | t) = (1 - 1 / (2k)) - (1 - α)^2 * ((1 - 1 / (2k)) - F(t* | t*))`. -/
private theorem renormalize_none_decomposition (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    {t : Option V → ℝ} (ht : IsMixedStrategy t) (hne : t ≠ zeroPureStrategy V) :
    ∃ t' : Option V → ℝ, IsMixedStrategy t' ∧ t' none = 0 ∧ t none < 1 ∧
      (cliqueESSGame G k).fitness t t =
        (1 - 1 / (2 * (k : ℝ))) -
          (1 - t none) ^ 2 * ((1 - 1 / (2 * (k : ℝ))) - (cliqueESSGame G k).fitness t' t') := by
  have hle1 : t none ≤ 1 := by
    calc t none ≤ ∑ o, t o :=
          Finset.single_le_sum (fun o _ => ht.nonneg o) (Finset.mem_univ none)
      _ = 1 := ht.sum_eq_one
  have hlt1 : t none < 1 := by
    rcases hle1.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      apply hne
      ext o
      cases o with
      | none => simp [zeroPureStrategy, heq]
      | some v =>
        have hsumV : ∑ w : V, t (some w) = 0 := by
          have := ht.sum_eq_one
          rw [Fintype.sum_option, heq] at this
          linarith
        have hzv : t (some v) = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun w _ => ht.nonneg (some w)).1 hsumV v
            (Finset.mem_univ v)
        simp [zeroPureStrategy, Pi.single_apply, hzv]
  set α := t none
  have h1α : 0 < 1 - α := sub_pos.2 hlt1
  let t' : Option V → ℝ := fun o =>
    match o with
    | none => 0
    | some v => t (some v) / (1 - α)
  have ht'_mix : IsMixedStrategy t' := by
    refine ⟨fun o => ?_, ?_⟩
    · cases o with
      | none => exact le_rfl
      | some v => exact div_nonneg (ht.nonneg (some v)) h1α.le
    · rw [Fintype.sum_option]
      have hsumV : ∑ v : V, t (some v) = 1 - α := by
        have := ht.sum_eq_one
        rw [Fintype.sum_option] at this
        linarith
      simp only [t', zero_add, ← Finset.sum_div, hsumV, div_self h1α.ne']
  have ht_decomp : t = α • zeroPureStrategy V + (1 - α) • t' := by
    ext o
    cases o with
    | none => simp [α, zeroPureStrategy, t']
    | some v =>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zeroPureStrategy,
        Pi.single_eq_of_ne (Option.some_ne_none v), mul_zero, zero_add, t']
      field_simp [h1α.ne']
  have hf_e0_e0 : (cliqueESSGame G k).fitness (zeroPureStrategy V) (zeroPureStrategy V) =
      1 - 1 / (2 * (k : ℝ)) :=
    fitness_zeroPureStrategy_left G k isMixedStrategy_zeroPureStrategy.sum_eq_one
  have hf_e0_t' : (cliqueESSGame G k).fitness (zeroPureStrategy V) t' =
      1 - 1 / (2 * (k : ℝ)) :=
    fitness_zeroPureStrategy_left G k ht'_mix.sum_eq_one
  have hf_t'_e0 : (cliqueESSGame G k).fitness t' (zeroPureStrategy V) =
      1 - 1 / (2 * (k : ℝ)) :=
    fitness_zeroPureStrategy_right G k ht'_mix.sum_eq_one
  refine ⟨t', ht'_mix, rfl, hlt1, ?_⟩
  conv_lhs => rw [ht_decomp]
  rw [SymmetricGame.fitness_add_left, SymmetricGame.fitness_add_right,
    SymmetricGame.fitness_add_right, SymmetricGame.fitness_smul_left,
    SymmetricGame.fitness_smul_left, SymmetricGame.fitness_smul_right,
    SymmetricGame.fitness_smul_right, SymmetricGame.fitness_smul_left,
    SymmetricGame.fitness_smul_left, SymmetricGame.fitness_smul_right,
    SymmetricGame.fitness_smul_right, hf_e0_e0, hf_e0_t', hf_t'_e0]
  ring

/-! ### Lemmas 29.4–29.7 -/

/-- Payoff of pure vertex `some u` against `cliqueUniform C`: `1 - 1 / (2 * #C)` when `u ∈ C`. -/
private theorem cliqueESSGame_mulVec_cliqueUniform_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) {C : Finset V} (hCne : C.Nonempty) (hC : G.IsClique (C : Set V)) {u : V}
    (hu : u ∈ C) :
    ((cliqueESSGame G k).payoff *ᵥ cliqueUniform C) (some u) =
      1 - 1 / (2 * (C.card : ℝ)) := by
  have hcard_pos : (0 : ℝ) < C.card := Nat.cast_pos.2 (Finset.card_pos.2 hCne)
  rw [mulVec, dotProduct, Fintype.sum_option]
  have hzero : (cliqueESSGame G k).payoff (some u) none * cliqueUniform C none = 0 := by
    simp [cliqueUniform]
  rw [hzero, zero_add]
  have hsub : ∀ v : V, v ∉ C →
      (cliqueESSGame G k).payoff (some u) (some v) * cliqueUniform C (some v) = 0 := by
    intro v hv; simp [cliqueUniform, hv]
  rw [← Finset.sum_subset (Finset.subset_univ C) fun v _ hv => hsub v hv]
  have hsplit : ∑ v ∈ C,
      (cliqueESSGame G k).payoff (some u) (some v) * cliqueUniform C (some v) =
      ∑ v ∈ C, (if u = v then (1 / 2) * (1 / (C.card : ℝ)) else 1 / (C.card : ℝ)) := by
    refine Finset.sum_congr rfl fun v hv => ?_
    simp only [cliqueESSGame, cliqueESSPayoff, Matrix.of_apply, cliqueUniform, hv, ↓reduceIte]
    by_cases huv : u = v
    · simp [huv]
    · simp [huv, hC hu hv huv]
  rw [hsplit, ← Finset.add_sum_erase C _ hu]
  have hrest : ∑ v ∈ C.erase u,
      (if u = v then (1 / 2) * (1 / (C.card : ℝ)) else 1 / (C.card : ℝ)) =
      ((C.card : ℝ) - 1) * (1 / (C.card : ℝ)) := by
    have heq : ∑ v ∈ C.erase u,
        (if u = v then (1 / 2) * (1 / (C.card : ℝ)) else 1 / (C.card : ℝ)) =
        ∑ _v ∈ C.erase u, (1 / (C.card : ℝ)) :=
      Finset.sum_congr rfl fun v hv => by
        rw [if_neg (Finset.mem_erase.1 hv).1.symm]
    rw [heq, Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hu,
      Nat.cast_sub (Finset.one_le_card.2 hCne), Nat.cast_one]
  rw [if_pos rfl, hrest]
  field_simp [hcard_pos.ne']
  ring

/-- If `u ∉ C` has a non-neighbor in `C`, its payoff against `cliqueUniform C` is at most
`1 - 1 / #C`. -/
private theorem cliqueESSGame_mulVec_cliqueUniform_not_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) {C : Finset V} (hCne : C.Nonempty) {u w : V} (hu : u ∉ C) (hw : w ∈ C)
    (hnadj : ¬ G.Adj u w) :
    ((cliqueESSGame G k).payoff *ᵥ cliqueUniform C) (some u) ≤
      1 - 1 / (C.card : ℝ) := by
  have hcard_pos : (0 : ℝ) < C.card := Nat.cast_pos.2 (Finset.card_pos.2 hCne)
  rw [mulVec, dotProduct, Fintype.sum_option]
  have hzero : (cliqueESSGame G k).payoff (some u) none * cliqueUniform C none = 0 := by
    simp [cliqueUniform]
  rw [hzero, zero_add]
  have hsub : ∀ v : V, v ∉ C →
      (cliqueESSGame G k).payoff (some u) (some v) * cliqueUniform C (some v) = 0 := by
    intro v hv; simp [cliqueUniform, hv]
  rw [← Finset.sum_subset (Finset.subset_univ C) fun v _ hv => hsub v hv]
  rw [← Finset.add_sum_erase C _ hw]
  have huw : u ≠ w := fun h => hu (h ▸ hw)
  have hterm_w : (cliqueESSGame G k).payoff (some u) (some w) * cliqueUniform C (some w) = 0 := by
    simp [cliqueESSGame, cliqueESSPayoff, Matrix.of_apply, huw, hnadj]
  have hle_rest : ∑ v ∈ C.erase w,
      (cliqueESSGame G k).payoff (some u) (some v) * cliqueUniform C (some v) ≤
      ∑ _v ∈ C.erase w, (1 / (C.card : ℝ)) := by
    refine Finset.sum_le_sum fun v hv => ?_
    have hvC : v ∈ C := (Finset.mem_erase.1 hv).2
    have huv : u ≠ v := fun h => hu (h ▸ hvC)
    simp only [cliqueESSGame, cliqueESSPayoff, Matrix.of_apply, cliqueUniform, huv, hvC,
      ↓reduceIte]
    split_ifs <;> positivity
  rw [hterm_w, zero_add]
  calc ∑ v ∈ C.erase w, (cliqueESSGame G k).payoff (some u) (some v) * cliqueUniform C (some v)
      ≤ ∑ _v ∈ C.erase w, (1 / (C.card : ℝ)) := hle_rest
    _ = ((C.card : ℝ) - 1) * (1 / (C.card : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hw,
          Nat.cast_sub (Finset.one_le_card.2 hCne), Nat.cast_one]
    _ = 1 - 1 / (C.card : ℝ) := by field_simp [hcard_pos.ne']

/-- **Lemma 29.4** ([Suri2007], p. 722): if `C` is a maximal clique of `G` with `k < C.card`
(and `0 < k`), then the uniform distribution `cliqueUniform C` is an ESS of `cliqueESSGame G k`. -/
theorem isESS_cliqueUniform_of_maximal (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hk : 0 < k) {C : Finset V} (hC : G.IsClique (C : Set V))
    (hmax : ∀ u, u ∉ C → ∃ w ∈ C, ¬ G.Adj u w) (hsize : k < C.card) :
    (cliqueESSGame G k).IsESS (cliqueUniform C) := by
  have hCne : C.Nonempty := Finset.card_pos.1 (by omega)
  have hmix : IsMixedStrategy (cliqueUniform C) := isMixedStrategy_cliqueUniform hCne
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hcpos : (0 : ℝ) < C.card := Nat.cast_pos.2 (by omega)
  have hklt : (k : ℝ) < C.card := Nat.cast_lt.2 hsize
  have hself : (cliqueESSGame G k).fitness (cliqueUniform C) (cliqueUniform C) =
      1 - 1 / (2 * (C.card : ℝ)) :=
    fitness_cliqueUniform_self G k hCne hC
  have hnone_lt : ((cliqueESSGame G k).payoff *ᵥ cliqueUniform C) none <
      1 - 1 / (2 * (C.card : ℝ)) := by
    rw [cliqueESSGame_mulVec_none G k hmix.sum_eq_one]
    have : 1 / (2 * (C.card : ℝ)) < 1 / (2 * (k : ℝ)) := by gcongr
    linarith
  have hout_lt : ∀ u, u ∉ C →
      ((cliqueESSGame G k).payoff *ᵥ cliqueUniform C) (some u) <
        1 - 1 / (2 * (C.card : ℝ)) := by
    intro u hu
    obtain ⟨w, hwC, hnw⟩ := hmax u hu
    have hle := cliqueESSGame_mulVec_cliqueUniform_not_mem G k hCne hu hwC hnw
    have : 1 / (2 * (C.card : ℝ)) < 1 / (C.card : ℝ) := by
      have : (0 : ℝ) < 1 / (C.card : ℝ) := by positivity
      linarith [show 1 / (2 * (C.card : ℝ)) = (1 / 2) * (1 / (C.card : ℝ)) by ring]
    linarith
  have hpay_le : ∀ o : Option V,
      ((cliqueESSGame G k).payoff *ᵥ cliqueUniform C) o ≤ 1 - 1 / (2 * (C.card : ℝ)) := by
    intro o
    cases o with
    | none => exact hnone_lt.le
    | some u =>
      by_cases hu : u ∈ C
      · rw [cliqueESSGame_mulVec_cliqueUniform_mem G k hCne hC hu]
      · exact (hout_lt u hu).le
  rw [SymmetricGame.isESS_iff_strict_or_eq]
  refine ⟨hmix, fun t ht hne => ?_⟩
  by_cases hsupp : t none = 0 ∧ ∀ u, u ∉ C → t (some u) = 0
  · right
    have hsumC : ∑ u ∈ C, t (some u) = 1 := by
      have htot := ht.sum_eq_one
      rw [Fintype.sum_option, hsupp.1, zero_add] at htot
      rw [← htot]
      exact Finset.sum_subset (Finset.subset_univ C) fun u _ hu => hsupp.2 u hu
    have hts : (cliqueESSGame G k).fitness t (cliqueUniform C) =
        1 - 1 / (2 * (C.card : ℝ)) := by
      refine ht.dotProduct_eq_of_forall_pos fun o ho => ?_
      cases o with
      | none => linarith [hsupp.1]
      | some u =>
        have hu : u ∈ C := by
          by_contra hu'
          linarith [hsupp.2 u hu']
        exact cliqueESSGame_mulVec_cliqueUniform_mem G k hCne hC hu
    have hst : (cliqueESSGame G k).fitness (cliqueUniform C) t =
        1 - 1 / (2 * (C.card : ℝ)) := by
      rw [SymmetricGame.fitness_symm _ (cliqueESSPayoff_isSymm G k), hts]
    have htt : (cliqueESSGame G k).fitness t t =
        1 - (1 / 2) * ∑ u ∈ C, t (some u) ^ 2 := by
      rw [fitness_cliqueESSGame_of_none_eq_zero G k hsupp.1]
      have hsumV : ∑ u : V, t (some u) = 1 := by
        have := ht.sum_eq_one
        rw [Fintype.sum_option, hsupp.1, zero_add] at this
        exact this
      exact vertexQuad_eq_of_isClique G hC hsupp.2 hsumV
    have hcs := sum_sq_sub_one_div_card hCne hsumC (x := fun u => t (some u))
    have hdiff_pos : 0 < ∑ u ∈ C, (t (some u) - 1 / (C.card : ℝ)) ^ 2 := by
      by_contra hle
      push Not at hle
      have h0 : ∑ u ∈ C, (t (some u) - 1 / (C.card : ℝ)) ^ 2 = 0 :=
        le_antisymm hle (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      apply hne
      ext o
      cases o with
      | none => exact hsupp.1
      | some u =>
        by_cases hu : u ∈ C
        · have hsq0 : (t (some u) - 1 / (C.card : ℝ)) ^ 2 = 0 :=
            (Finset.sum_eq_zero_iff_of_nonneg fun w _ => sq_nonneg _).1 h0 u hu
          have := sub_eq_zero.1 (sq_eq_zero_iff.1 hsq0)
          simpa only [cliqueUniform, hu, ↓reduceIte] using this
        · simp [cliqueUniform, hu, hsupp.2 u hu]
    refine ⟨by rw [hts, hself], ?_⟩
    linarith
  · left
    rw [hself, SymmetricGame.fitness]
    have hlt_exists : ∃ o : Option V, 0 < t o ∧
        ((cliqueESSGame G k).payoff *ᵥ cliqueUniform C) o < 1 - 1 / (2 * (C.card : ℝ)) := by
      rcases not_and_or.1 hsupp with h0 | hV
      · exact ⟨none, lt_of_le_of_ne (ht.nonneg none) (Ne.symm h0), hnone_lt⟩
      · push Not at hV
        obtain ⟨u, hu, hu_ne⟩ := hV
        exact ⟨some u, lt_of_le_of_ne (ht.nonneg (some u)) (Ne.symm hu_ne), hout_lt u hu⟩
    obtain ⟨o₀, ho₀_pos, ho₀_lt⟩ := hlt_exists
    calc t ⬝ᵥ ((cliqueESSGame G k).payoff *ᵥ cliqueUniform C)
        = ∑ o, t o * ((cliqueESSGame G k).payoff *ᵥ cliqueUniform C) o := rfl
      _ < ∑ o, t o * (1 - 1 / (2 * (C.card : ℝ))) :=
          Finset.sum_lt_sum
            (fun o _ => mul_le_mul_of_nonneg_left (hpay_le o) (ht.nonneg o))
            ⟨o₀, Finset.mem_univ o₀, mul_lt_mul_of_pos_left ho₀_lt ho₀_pos⟩
      _ = 1 - 1 / (2 * (C.card : ℝ)) := by rw [← Finset.sum_mul, ht.sum_eq_one, one_mul]

/-- **Lemma 29.5** ([Suri2007], p. 722): if `G.cliqueNum < k` (with `0 < k`), then pure
strategy `0` (`zeroPureStrategy V`) is an ESS of `cliqueESSGame G k`. -/
theorem isESS_zeroPureStrategy_of_cliqueNum_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hlt : G.cliqueNum < k) :
    (cliqueESSGame G k).IsESS (zeroPureStrategy V) := by
  have hk : 0 < k := by omega
  rw [SymmetricGame.isESS_iff_strict_or_eq]
  refine ⟨isMixedStrategy_zeroPureStrategy, fun t ht hne => ?_⟩
  right
  have heq : (cliqueESSGame G k).fitness t (zeroPureStrategy V) =
      (cliqueESSGame G k).fitness (zeroPureStrategy V) (zeroPureStrategy V) := by
    rw [fitness_zeroPureStrategy_right G k ht.sum_eq_one,
      fitness_zeroPureStrategy_left G k isMixedStrategy_zeroPureStrategy.sum_eq_one]
  refine ⟨heq, ?_⟩
  rw [fitness_zeroPureStrategy_left G k ht.sum_eq_one]
  obtain ⟨t', ht', ht'0, ht_lt, hdecomp⟩ := renormalize_none_decomposition G k ht hne
  have hωpos : 0 < G.cliqueNum := cliqueNum_pos_of_isMixedStrategy_none_zero G ht' ht'0
  have hms := fitness_cliqueESSGame_le G k ht' ht'0
  have hωposR : (0 : ℝ) < G.cliqueNum := Nat.cast_pos.2 hωpos
  have hωltR : (G.cliqueNum : ℝ) < k := Nat.cast_lt.2 hlt
  have hfrac : 1 / (2 * (k : ℝ)) < 1 / (2 * (G.cliqueNum : ℝ)) := by gcongr
  have hgap : 0 < (1 - 1 / (2 * (k : ℝ))) - (cliqueESSGame G k).fitness t' t' := by linarith
  have hsq : 0 < (1 - t none) ^ 2 := sq_pos_of_pos (sub_pos.2 ht_lt)
  rw [hdecomp]
  nlinarith

/-- **Lemma 29.6** ([Suri2007], p. 722): if `k ≤ G.cliqueNum` (and `0 < k`), then pure
strategy `0` (`zeroPureStrategy V`) is *not* an ESS of `cliqueESSGame G k`. -/
theorem not_isESS_zeroPureStrategy_of_le_cliqueNum (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 0 < k) (hle : k ≤ G.cliqueNum) :
    ¬ (cliqueESSGame G k).IsESS (zeroPureStrategy V) := by
  intro hess
  obtain ⟨C, hC⟩ := G.exists_isNClique_cliqueNum
  have hCne : C.Nonempty := Finset.card_pos.1 (by rw [hC.card_eq]; omega)
  let t := cliqueUniform C
  have ht : IsMixedStrategy t := isMixedStrategy_cliqueUniform hCne
  have hne : t ≠ zeroPureStrategy V := cliqueUniform_ne_zeroPureStrategy C
  have heq : (cliqueESSGame G k).fitness t (zeroPureStrategy V) =
      (cliqueESSGame G k).fitness (zeroPureStrategy V) (zeroPureStrategy V) := by
    rw [fitness_zeroPureStrategy_right G k ht.sum_eq_one,
      fitness_zeroPureStrategy_left G k isMixedStrategy_zeroPureStrategy.sum_eq_one]
  have hlt := hess.fitness_lt_of_eq ht hne heq
  rw [fitness_zeroPureStrategy_left G k ht.sum_eq_one,
    fitness_cliqueUniform_self G k hCne hC.isClique, hC.card_eq] at hlt
  have hkposR : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hleR : (k : ℝ) ≤ G.cliqueNum := Nat.cast_le.2 hle
  have hfrac : 1 / (2 * (G.cliqueNum : ℝ)) ≤ 1 / (2 * (k : ℝ)) := by gcongr
  linarith

/-- **Lemma 29.7 / Exercise 29.5** ([Suri2007], pp. 722–723, 735): if `G.cliqueNum ≤ k`
(and `0 < k`), then *no* strategy distinct from pure strategy `0` is an ESS of `cliqueESSGame G k`. -/
theorem not_isESS_of_cliqueNum_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hle : G.cliqueNum ≤ k) {s : Option V → ℝ}
    (hne : s ≠ zeroPureStrategy V) :
    ¬ (cliqueESSGame G k).IsESS s := by
  intro hess
  obtain ⟨s', hs', hs'0, hs_lt, hdecomp⟩ :=
    renormalize_none_decomposition G k hess.isMixedStrategy hne
  have hωpos : 0 < G.cliqueNum := cliqueNum_pos_of_isMixedStrategy_none_zero G hs' hs'0
  have hms := fitness_cliqueESSGame_le G k hs' hs'0
  have hωposR : (0 : ℝ) < G.cliqueNum := Nat.cast_pos.2 hωpos
  have hleR : (G.cliqueNum : ℝ) ≤ k := Nat.cast_le.2 hle
  have hfrac : 1 / (2 * (k : ℝ)) ≤ 1 / (2 * (G.cliqueNum : ℝ)) := by gcongr
  have hs'_le : (cliqueESSGame G k).fitness s' s' ≤ 1 - 1 / (2 * (k : ℝ)) := by linarith
  have hsq_pos : 0 < (1 - s none) ^ 2 := sq_pos_of_pos (sub_pos.2 hs_lt)
  have he0s : (cliqueESSGame G k).fitness (zeroPureStrategy V) s =
      1 - 1 / (2 * (k : ℝ)) :=
    fitness_zeroPureStrategy_left G k hess.isMixedStrategy.sum_eq_one
  have hbr := hess.fitness_le_self isMixedStrategy_zeroPureStrategy
  rcases hs'_le.lt_or_eq with hlt | heq
  · rw [hdecomp, he0s] at hbr
    nlinarith
  · have htie : (cliqueESSGame G k).fitness (zeroPureStrategy V) s =
        (cliqueESSGame G k).fitness s s := by
      rw [he0s, hdecomp, heq]
      ring
    have hlt := hess.fitness_lt_of_eq isMixedStrategy_zeroPureStrategy hne.symm htie
    rw [fitness_zeroPureStrategy_left G k isMixedStrategy_zeroPureStrategy.sum_eq_one,
      fitness_zeroPureStrategy_right G k hess.isMixedStrategy.sum_eq_one] at hlt
    exact lt_irrefl _ hlt

/-! ### Exact characterizations -/

/-- For `k ≥ 1`, pure strategy `0` (`zeroPureStrategy V`) is an ESS of `cliqueESSGame G k`
if and only if `G.cliqueNum < k` (combining Lemmas 29.5 and 29.6, [Suri2007], p. 723). -/
theorem isESS_zeroPureStrategy_iff (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hk : 0 < k) :
    (cliqueESSGame G k).IsESS (zeroPureStrategy V) ↔ G.cliqueNum < k := by
  constructor
  · intro h
    by_contra hnot
    exact not_isESS_zeroPureStrategy_of_le_cliqueNum G hk (Nat.le_of_not_lt hnot) h
  · exact isESS_zeroPureStrategy_of_cliqueNum_lt G

/-- For `k ≥ 1`, `cliqueESSGame G k` possesses an ESS if and only if `G.cliqueNum ≠ k`
(combining Lemmas 29.4, 29.5, 29.6, and 29.7, [Suri2007], pp. 722–723). -/
theorem hasESS_cliqueESSGame_iff (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hk : 0 < k) :
    (cliqueESSGame G k).HasESS ↔ G.cliqueNum ≠ k := by
  constructor
  · rintro ⟨s, hs⟩ hEq
    by_cases h0 : s = zeroPureStrategy V
    · subst h0
      exact not_isESS_zeroPureStrategy_of_le_cliqueNum G hk hEq.ge hs
    · exact not_isESS_of_cliqueNum_le G hEq.le h0 hs
  · intro hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨zeroPureStrategy V, isESS_zeroPureStrategy_of_cliqueNum_lt G hlt⟩
    · obtain ⟨C, hC⟩ := G.exists_isNClique_cliqueNum
      have hmax : ∀ u, u ∉ C → ∃ w ∈ C, ¬ G.Adj u w := by
        intro u hu
        by_contra hall
        push Not at hall
        have hinsert : G.IsClique ((insert u C : Finset V) : Set V) := by
          rw [Finset.coe_insert]
          exact hC.isClique.insert fun w hw _ => hall w hw
        have hle := hinsert.card_le_cliqueNum
        rw [Finset.card_insert_of_notMem hu, hC.card_eq] at hle
        omega
      refine ⟨cliqueUniform C,
        isESS_cliqueUniform_of_maximal G hk hC.isClique hmax (hC.card_eq ▸ hgt)⟩

end Cslib.GameTheory
