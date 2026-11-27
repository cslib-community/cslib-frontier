/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MarkovChain.Coloring
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpOneSubInvPow
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Freezing one vertex keeps a fraction of the colorings

Fix a proper coloring `b` of a graph `G` with maximum degree `Δ`, a set `U` of vertices and
`v ∈ U`, and let `X_U` be the proper `q`-colorings agreeing with `b` off `U`
(`SimpleGraph.frozenColorings`). Freezing `v` at its color `b v` keeps a fraction at least
`(1 - 1 / (q - Δ)) ^ Δ / q` of `X_U` when `Δ < q`
(`Cslib.Probability.MarkovChain.mul_card_frozenColorings_le_card_erase`), hence at least
`1 / (e q)` when `2Δ < q`
(`Cslib.Probability.MarkovChain.inv_exp_mul_le_card_frozenColorings_erase_div`). This is
[LevinPeres2017], Lemma 14.16, the lower bound on the ratios `|X_{k-1}| / |X_k|` estimated by the
approximate counting algorithm of [LevinPeres2017], Section 14.4.2.

The proof follows [LevinPeres2017]. Start from the uniform distribution `π` on `X_U` and recolor,
by heat-bath updates (`Cslib.Probability.MarkovChain.recolor`), the neighbors of `v` in `U` and
then `v`. Each update preserves `π` (`Cslib.Probability.MarkovChain.isStationary_recolor_frozen`).
An update at a neighbor avoids `b v` with probability at least `1 - 1 / (q - Δ)`, since at least
`q - Δ` colors are allowed. Once no neighbor has color `b v`, which already holds off `U` because
`b` is proper, the update at `v` picks `b v` with probability at least `1 / q`. The ending
distribution is `π`, and `x v = b v` is the event `x ∈ X_{U \ {v}}`.

## Main results

* `Cslib.Probability.MarkovChain.sum_uniformOfFinset_frozenColorings_ite`: under the uniform
  distribution on `X_U`, the probability that `x v = b v` is `|X_{U \ {v}}| / |X_U|`.
* `Cslib.Probability.MarkovChain.mul_card_frozenColorings_le_card_erase`: the bound
  `(1 - 1 / (q - Δ)) ^ Δ / q`.
* `Cslib.Probability.MarkovChain.inv_exp_mul_le_card_frozenColorings_erase_div`:
  [LevinPeres2017], Lemma 14.16.

## References

* [LevinPeres2017], Section 14.4.2.
-/

public section

open scoped ENNReal Cslib.Probability.PMF

namespace Cslib.Probability.MarkovChain

open Cslib.Probability.PMF SimpleGraph

variable {V : Type*} {q : ℕ} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem toOuterMeasure_uniform_frozenColorings {U : Finset V} {b : V → Fin q}
    (hne : (frozenColorings G q U b).Nonempty) (v : V) :
    ((uniformOfFinset (frozenColorings G q U b) hne).toOuterMeasure {x | x v = b v}).toReal =
      ((frozenColorings G q (U.erase v) b).card : ℝ) / (frozenColorings G q U b).card := by
  rw [toOuterMeasure_uniformOfFinset_toReal, frozenColorings_erase]
  rfl

/-- Under the uniform distribution on `X_U`, the probability that `x v = b v` is
`|X_{U \ {v}}| / |X_U|`. -/
theorem sum_uniformOfFinset_frozenColorings_ite {U : Finset V} {b : V → Fin q}
    (hne : (frozenColorings G q U b).Nonempty) (v : V) :
    ∑ x, ((uniformOfFinset (frozenColorings G q U b) hne) x).toReal *
        (if x v = b v then 1 else 0) =
      ((frozenColorings G q (U.erase v) b).card : ℝ) / (frozenColorings G q U b).card := by
  simpa only [toOuterMeasure_toReal_eq_sum_ite, Set.mem_ofPred_eq] using
    toOuterMeasure_uniform_frozenColorings hne v

/-- **Freezing a vertex** ([LevinPeres2017], proof of Lemma 14.16): if `b` is a proper coloring,
`Δ < q` and `v ∈ U`, then freezing `v` at `b v` keeps a fraction at least
`(1 - 1 / (q - Δ)) ^ Δ / q` of the colorings agreeing with `b` off `U`. -/
theorem mul_card_frozenColorings_le_card_erase (hq : G.maxDegree < q) {b : V → Fin q}
    (hb : G.IsProperColoring b) {U : Finset V} {v : V} (hv : v ∈ U) :
    (1 - 1 / ((q - G.maxDegree : ℕ) : ℝ)) ^ G.maxDegree / q *
        (frozenColorings G q U b).card ≤ (frozenColorings G q (U.erase v) b).card := by
  have hne : (frozenColorings G q U b).Nonempty := ⟨b, mem_frozenColorings_self hb⟩
  set π := uniformOfFinset (frozenColorings G q U b) hne with hπ_def
  set r : ℝ := 1 - 1 / ((q - G.maxDegree : ℕ) : ℝ) with hr_def
  have hD : (1 : ℝ) ≤ ((q - G.maxDegree : ℕ) : ℝ) := by
    exact_mod_cast (by lia : 1 ≤ q - G.maxDegree)
  have hr0 : 0 ≤ r := sub_nonneg.mpr (div_le_one_of_le₀ hD (by linarith))
  have hr1 : r ≤ 1 := sub_le_self _ (by positivity)
  have hstat (w : V) (hw : w ∈ U) : π.bind (recolor G · w) = π :=
    isStationary_recolor_frozen G hne hw
  -- recoloring the vertices of `F ⊆ U` one at a time: no vertex of `F` has color `b v`
  have hF : ∀ F : Finset V, F ⊆ U →
      r ^ F.card ≤ (π.toOuterMeasure {x | ∀ u ∈ F, x u ≠ b v}).toReal := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _
      rw [show {x : V → Fin q | ∀ u ∈ (∅ : Finset V), x u ≠ b v} = Set.univ by ext; simp,
        (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)]
      simp
    | @insert w F hwF ih =>
      intro hsub
      have hwU : w ∈ U := hsub (Finset.mem_insert_self w F)
      have ih' := ih ((Finset.subset_insert w F).trans hsub)
      have key := toOuterMeasure_bind_ge_mul π (recolor G · w)
        {x | ∀ u ∈ F, x u ≠ b v} {x | ∀ u ∈ insert w F, x u ≠ b v} hr0 ih' ?_
      · rwa [hstat w hwU, ← pow_succ, ← Finset.card_insert_of_notMem hwF] at key
      intro x _ hx
      have hA := G.allowedColors_nonempty hq x w
      rw [recolor_of_nonempty G hA, PMF.toOuterMeasure_map_apply]
      have hpre : (Function.update x w) ⁻¹' {x' | ∀ u ∈ insert w F, x' u ≠ b v} =
          ({b v} : Set (Fin q))ᶜ := by
        ext c
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff,
          Finset.forall_mem_insert, Function.update_self]
        exact ⟨And.left, fun hc => ⟨hc, fun u hu => by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hu hwF)]
          exact hx u hu⟩⟩
      rw [hpre]
      have hmass := toOuterMeasure_toReal_add_compl (uniformOfFinset _ hA) {b v}
      rw [PMF.toOuterMeasure_apply_singleton] at hmass
      have hcard : (((q - G.maxDegree : ℕ) : ℝ)) ≤ (G.allowedColors x w).card := by
        exact_mod_cast G.sub_maxDegree_le_card_allowedColors x w
      have hle : ((uniformOfFinset (G.allowedColors x w) hA) (b v)).toReal ≤
          1 / ((q - G.maxDegree : ℕ) : ℝ) := by
        rw [uniformOfFinset_apply]
        split_ifs
        · rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, ← one_div]
          exact one_div_le_one_div_of_le (by linarith) hcard
        · rw [ENNReal.toReal_zero]
          positivity
      linarith only [hmass, hle]
  -- the neighbors of `v` in `U`
  set F := U.filter fun u => G.Adj v u with hF_def
  have hFcard : F.card ≤ G.maxDegree := by
    refine (Finset.card_le_card fun u hu =>
      (G.mem_neighborFinset v u).2 (Finset.mem_filter.1 hu).2).trans
      ((G.card_neighborFinset_eq_degree v).trans_le (G.degree_le_maxDegree v))
  -- the final update at `v` picks `b v` with probability at least `1 / q`
  have hfinal : r ^ F.card * (q : ℝ)⁻¹ ≤ (π.toOuterMeasure {x | x v = b v}).toReal := by
    have key := toOuterMeasure_bind_ge_mul π (recolor G · v) {x | ∀ u ∈ F, x u ≠ b v}
      {x | x v = b v} (by positivity : 0 ≤ (q : ℝ)⁻¹) (hF F (Finset.filter_subset _ _)) ?_
    · rwa [hstat v hv] at key
    intro x hxπ hx
    obtain ⟨hxp, hxb⟩ := mem_frozenColorings.1 ((mem_support_uniformOfFinset_iff hne x).1 hxπ)
    have hbv : b v ∈ G.allowedColors x v := by
      refine (mem_allowedColors G).2 fun u hu => ?_
      by_cases huU : u ∈ U
      · exact hx u (Finset.mem_filter.2 ⟨huU, hu⟩)
      · rw [hxb u huU]
        exact (((isProperColoring_iff G).1 hb) v u hu).symm
    have hA : (G.allowedColors x v).Nonempty := ⟨b v, hbv⟩
    rw [recolor_of_nonempty G hA, PMF.toOuterMeasure_map_apply,
      show (Function.update x v) ⁻¹' {y | y v = b v} = {b v} by ext c; simp,
      PMF.toOuterMeasure_apply_singleton, uniformOfFinset_apply, ite_eq_left hbv,
      ENNReal.toReal_inv, ENNReal.toReal_natCast]
    exact inv_anti₀ (Nat.cast_pos.2 hA.card_pos)
      (by exact_mod_cast (Finset.card_le_univ _).trans_eq (Fintype.card_fin q))
  rw [← le_div_iff₀ (Nat.cast_pos.2 hne.card_pos),
    ← toOuterMeasure_uniform_frozenColorings hne v, ← hπ_def, div_eq_mul_inv]
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hr0 hr1 hFcard)
    (by positivity)).trans hfinal

/-- **The ratios are not too small** ([LevinPeres2017], Lemma 14.16): if `b` is a proper
coloring, `2Δ < q` and `v ∈ U`, then freezing `v` at `b v` keeps a fraction at least `1 / (e q)`
of the colorings agreeing with `b` off `U`. -/
theorem inv_exp_mul_le_card_frozenColorings_erase_div (hq : 2 * G.maxDegree < q) {b : V → Fin q}
    (hb : G.IsProperColoring b) {U : Finset V} {v : V} (hv : v ∈ U) :
    (Real.exp 1 * q)⁻¹ ≤
      ((frozenColorings G q (U.erase v) b).card : ℝ) / (frozenColorings G q U b).card := by
  have hne : (frozenColorings G q U b).Nonempty := ⟨b, mem_frozenColorings_self hb⟩
  have hX : (0 : ℝ) < (frozenColorings G q U b).card := Nat.cast_pos.2 hne.card_pos
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.2 (by lia)
  have h := mul_card_frozenColorings_le_card_erase (by lia) hb hv
  have hexp : Real.exp (-1) ≤ (1 - 1 / ((q - G.maxDegree : ℕ) : ℝ)) ^ G.maxDegree := by
    rw [one_div]
    refine Real.exp_neg_one_le_one_sub_inv_pow ?_
    exact_mod_cast (by lia : G.maxDegree + 1 ≤ q - G.maxDegree)
  rw [le_div_iff₀ hX]
  calc (Real.exp 1 * q)⁻¹ * (frozenColorings G q U b).card
      = Real.exp (-1) / q * (frozenColorings G q U b).card := by
        rw [Real.exp_neg, mul_inv]
        ring
    _ ≤ (1 - 1 / ((q - G.maxDegree : ℕ) : ℝ)) ^ G.maxDegree / q *
          (frozenColorings G q U b).card := by
        gcongr
    _ ≤ _ := h

end Cslib.Probability.MarkovChain
