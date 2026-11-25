/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MarkovChain.HittingTime
public import CslibFrontier.Probability.MarkovChain.Spectral
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Hitting times of the simple random walk on a graph

The simple random walk on a finite graph `G` moves from `x` to a uniformly random neighbor of `x`
(`Cslib.Probability.MarkovChain.randomWalk`): its transition probabilities are
`P x y = 1 / deg x` for adjacent `x`, `y` and `0` otherwise (`randomWalk_apply`). An isolated
vertex keeps the walk in place, so `randomWalk G` is a Markov chain for every graph, and the
expected hitting and return times of `Cslib.Probability.MarkovChain.hittingTime` apply.

The degrees form a stationary measure: `∑ x, deg x * P x y = deg y`
(`sum_degree_mul_randomWalk`). Since `∑ x, deg x = 2 |E|`, Kac's formula gives
`deg v * E_v[τ⁺_v] = 2 |E|` in a connected graph (`degree_mul_returnTime_randomWalk`), that is,
`E_v[τ⁺_v] = 2 |E| / deg v` when `deg v > 0`. On a single vertex `deg v = 0` and the walk
stays put (`randomWalk_apply_of_degree_eq_zero`), so `E_v[τ⁺_v] = 1` while `2 |E| / deg v = 0` in
`ℝ≥0∞`. For `deg v > 0`, conditioning on the first step gives
`E_v[τ⁺_v] = 1 + (1 / deg v) ∑_{u ~ v} E_u[τ_v]`, so the expected hitting times of `v` from its
neighbors sum to `2 |E| - deg v` (`degree_add_sum_hittingTime_randomWalk`). In particular, for
every edge `{u, v}`, `E_u[τ_v] ≤ 2 |E| - deg v ≤ 2 |E|` (`hittingTime_randomWalk_add_degree_le`,
`hittingTime_randomWalk_le_of_adj`). This is the endpoint of Exercise 6.19 of Goldreich's draft,
which completes the proof of his Proposition 6.13 [Goldreich, Exercise 6.19][Goldreich2007Draft].
The proof here goes through Kac's formula and the neighbor sum
[Levin and Peres, Section 10.6][LevinPeres2017]; Goldreich's guideline instead counts traversals
of the stationary walk and takes a commute-time limit. By the triangle inequality for hitting times,
`E_u[τ_v] ≤ ℓ · 2 |E|` along any walk of length `ℓ` from `u` to `v`
(`hittingTime_randomWalk_le_length_mul`, `hittingTime_randomWalk_le_dist_mul`).

## Main definitions

* `Cslib.Probability.MarkovChain.randomWalk`: the simple random walk on a graph.
* `Cslib.Probability.MarkovChain.degreeStationary`: the degree-proportional stationary distribution
  `π(v) = deg(v) / (2 |E|)` on a graph with at least one edge.

## Main results

* `Cslib.Probability.MarkovChain.randomWalk_apply`,
  `Cslib.Probability.MarkovChain.randomWalk_apply_of_degree_eq_zero`: its transition
  probabilities from a vertex with a neighbor and from an isolated vertex.
* `Cslib.Probability.MarkovChain.sum_degree_mul_randomWalk`: the degrees are stationary.
* `Cslib.Probability.MarkovChain.isReversible_randomWalk`,
  `Cslib.Probability.MarkovChain.isStationary_randomWalk`: detailed balance and stationarity of
  `degreeStationary`.
* `Cslib.Probability.MarkovChain.distToStationary_lazy_randomWalk_le`,
  `Cslib.Probability.MarkovChain.mixingTime_lazy_randomWalk_le`: total-variation and mixing-time
  bounds for `(randomWalk G).lazy` on connected nontrivial graphs via `spectralGap`.
* `Cslib.Probability.MarkovChain.degree_mul_returnTime_randomWalk`: `deg v * E_v[τ⁺_v] = 2 |E|`.
* `Cslib.Probability.MarkovChain.hittingTime_randomWalk_add_degree_le`,
  `Cslib.Probability.MarkovChain.hittingTime_randomWalk_le_of_adj`: `E_u[τ_v] + deg v ≤ 2 |E|`
  for every edge `{u, v}` of a connected graph (Goldreich, Exercise 6.19).
* `Cslib.Probability.MarkovChain.hittingTime_randomWalk_le_length_mul`,
  `Cslib.Probability.MarkovChain.hittingTime_randomWalk_le_dist_mul`: `E_u[τ_v] ≤ ℓ · 2 |E|`
  when a walk of length `ℓ` joins `u` to `v`.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2007Draft]
* [D. A. Levin, Y. Peres, *Markov Chains and Mixing Times*][LevinPeres2017]
-/

public section

namespace Cslib.Probability.MarkovChain

open Finset SimpleGraph
open scoped ENNReal

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **simple random walk** on `G`: from `x`, move to a uniformly random neighbor of `x`. An
isolated vertex keeps the walk in place. -/
noncomputable def randomWalk : MarkovChain V where
  step x :=
    if h : (G.neighborFinset x).Nonempty then PMF.uniformOfFinset _ h else _root_.PMF.pure x

variable {G}

/-- The transition probabilities of the simple random walk from a vertex with a neighbor. -/
theorem randomWalk_apply {x : V} (hx : 0 < G.degree x) (y : V) :
    randomWalk G x y = if G.Adj x y then (G.degree x : ℝ≥0∞)⁻¹ else 0 := by
  have hne : (G.neighborFinset x).Nonempty := by
    rwa [← card_pos, card_neighborFinset_eq_degree]
  change (if h : (G.neighborFinset x).Nonempty then PMF.uniformOfFinset _ h
    else _root_.PMF.pure x) y = _
  rw [dite_eq_left hne, PMF.uniformOfFinset_apply, card_neighborFinset_eq_degree]
  simp

/-- From an isolated vertex the simple random walk stays put. -/
theorem randomWalk_apply_of_degree_eq_zero [DecidableEq V] {x : V} (hx : G.degree x = 0) (y : V) :
    randomWalk G x y = if y = x then 1 else 0 := by
  have hne : ¬ (G.neighborFinset x).Nonempty := by
    rw [← card_pos, card_neighborFinset_eq_degree, hx]; exact lt_irrefl 0
  change (if h : (G.neighborFinset x).Nonempty then PMF.uniformOfFinset _ h
    else _root_.PMF.pure x) y = _
  rw [dite_eq_right hne]
  by_cases h : y = x <;> simp [h, PMF.pure_apply]

theorem randomWalk_apply_of_adj {x y : V} (h : G.Adj x y) :
    randomWalk G x y = (G.degree x : ℝ≥0∞)⁻¹ := by
  rw [randomWalk_apply h.degree_pos_left, ite_eq_left h]

theorem randomWalk_apply_of_not_adj {x y : V} (hx : 0 < G.degree x) (h : ¬ G.Adj x y) :
    randomWalk G x y = 0 := by
  rw [randomWalk_apply hx, ite_eq_right h]

theorem randomWalk_ne_zero_of_adj {x y : V} (h : G.Adj x y) : randomWalk G x y ≠ 0 := by
  rw [randomWalk_apply_of_adj h]
  exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)

/-- The degrees form a stationary measure of the simple random walk. -/
theorem sum_degree_mul_randomWalk (y : V) :
    ∑ x, (G.degree x : ℝ≥0∞) * randomWalk G x y = G.degree y := by
  have hterm (x) : (G.degree x : ℝ≥0∞) * randomWalk G x y = if G.Adj y x then 1 else 0 := by
    rcases (G.degree x).eq_zero_or_pos with hx | hx
    · simp [hx, show ¬ G.Adj y x from fun h => hx.not_gt h.degree_pos_right]
    by_cases h : G.Adj x y
    · rw [randomWalk_apply_of_adj h, ite_eq_left h.symm]
      exact ENNReal.mul_inv_cancel (by exact_mod_cast hx.ne') (ENNReal.natCast_ne_top _)
    · simp [randomWalk_apply_of_not_adj hx h, show ¬ G.Adj y x from fun h' => h h'.symm]
  simp_rw [hterm]
  rw [sum_boole, ← neighborFinset_eq_filter, card_neighborFinset_eq_degree]

variable [DecidableEq V]

/-- In a connected graph, the expected hitting time of any vertex is finite. -/
theorem hittingTime_randomWalk_ne_top (hG : G.Connected) (v x : V) :
    hittingTime (randomWalk G) v x ≠ ⊤ := by
  refine hittingTime_ne_top (S := Set.univ) (by simp) (fun y _ => ?_) (Set.mem_univ x)
  exact Relation.ReflTransGen.mono (fun a b h => randomWalk_ne_zero_of_adj h) _ _
    ((reachable_iff_reflTransGen y v).1 (hG y v))

/-- **Expected return time** of the simple random walk on a connected graph:
`deg v * E_v[τ⁺_v] = 2 |E|`, by Kac's formula for the stationary measure given by the
degrees. -/
theorem degree_mul_returnTime_randomWalk (hG : G.Connected) (v : V) :
    (G.degree v : ℝ≥0∞) * returnTime (randomWalk G) v = 2 * #G.edgeFinset := by
  rw [mul_returnTime_eq sum_degree_mul_randomWalk v, ← Nat.cast_sum,
    sum_degrees_eq_twice_card_edges]
  · push_cast; rfl
  · exact (ENNReal.sum_lt_top.2 fun x _ => ENNReal.mul_lt_top (ENNReal.natCast_lt_top _)
      (hittingTime_randomWalk_ne_top hG v x).lt_top).ne

/-- In a connected graph, the expected hitting times of `v` from its neighbors sum to
`2 |E| - deg v`. -/
theorem degree_add_sum_hittingTime_randomWalk (hG : G.Connected) {v : V} (hv : 0 < G.degree v) :
    (G.degree v : ℝ≥0∞) + ∑ u ∈ G.neighborFinset v, hittingTime (randomWalk G) v u =
      2 * #G.edgeFinset := by
  have hd : (G.degree v : ℝ≥0∞) ≠ 0 := by exact_mod_cast hv.ne'
  rw [← degree_mul_returnTime_randomWalk hG v, returnTime_eq, mul_add, mul_one, mul_sum]
  congr 1
  rw [← sum_filter_add_sum_filter_not univ (G.Adj v),
    sum_eq_zero (s := univ.filter fun u => ¬ G.Adj v u) fun u hu => by
      simp [randomWalk_apply_of_not_adj hv (mem_filter.1 hu).2],
    add_zero, ← neighborFinset_eq_filter]
  refine sum_congr rfl fun u hu => ?_
  rw [randomWalk_apply_of_adj ((mem_neighborFinset G v u).1 hu), ← mul_assoc,
    ENNReal.mul_inv_cancel hd (ENNReal.natCast_ne_top _), one_mul]

/-- **Goldreich, Exercise 6.19.** For an edge `{u, v}` of a connected graph `G = (V, E)`, the
expected number of steps of the random walk from `u` to reach `v` satisfies
`E_u[τ_v] + deg v ≤ 2 |E|`. -/
theorem hittingTime_randomWalk_add_degree_le (hG : G.Connected) {u v : V} (huv : G.Adj u v) :
    hittingTime (randomWalk G) v u + G.degree v ≤ 2 * #G.edgeFinset := by
  rw [← degree_add_sum_hittingTime_randomWalk hG huv.degree_pos_right, add_comm]
  gcongr
  exact single_le_sum (f := fun u => hittingTime (randomWalk G) v u) (fun _ _ => zero_le)
    ((mem_neighborFinset G v u).2 huv.symm)

/-- **Goldreich, Exercise 6.19.** For an edge `{u, v}` of a connected graph `G = (V, E)`,
`E_u[τ_v] ≤ 2 |E|`. -/
theorem hittingTime_randomWalk_le_of_adj (hG : G.Connected) {u v : V} (huv : G.Adj u v) :
    hittingTime (randomWalk G) v u ≤ 2 * #G.edgeFinset :=
  le_self_add.trans (hittingTime_randomWalk_add_degree_le hG huv)

/-- Along a walk of length `ℓ` from `u` to `v` in a connected graph,
`E_u[τ_v] ≤ ℓ · 2 |E|`. -/
theorem hittingTime_randomWalk_le_length_mul (hG : G.Connected) {u v : V} (p : G.Walk u v) :
    hittingTime (randomWalk G) v u ≤ p.length * (2 * #G.edgeFinset) := by
  induction p with
  | nil => simp
  | @cons x y z hxy p ih =>
    calc hittingTime (randomWalk G) z x
        ≤ hittingTime (randomWalk G) y x + hittingTime (randomWalk G) z y :=
          hittingTime_le_add y z x
      _ ≤ 2 * #G.edgeFinset + p.length * (2 * #G.edgeFinset) :=
          add_le_add (hittingTime_randomWalk_le_of_adj hG hxy) ih
      _ = (Walk.cons hxy p).length * (2 * #G.edgeFinset) := by
          rw [Walk.length_cons]; push_cast; ring

/-- In a connected graph, `E_u[τ_v] ≤ dist(u, v) · 2 |E|`. -/
theorem hittingTime_randomWalk_le_dist_mul (hG : G.Connected) (u v : V) :
    hittingTime (randomWalk G) v u ≤ G.dist u v * (2 * #G.edgeFinset) := by
  obtain ⟨p, hp⟩ := (hG u v).exists_walk_length_eq_dist
  simpa [hp] using hittingTime_randomWalk_le_length_mul hG p

/-! ### Degree-stationary distribution and lazy spectral mixing -/

omit [DecidableEq V] in
private theorem two_mul_card_edgeFinset_pos (hG : G ≠ ⊥) : 0 < 2 * #G.edgeFinset := by
  obtain ⟨u, v, huv⟩ : ∃ u v, G.Adj u v := by
    by_contra! hall; exact hG (SimpleGraph.ext (by ext u v; simp [hall u v]))
  rw [← G.sum_degrees_eq_twice_card_edges]
  exact sum_pos' (fun _ _ => Nat.zero_le _) ⟨u, mem_univ u, huv.degree_pos_left⟩

omit [DecidableEq V] in
/-- The **degree-proportional stationary distribution** `π(v) = deg(v) / (2 |E|)` of the simple
random walk on a finite graph `G ≠ ⊥` ([LevinPeres2017], Section 1.5, `(1.20)`). -/
noncomputable def degreeStationary (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G ≠ ⊥) :
    PMF V :=
  PMF.ofFintype (fun v => (G.degree v : ℝ≥0∞) / (2 * #G.edgeFinset)) (by
    have hpos := two_mul_card_edgeFinset_pos hG
    have h0 : ((2 * #G.edgeFinset : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hpos.ne'
    have htop : ((2 * #G.edgeFinset : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    simp_rw [div_eq_mul_inv]
    rw [← sum_mul, ← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using ENNReal.mul_inv_cancel h0 htop)

omit [DecidableEq V] in
theorem degreeStationary_apply (hG : G ≠ ⊥) (v : V) :
    degreeStationary G hG v = (G.degree v : ℝ≥0∞) / (2 * #G.edgeFinset) := by
  rw [degreeStationary, PMF.ofFintype_apply]

omit [DecidableEq V] in
/-- The simple random walk on `G ≠ ⊥` satisfies detailed balance with respect to
`degreeStationary G hG` ([LevinPeres2017], Section 1.5). -/
theorem isReversible_randomWalk (hG : G ≠ ⊥) :
    (randomWalk G).IsReversible (degreeStationary G hG) := by
  intro x y
  rcases eq_or_ne x y with rfl | hxy
  · rfl
  rw [degreeStationary_apply, degreeStationary_apply]
  by_cases hadj : G.Adj x y
  · have hx0 : (G.degree x : ℝ≥0∞) ≠ 0 := by exact_mod_cast hadj.degree_pos_left.ne'
    have hy0 : (G.degree y : ℝ≥0∞) ≠ 0 := by exact_mod_cast hadj.degree_pos_right.ne'
    rw [randomWalk_apply_of_adj hadj, randomWalk_apply_of_adj hadj.symm,
      div_eq_mul_inv, div_eq_mul_inv, mul_right_comm _ _ (G.degree x : ℝ≥0∞)⁻¹,
      ENNReal.mul_inv_cancel hx0 (ENNReal.natCast_ne_top _),
      mul_right_comm _ _ (G.degree y : ℝ≥0∞)⁻¹,
      ENNReal.mul_inv_cancel hy0 (ENNReal.natCast_ne_top _)]
  · have hside {a b : V} (hnadj : ¬ G.Adj a b) :
        (G.degree a : ℝ≥0∞) / (2 * #G.edgeFinset) * randomWalk G a b = 0 := by
      rcases (G.degree a).eq_zero_or_pos with ha0 | hapos
      · simp [ha0]
      · rw [randomWalk_apply_of_not_adj hapos hnadj, mul_zero]
    rw [hside hadj, hside fun h => hadj h.symm]

omit [DecidableEq V] in
/-- `degreeStationary G hG` is stationary for `randomWalk G`. -/
theorem isStationary_randomWalk (hG : G ≠ ⊥) :
    (randomWalk G).IsStationary (degreeStationary G hG) :=
  (isReversible_randomWalk hG).isStationary

omit [DecidableEq V] in
private theorem inv_two_mul_edges_le_degreeStationary [Nontrivial V] (hconn : G.Connected)
    (hG : G ≠ ⊥) (v : V) :
    (2 * (#G.edgeFinset : ℝ))⁻¹ ≤ (degreeStationary G hG v).toReal := by
  have hdeg : 1 ≤ G.degree v := by
    obtain ⟨w, hvw⟩ := exists_ne v
    obtain ⟨p⟩ := hconn v w
    cases p with
    | nil => exact absurd rfl hvw.symm
    | @cons _ u _ huv _ => exact huv.degree_pos_left
  have hpos : (0 : ℝ) < 2 * #G.edgeFinset := by
    exact_mod_cast two_mul_card_edgeFinset_pos hG
  rw [degreeStationary_apply, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_natCast, inv_eq_one_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hdeg) hpos.le

omit [DecidableEq V] in
private theorem degreeStationary_ne_zero [Nontrivial V] (hconn : G.Connected) (hG : G ≠ ⊥)
    (v : V) : degreeStationary G hG v ≠ 0 := fun hv0 => by
  have hpos : (0 : ℝ) < 2 * #G.edgeFinset := by exact_mod_cast two_mul_card_edgeFinset_pos hG
  linarith [inv_two_mul_edges_le_degreeStationary hconn hG v, inv_pos.mpr hpos,
    show (degreeStationary G hG v).toReal = 0 by simp [hv0]]

omit [DecidableEq V] in
/-- **Lazy random-walk total-variation contraction on a connected nontrivial graph**:
`d(t) ≤ (1 / 2) √(2 |E| - 1) · (1 - γ / 2)^t`. -/
theorem distToStationary_lazy_randomWalk_le [Nontrivial V] (hconn : G.Connected)
    (hG : G ≠ ⊥) (t : ℕ) :
    ((randomWalk G).lazy).distToStationary (degreeStationary G hG) t ≤
      (1 / 2) * Real.sqrt (2 * (#G.edgeFinset : ℝ) - 1) *
        (1 - (randomWalk G).spectralGap (degreeStationary G hG) / 2) ^ t := by
  have hpos : (0 : ℝ) < 2 * #G.edgeFinset := by exact_mod_cast two_mul_card_edgeFinset_pos hG
  have hedg : (#G.edgeFinset : ℝ) ≠ 0 := by linarith
  have hrev := isReversible_randomWalk hG
  have hd := hrev.lazy.distToStationary_le_of_le_toReal (inv_pos.mpr hpos)
    (inv_two_mul_edges_le_degreeStationary hconn hG) t
  rw [hrev.spectralContraction_lazy (degreeStationary_ne_zero hconn hG)] at hd
  exact hd.trans_eq (by
    rw [show (1 - (2 * (#G.edgeFinset : ℝ))⁻¹) / (2 * (#G.edgeFinset : ℝ))⁻¹ =
      2 * (#G.edgeFinset : ℝ) - 1 by field_simp [hedg]])

omit [DecidableEq V] in
/-- **Lazy random-walk mixing-time bound on a connected nontrivial graph**:
`t_mix(ε) ≤ ⌈2 γ⁻¹ ((1 / 2) log(2 |E|) + log(1 / (2 ε)))⌉₊`. -/
theorem mixingTime_lazy_randomWalk_le [Nontrivial V] (hconn : G.Connected) (hG : G ≠ ⊥)
    (hgap : 0 < (randomWalk G).spectralGap (degreeStationary G hG))
    {ε : ℝ} (hε : 0 < ε) :
    ((randomWalk G).lazy).mixingTime (degreeStationary G hG) ε ≤
      (⌈2 * ((randomWalk G).spectralGap (degreeStationary G hG))⁻¹ *
        ((1 / 2) * Real.log (2 * #G.edgeFinset) + Real.log (1 / (2 * ε)))⌉₊ : ℕ) := by
  have hpos : (0 : ℝ) < 2 * #G.edgeFinset := by exact_mod_cast two_mul_card_edgeFinset_pos hG
  have hπ := degreeStationary_ne_zero hconn hG
  have hrev := isReversible_randomWalk hG
  refine (hrev.lazy.mixingTime_le_of_absSpectralGap_pos (inv_pos.mpr hpos)
    (inv_two_mul_edges_le_degreeStationary hconn hG)
    (by rw [hrev.absSpectralGap_lazy hπ]; linarith) hε).trans_eq ?_
  congr 2
  rw [hrev.absSpectralGap_lazy hπ, div_inv_eq_mul, one_mul, inv_div]
  ring

end Cslib.Probability.MarkovChain
