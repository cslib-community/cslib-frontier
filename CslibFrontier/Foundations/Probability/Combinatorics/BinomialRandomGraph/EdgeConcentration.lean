/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Combinatorics/BinomialRandomGraph/`)

public import CslibFrontier.Foundations.MeasureTheory.Constructions.SimpleGraph
public import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Set.Card
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.Data.Nat.Choose.Real
import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.EdgePattern
import CslibFrontier.Probability.Chernoff
import CslibFrontier.Probability.PMF.Coin
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Sym.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Edge concentration and non-neighborhood bounds in binomial random graphs

In Mathlib's binomial random graph `G(V, p)` (`SimpleGraph.binomialRandom V p`), the edges on any
finite set `S : Finset (Sym2 V)` of non-diagonal pairs are mutually independent `Bernoulli(p)`
trials (`SimpleGraph.binomialRandom_real_edgePattern_of_injective`). Transporting the
multiplicative Chernoff bounds of `Cslib.Probability.PMF` along this exact product law yields:

* **Edge-count Chernoff bounds** for arbitrary finite sets `S` of non-diagonal pairs
  (`SimpleGraph.binomialRandom_real_edgeCount_ge_one_add_mul`,
  `SimpleGraph.binomialRandom_real_edgeCount_ge_one_add_mul_of_le_one`,
  `SimpleGraph.binomialRandom_real_edgeCount_le_one_sub_mul`,
  `SimpleGraph.binomialRandom_real_edgeCount_abs_sub_ge_mul`), together with direct corollaries
  for bipartite edge counts between disjoint vertex sets and single-vertex degrees;
* **Uniform vertex-to-set degree concentration**
  (`SimpleGraph.binomialRandom_real_exists_many_badDegree_le`): a finite-`n` union bound showing
  that simultaneously over all vertex subsets `A` of size at least `a₀`, few vertices can have
  `|N(u) ∩ A|` deviate from `|A| p` by more than `η |A| p`;
* **Bollobás's non-neighborhood bound** (Bollobás 2001, Theorem 2.15; [Suri2007], Theorem 29.18,
  p. 731): for `δ, C > 0` with `3 log n ≤ δ p n` and `3 log (e / δ) ≤ C`, every vertex subset `U`
  of size at least `u` (with `C ≤ u p`, in particular `u = ⌈C / p⌉`) leaves at most `δ n`
  outside vertices with no neighbor in `U`, with failure probability at most `exp (-C δ n / 3)`
  (`SimpleGraph.binomialRandom_real_exists_large_nonNeighborhood_le`), and tending to `1` as
  `C δ n → ∞` (`SimpleGraph.tendsto_binomialRandom_real_forall_nonNeighborhood_le`).

## Main results

* `SimpleGraph.binomialRandom_real_edgeCount_ge_one_add_mul`,
  `SimpleGraph.binomialRandom_real_edgeCount_ge_one_add_mul_of_le_one`,
  `SimpleGraph.binomialRandom_real_edgeCount_le_one_sub_mul`,
  `SimpleGraph.binomialRandom_real_edgeCount_abs_sub_ge_mul`: multiplicative Chernoff bounds on
  the number of present edges in a finite set of non-diagonal pairs.
* `SimpleGraph.binomialRandom_real_bipartiteEdgeCount_ge_one_add_mul_of_le_one`,
  `SimpleGraph.binomialRandom_real_bipartiteEdgeCount_le_one_sub_mul`,
  `SimpleGraph.binomialRandom_real_degree_ge_one_add_mul_of_le_one`: Chernoff bounds for
  bipartite edge counts and vertex degrees.
* `SimpleGraph.binomialRandom_real_exists_many_badDegree_le`: uniform bound on vertices whose
  degree into a large set deviates from its expectation.
* `SimpleGraph.binomialRandom_real_exists_large_nonNeighborhood_le`,
  `SimpleGraph.tendsto_binomialRandom_real_forall_nonNeighborhood_le`: Bollobás Theorem 2.15 /
  [Suri2007], Theorem 29.18.

## References

* [S. Suri, *Computational Evolutionary Game Theory*, Section 29.4.1, Theorem 29.18, p. 731]
  [Suri2007] (citing B. Bollobás, *Random Graphs*, 2001, Theorem 2.15)
* [M. Mitzenmacher, E. Upfal, *Probability and Computing*, Section 4.2][MitzenmacherUpfal2017]
-/

public section

open MeasureTheory ProbabilityTheory unitInterval Finset Filter
open scoped Finset Topology

namespace SimpleGraph

variable {V : Type*}

/-! ### Bridging `G(V, p)` edge indicators to `Cslib.Probability.PMF.pi` -/

/-- Classical edge-presence indicator on a finite set `S` of vertex pairs. -/
private noncomputable def edgeIndicator (S : Finset (Sym2 V)) (G : SimpleGraph V)
    (e : {e : Sym2 V // e ∈ S}) : Bool :=
  open Classical in decide (e.1 ∈ G.edgeSet)

private theorem edgeIndicator_eq_true_iff (S : Finset (Sym2 V)) (G : SimpleGraph V)
    (e : {e : Sym2 V // e ∈ S}) :
    edgeIndicator S G e = true ↔ e.1 ∈ G.edgeSet := by
  classical
  simp [edgeIndicator]

/-- The real probability of any event depending only on the edges in a finite set `S` of
non-diagonal pairs equals the corresponding `Cslib.Probability.PMF.pi` event probability. -/
private theorem binomialRandom_real_edgeEvent_eq_pi [Finite V] (p : I) (S : Finset (Sym2 V))
    (hS : ∀ e ∈ S, ¬e.IsDiag) (P : ({e : Sym2 V // e ∈ S} → Bool) → Prop) :
    G(V, p).real {G | P (edgeIndicator S G)} =
      ((Cslib.Probability.PMF.pi (fun _ : {e : Sym2 V // e ∈ S} => Cslib.Probability.PMF.coin p))
        |>.toOuterMeasure {b | P b}).toReal := by
  classical
  let ι := {e : Sym2 V // e ∈ S}
  let μ := Cslib.Probability.PMF.pi (fun _ : ι => Cslib.Probability.PMF.coin p)
  let pat : (ι → Bool) → Set (SimpleGraph V) :=
    fun b => {G | ∀ e : ι, (e.1 ∈ G.edgeSet ↔ b e = true)}
  let A : Finset (ι → Bool) := univ.filter P
  have hpat (b : ι → Bool) : G(V, p).real (pat b) = (μ b).toReal := by
    rw [binomialRandom_real_edgePattern_of_injective p Subtype.val_injective
      (fun e => hS e.1 e.2) b]
    simp only [μ, Cslib.Probability.PMF.pi_apply, ENNReal.toReal_prod]
    exact Finset.prod_congr rfl fun e _ => (Cslib.Probability.PMF.coin_apply_toReal p (b e)).symm
  have hset : {G : SimpleGraph V | P (edgeIndicator S G)} = ⋃ b ∈ A, pat b := by
    ext G
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_filter, mem_univ, true_and, pat, A]
    constructor
    · intro hG
      exact ⟨edgeIndicator S G, hG, fun e => (edgeIndicator_eq_true_iff S G e).symm⟩
    · rintro ⟨b, hb, hGb⟩
      have heq : edgeIndicator S G = b := by
        funext e
        rw [Bool.eq_iff_iff, edgeIndicator_eq_true_iff]
        exact hGb e
      rwa [heq]
  have hdisj : (A : Set (ι → Bool)).PairwiseDisjoint pat := by
    intro b _ b' _ hbb'
    refine Set.disjoint_left.2 fun G hGb hGb' => hbb' (funext fun e => ?_)
    rw [Bool.eq_iff_iff, ← hGb e, hGb' e]
  rw [hset, measureReal_biUnion_finset hdisj fun b _ => MeasurableSet.of_discrete]
  simp_rw [hpat]
  have houter : μ.toOuterMeasure {b | P b} = ∑ b ∈ A, μ b := by
    rw [PMF.toOuterMeasure_apply, tsum_fintype]
    dsimp only [A]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : P b <;> simp [hb]
  rw [houter, ENNReal.toReal_sum fun b _ => PMF.apply_ne_top μ b]

/-- Express the edge count `((S : Set (Sym2 V)) ∩ G.edgeSet).ncard` as a sum of `0`/`1` edge
indicators over `S`. -/
private theorem ncard_inter_edgeSet_eq_sum (S : Finset (Sym2 V)) (G : SimpleGraph V) :
    (((S : Set (Sym2 V)) ∩ G.edgeSet).ncard : ℝ) =
      ∑ e : {e : Sym2 V // e ∈ S}, if edgeIndicator S G e then (1 : ℝ) else 0 := by
  classical
  have hcoe : ((S : Set (Sym2 V)) ∩ G.edgeSet) =
      ((S.filter (· ∈ G.edgeSet) : Finset (Sym2 V)) : Set (Sym2 V)) := by
    ext e
    simp
  rw [hcoe, Set.ncard_coe_finset, Finset.card_filter, Nat.cast_sum, ← Finset.sum_attach S]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases he : e.1 ∈ G.edgeSet
  · simp [he, (edgeIndicator_eq_true_iff S G e).2 he]
  · have hne : edgeIndicator S G e ≠ true := fun h => he ((edgeIndicator_eq_true_iff S G e).1 h)
    simp [he, hne]

private def boolScore {ι : Type*} : ι → Bool → ℝ := fun _ b => if b then 1 else 0

private theorem boolScore_mem_Icc {ι : Type*} (p : I) (i : ι) (a : Bool)
    (_ : a ∈ (Cslib.Probability.PMF.coin p).support) : boolScore i a ∈ Set.Icc 0 1 := by
  cases a <;> simp [boolScore]

private theorem sum_coin_boolScore (p : I) (S : Finset (Sym2 V)) :
    ∑ i : {e : Sym2 V // e ∈ S}, ∑ a : Bool,
        (Cslib.Probability.PMF.coin p a).toReal * boolScore i a = (#S : ℝ) * (p : ℝ) := by
  simp [boolScore, Cslib.Probability.PMF.coin_apply_toReal]

private theorem binomialRandom_real_edgeCount_eq_pi [Finite V] (p : I) (S : Finset (Sym2 V))
    (hS : ∀ e ∈ S, ¬e.IsDiag) (P : ℝ → Prop) :
    G(V, p).real {G | P (((S : Set (Sym2 V)) ∩ G.edgeSet).ncard : ℝ)} =
      ((Cslib.Probability.PMF.pi fun _ : {e : Sym2 V // e ∈ S} =>
          Cslib.Probability.PMF.coin p).toOuterMeasure
        {b | P (∑ e : {e : Sym2 V // e ∈ S}, boolScore e (b e))}).toReal := by
  have heq : {G : SimpleGraph V | P (((S : Set (Sym2 V)) ∩ G.edgeSet).ncard : ℝ)} =
      {G | P (∑ e : {e : Sym2 V // e ∈ S}, boolScore e (edgeIndicator S G e))} := by
    ext G
    simp only [Set.mem_ofPred_eq, ncard_inter_edgeSet_eq_sum, boolScore]
  rw [heq]
  exact binomialRandom_real_edgeEvent_eq_pi p S hS
    (fun b => P (∑ e : {e : Sym2 V // e ∈ S}, boolScore e (b e)))

private theorem ncard_inter_neighborSet_eq_card_filter (B : Finset V) (G : SimpleGraph V) (u : V)
    [DecidablePred (G.Adj u)] :
    ((B : Set V) ∩ G.neighborSet u).ncard = #(B.filter (G.Adj u)) := by
  have hB : ((B : Set V) ∩ G.neighborSet u) = ((B.filter (G.Adj u) : Finset V) : Set V) := by
    ext v; simp [SimpleGraph.mem_neighborSet]
  rw [hB, Set.ncard_coe_finset]

/-! ### Multiplicative Chernoff bounds for edge counts -/

/-- **Multiplicative Chernoff upper tail for edge counts in `G(V, p)`**
([MitzenmacherUpfal2017], Section 4.2): for any finite set `S` of non-diagonal pairs whose
expected edge count `#S * p` is at most `μ`, and any `δ ≥ 0`, the probability that `G(V, p)` has
at least `(1 + δ) * μ` edges in `S` is at most `exp (-(δ ^ 2 * μ / (2 + δ)))`. -/
theorem binomialRandom_real_edgeCount_ge_one_add_mul [Finite V] (p : I) (S : Finset (Sym2 V))
    (hS : ∀ e ∈ S, ¬e.IsDiag) {μ δ : ℝ} (hμ : (#S : ℝ) * (p : ℝ) ≤ μ) (hδ : 0 ≤ δ) :
    G(V, p).real {G | (1 + δ) * μ ≤ (((S : Set (Sym2 V)) ∩ G.edgeSet).ncard : ℝ)} ≤
      Real.exp (-(δ ^ 2 * μ / (2 + δ))) := by
  rw [binomialRandom_real_edgeCount_eq_pi p S hS (fun x => (1 + δ) * μ ≤ x)]
  exact Cslib.Probability.PMF.pi_sum_ge_one_add_mul _ boolScore (boolScore_mem_Icc p)
    (by rw [sum_coin_boolScore p S]; exact hμ) hδ

/-- **Multiplicative Chernoff upper tail for `δ ≤ 1`** ([MitzenmacherUpfal2017], Section 4.2):
for `#S * p ≤ μ` and `0 ≤ δ ≤ 1`, `G(V, p)` has at least `(1 + δ) * μ` edges in `S` with
probability at most `exp (-(δ ^ 2 * μ / 3))`. -/
theorem binomialRandom_real_edgeCount_ge_one_add_mul_of_le_one [Finite V] (p : I)
    (S : Finset (Sym2 V)) (hS : ∀ e ∈ S, ¬e.IsDiag) {μ δ : ℝ} (hμ : (#S : ℝ) * (p : ℝ) ≤ μ)
    (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    G(V, p).real {G | (1 + δ) * μ ≤ (((S : Set (Sym2 V)) ∩ G.edgeSet).ncard : ℝ)} ≤
      Real.exp (-(δ ^ 2 * μ / 3)) := by
  rw [binomialRandom_real_edgeCount_eq_pi p S hS (fun x => (1 + δ) * μ ≤ x)]
  exact Cslib.Probability.PMF.pi_sum_ge_one_add_mul_of_le_one _ boolScore (boolScore_mem_Icc p)
    (by rw [sum_coin_boolScore p S]; exact hμ) hδ hδ₁

/-- **Multiplicative Chernoff lower tail for edge counts in `G(V, p)`**
([MitzenmacherUpfal2017], Section 4.2): for any finite set `S` of non-diagonal pairs with
`μ ≤ #S * p` and any `δ ≥ 0`, the probability that `G(V, p)` has at most `(1 - δ) * μ` edges in
`S` is at most `exp (-(δ ^ 2 * μ / 2))`. -/
theorem binomialRandom_real_edgeCount_le_one_sub_mul [Finite V] (p : I) (S : Finset (Sym2 V))
    (hS : ∀ e ∈ S, ¬e.IsDiag) {μ δ : ℝ} (hμ : μ ≤ (#S : ℝ) * (p : ℝ)) (hδ : 0 ≤ δ) :
    G(V, p).real {G | (((S : Set (Sym2 V)) ∩ G.edgeSet).ncard : ℝ) ≤ (1 - δ) * μ} ≤
      Real.exp (-(δ ^ 2 * μ / 2)) := by
  rw [binomialRandom_real_edgeCount_eq_pi p S hS (fun x => x ≤ (1 - δ) * μ)]
  exact Cslib.Probability.PMF.pi_sum_le_one_sub_mul _ boolScore (boolScore_mem_Icc p)
    (by rw [sum_coin_boolScore p S]; exact hμ) hδ

/-- **Two-sided multiplicative Chernoff bound for edge counts in `G(V, p)`**: for any finite set
`S` of non-diagonal pairs and `0 ≤ δ ≤ 1`, the edge count deviates from `#S * p` by at least
`δ * (#S * p)` with probability at most `2 * exp (-(δ ^ 2 * (#S * p) / 3))`. -/
theorem binomialRandom_real_edgeCount_abs_sub_ge_mul [Finite V] (p : I) (S : Finset (Sym2 V))
    (hS : ∀ e ∈ S, ¬e.IsDiag) {δ : ℝ} (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    G(V, p).real {G | δ * ((#S : ℝ) * (p : ℝ)) ≤
      |(((S : Set (Sym2 V)) ∩ G.edgeSet).ncard : ℝ) - (#S : ℝ) * (p : ℝ)|} ≤
      2 * Real.exp (-(δ ^ 2 * ((#S : ℝ) * (p : ℝ)) / 3)) := by
  rw [binomialRandom_real_edgeCount_eq_pi p S hS
    (fun x => δ * ((#S : ℝ) * (p : ℝ)) ≤ |x - (#S : ℝ) * (p : ℝ)|)]
  have h := Cslib.Probability.PMF.pi_sum_abs_sub_mean_ge_mul
    (fun _ : {e : Sym2 V // e ∈ S} => Cslib.Probability.PMF.coin p) boolScore
    (boolScore_mem_Icc p) hδ hδ₁
  simpa only [sum_coin_boolScore p S] using h

/-! ### Bipartite edge counts, internal edges, and vertex degrees -/

/-- The unordered pairs with one endpoint in `A` and the other in `B`. -/
private def bipartitePairs [DecidableEq V] (A B : Finset V) : Finset (Sym2 V) :=
  (A ×ˢ B).image Sym2.mk.uncurry

private theorem not_isDiag_of_mem_bipartitePairs [DecidableEq V] {A B : Finset V}
    (hAB : Disjoint A B) {e : Sym2 V} (he : e ∈ bipartitePairs A B) : ¬e.IsDiag := by
  simp only [bipartitePairs, Finset.mem_image, Finset.mem_product] at he
  rcases he with ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
  intro hdiag
  exact Finset.disjoint_left.1 hAB hu (Sym2.mk_isDiag_iff.1 hdiag ▸ hv)

private theorem injOn_bipartitePairs {A B : Finset V} (hAB : Disjoint A B) :
    Set.InjOn Sym2.mk.uncurry (↑(A ×ˢ B) : Set (V × V)) := by
  rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' h
  simp only [Finset.mem_coe, Finset.mem_product] at huv huv'
  rcases Sym2.eq_iff.1 (show s(u, v) = s(u', v') from h) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd huv'.2 (Finset.disjoint_left.1 hAB huv.1)

private theorem card_bipartitePairs [DecidableEq V] {A B : Finset V} (hAB : Disjoint A B) :
    #(bipartitePairs A B) = #A * #B := by
  rw [bipartitePairs, Finset.card_image_of_injOn (injOn_bipartitePairs hAB), Finset.card_product]

private theorem ncard_bipartitePairs_inter_edgeSet [DecidableEq V] {A B : Finset V}
    (hAB : Disjoint A B) (G : SimpleGraph V) :
    ((bipartitePairs A B : Set (Sym2 V)) ∩ G.edgeSet).ncard =
      ∑ u ∈ A, ((B : Set V) ∩ G.neighborSet u).ncard := by
  classical
  have h1 : ((bipartitePairs A B : Set (Sym2 V)) ∩ G.edgeSet) =
      (((bipartitePairs A B).filter (· ∈ G.edgeSet) : Finset (Sym2 V)) : Set (Sym2 V)) := by
    ext e; simp
  have h2 : (bipartitePairs A B).filter (· ∈ G.edgeSet) =
      ((A ×ˢ B).filter fun q => G.Adj q.1 q.2).image Sym2.mk.uncurry := by
    ext e
    simp only [bipartitePairs, Finset.mem_filter, Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨u, v⟩, huv, rfl⟩, hadj⟩
      exact ⟨(u, v), ⟨huv, hadj⟩, rfl⟩
    · rintro ⟨⟨u, v⟩, ⟨huv, hadj⟩, rfl⟩
      exact ⟨⟨(u, v), huv, rfl⟩, hadj⟩
  have hinj : Set.InjOn Sym2.mk.uncurry
      (↑((A ×ˢ B).filter fun q => G.Adj q.1 q.2) : Set (V × V)) :=
    (injOn_bipartitePairs hAB).mono (by intro q hq; exact (Finset.mem_filter.1 hq).1)
  rw [h1, Set.ncard_coe_finset, h2, Finset.card_image_of_injOn hinj]
  have hprod : #((A ×ˢ B).filter fun q => G.Adj q.1 q.2) =
      ∑ u ∈ A, #(B.filter (G.Adj u)) := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.card_filter]
  rw [hprod]
  exact Finset.sum_congr rfl fun u _ => (ncard_inter_neighborSet_eq_card_filter B G u).symm

/-- **Multiplicative Chernoff upper tail for bipartite edge counts**: for disjoint vertex sets
`A, B` with `#A * #B * p ≤ μ` and `0 ≤ δ ≤ 1`, the number of edges between `A` and `B` is at
least `(1 + δ) * μ` with probability at most `exp (-(δ ^ 2 * μ / 3))`. -/
theorem binomialRandom_real_bipartiteEdgeCount_ge_one_add_mul_of_le_one [Finite V] (p : I)
    {A B : Finset V} (hAB : Disjoint A B) {μ δ : ℝ} (hμ : (#A : ℝ) * (#B : ℝ) * (p : ℝ) ≤ μ)
    (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    G(V, p).real {G | (1 + δ) * μ ≤ ∑ u ∈ A, (((B : Set V) ∩ G.neighborSet u).ncard : ℝ)} ≤
      Real.exp (-(δ ^ 2 * μ / 3)) := by
  classical
  have hμ' : (#(bipartitePairs A B) : ℝ) * (p : ℝ) ≤ μ := by
    rw [card_bipartitePairs hAB, Nat.cast_mul]
    exact hμ
  have h := binomialRandom_real_edgeCount_ge_one_add_mul_of_le_one p (bipartitePairs A B)
    (fun _ => not_isDiag_of_mem_bipartitePairs hAB) hμ' hδ hδ₁
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext G
  simp only [Set.mem_ofPred_eq, ncard_bipartitePairs_inter_edgeSet hAB, Nat.cast_sum]

/-- **Multiplicative Chernoff lower tail for bipartite edge counts**: for disjoint vertex sets
`A, B` with `μ ≤ #A * #B * p` and `0 ≤ δ`, the number of edges between `A` and `B` is at most
`(1 - δ) * μ` with probability at most `exp (-(δ ^ 2 * μ / 2))`. -/
theorem binomialRandom_real_bipartiteEdgeCount_le_one_sub_mul [Finite V] (p : I)
    {A B : Finset V} (hAB : Disjoint A B) {μ δ : ℝ} (hμ : μ ≤ (#A : ℝ) * (#B : ℝ) * (p : ℝ))
    (hδ : 0 ≤ δ) :
    G(V, p).real {G | ∑ u ∈ A, (((B : Set V) ∩ G.neighborSet u).ncard : ℝ) ≤ (1 - δ) * μ} ≤
      Real.exp (-(δ ^ 2 * μ / 2)) := by
  classical
  have hμ' : μ ≤ (#(bipartitePairs A B) : ℝ) * (p : ℝ) := by
    rw [card_bipartitePairs hAB, Nat.cast_mul]
    exact hμ
  have h := binomialRandom_real_edgeCount_le_one_sub_mul p (bipartitePairs A B)
    (fun _ => not_isDiag_of_mem_bipartitePairs hAB) hμ' hδ
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext G
  simp only [Set.mem_ofPred_eq, ncard_bipartitePairs_inter_edgeSet hAB, Nat.cast_sum]

/-- **Multiplicative Chernoff upper tail for vertex degrees**: for any vertex `u` with
`(Fintype.card V - 1) * p ≤ μ` and `0 ≤ δ ≤ 1`, the degree of `u` in `G(V, p)` is at least
`(1 + δ) * μ` with probability at most `exp (-(δ ^ 2 * μ / 3))`. -/
theorem binomialRandom_real_degree_ge_one_add_mul_of_le_one [Fintype V] (p : I) (u : V)
    {μ δ : ℝ} (hμ : ((Fintype.card V - 1 : ℕ) : ℝ) * (p : ℝ) ≤ μ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    G(V, p).real {G | (1 + δ) * μ ≤ ((G.neighborSet u).ncard : ℝ)} ≤
      Real.exp (-(δ ^ 2 * μ / 3)) := by
  classical
  have hdisj : Disjoint ({u} : Finset V) (univ.erase u) := by simp
  have hcard : #(univ.erase u) = Fintype.card V - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ u), Finset.card_univ]
  have h := binomialRandom_real_bipartiteEdgeCount_ge_one_add_mul_of_le_one p hdisj
    (by simpa [hcard] using hμ) hδ hδ₁
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext G
  simp only [Set.mem_ofPred_eq, Finset.sum_singleton]
  have hset : ((univ.erase u : Finset V) : Set V) ∩ G.neighborSet u = G.neighborSet u := by
    ext v
    simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_erase, mem_univ, and_true,
      SimpleGraph.mem_neighborSet, and_iff_right_iff_imp]
    intro hadj
    exact hadj.ne'
  rw [hset]

/-! ### Uniform vertex-to-set degree concentration -/

/-- Non-diagonal unordered pairs inside a vertex subset `K`. -/
private def internalPairs [DecidableEq V] (K : Finset V) : Finset (Sym2 V) :=
  K.offDiag.image Sym2.mk.uncurry

private theorem not_isDiag_of_mem_internalPairs [DecidableEq V] {K : Finset V} {e : Sym2 V}
    (he : e ∈ internalPairs K) : ¬e.IsDiag := by
  simp only [internalPairs, Finset.mem_image, Finset.mem_offDiag] at he
  rcases he with ⟨⟨u, v⟩, ⟨-, -, hne⟩, rfl⟩
  simpa using hne

private theorem card_internalPairs_le [DecidableEq V] (K : Finset V) :
    2 * #(internalPairs K) ≤ #K * #K := by
  rw [internalPairs, Sym2.card_image_offDiag, Nat.choose_two_right]
  exact (Nat.mul_div_le _ 2).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ 1))

private theorem sum_ncard_inter_self_eq_two_mul [DecidableEq V] (K : Finset V) (G : SimpleGraph V) :
    ∑ u ∈ K, ((K : Set V) ∩ G.neighborSet u).ncard =
      2 * ((internalPairs K : Set (Sym2 V)) ∩ G.edgeSet).ncard := by
  classical
  let E : Finset (V × V) := K.offDiag.filter fun q => G.Adj q.1 q.2
  have hE_lhs : ∑ u ∈ K, ((K : Set V) ∩ G.neighborSet u).ncard = #E := by
    have hsum : ∑ u ∈ K, ((K : Set V) ∩ G.neighborSet u).ncard =
        ∑ u ∈ K, #(K.filter (G.Adj u)) :=
      Finset.sum_congr rfl fun u _ => ncard_inter_neighborSet_eq_card_filter K G u
    rw [hsum]
    have hE_eq : E = (K ×ˢ K).filter fun q => G.Adj q.1 q.2 := by
      ext ⟨u, v⟩
      simp only [E, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product]
      exact ⟨fun ⟨⟨hu, hv, _⟩, hadj⟩ => ⟨⟨hu, hv⟩, hadj⟩,
        fun ⟨⟨hu, hv⟩, hadj⟩ => ⟨⟨hu, hv, hadj.ne⟩, hadj⟩⟩
    rw [hE_eq, Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl fun u _ => Finset.card_filter _ _
  have hE_img : E.image Sym2.mk.uncurry = (internalPairs K).filter (· ∈ G.edgeSet) := by
    ext e
    simp only [E, internalPairs, Finset.mem_image, Finset.mem_filter, Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨u, v⟩, ⟨huv, hadj⟩, rfl⟩
      exact ⟨⟨(u, v), huv, rfl⟩, hadj⟩
    · rintro ⟨⟨⟨u, v⟩, huv, rfl⟩, hadj⟩
      exact ⟨(u, v), ⟨huv, hadj⟩, rfl⟩
  have hfib : ∀ e ∈ E.image Sym2.mk.uncurry, #(E.filter fun q => Sym2.mk.uncurry q = e) = 2 := by
    intro e he
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.1 he
    have huv' := Finset.mem_filter.1 huv
    have hoff := Finset.mem_offDiag.1 huv'.1
    have hset :
        E.filter (fun q => Sym2.mk.uncurry q = Sym2.mk.uncurry (u, v)) = {(u, v), (v, u)} := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨_, hxy⟩
        exact Sym2.eq_iff.1 hxy
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨huv, rfl⟩
        · exact ⟨Finset.mem_filter.2
            ⟨Finset.mem_offDiag.2 ⟨hoff.2.1, hoff.1, hoff.2.2.symm⟩, huv'.2.symm⟩, Sym2.eq_swap⟩
    rw [hset, Finset.card_pair (fun h => hoff.2.2 (congrArg Prod.fst h))]
  have hcardE : #E = 2 * #(E.image Sym2.mk.uncurry) := by
    rw [Finset.card_eq_sum_card_image Sym2.mk.uncurry E, Finset.sum_congr rfl hfib,
      Finset.sum_const, smul_eq_mul, mul_comm]
  have hncard : ((internalPairs K : Set (Sym2 V)) ∩ G.edgeSet).ncard =
      #((internalPairs K).filter (· ∈ G.edgeSet)) := by
    have hcoe : ((internalPairs K : Set (Sym2 V)) ∩ G.edgeSet) =
        (((internalPairs K).filter (· ∈ G.edgeSet) : Finset (Sym2 V)) : Set (Sym2 V)) := by
      ext e; simp
    rw [hcoe, Set.ncard_coe_finset]
  rw [hE_lhs, hcardE, hE_img, hncard]

/-- Decompose `∑ u ∈ K, |N(u) ∩ A|` into bipartite edges `e(K, A \ K)` plus internal edges inside
`K`. -/
private theorem bipartite_le_sum_ncard_le_add_internal [DecidableEq V] (K A : Finset V)
    (G : SimpleGraph V) :
    (∑ u ∈ K, ((((A \ K : Finset V) : Set V) ∩ G.neighborSet u).ncard : ℝ)) ≤
        ∑ u ∈ K, (((A : Set V) ∩ G.neighborSet u).ncard : ℝ) ∧
      ∑ u ∈ K, (((A : Set V) ∩ G.neighborSet u).ncard : ℝ) ≤
        (∑ u ∈ K, ((((A \ K : Finset V) : Set V) ∩ G.neighborSet u).ncard : ℝ)) +
          2 * (((internalPairs K : Set (Sym2 V)) ∩ G.edgeSet).ncard : ℝ) := by
  have h1 : ∀ u ∈ K, (((A \ K : Finset V) : Set V) ∩ G.neighborSet u).ncard ≤
      ((A : Set V) ∩ G.neighborSet u).ncard := fun u _ =>
    Set.ncard_le_ncard (Set.inter_subset_inter_left _ (by exact_mod_cast Finset.sdiff_subset))
      (Set.toFinite _)
  have h2 : ∀ u ∈ K, ((A : Set V) ∩ G.neighborSet u).ncard ≤
      (((A \ K : Finset V) : Set V) ∩ G.neighborSet u).ncard +
        ((K : Set V) ∩ G.neighborSet u).ncard := by
    intro u _
    have hsub : ((A : Set V) ∩ G.neighborSet u) ⊆
        (((A \ K : Finset V) : Set V) ∩ G.neighborSet u) ∪ ((K : Set V) ∩ G.neighborSet u) := by
      intro v hv
      by_cases hvK : v ∈ K
      · exact Or.inr ⟨hvK, hv.2⟩
      · exact Or.inl ⟨Finset.mem_sdiff.2 ⟨hv.1, hvK⟩, hv.2⟩
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
  refine ⟨Finset.sum_le_sum fun u hu => Nat.cast_le.2 (h1 u hu), ?_⟩
  have hsum : ∑ u ∈ K, ((A : Set V) ∩ G.neighborSet u).ncard ≤
      ∑ u ∈ K, (((A \ K : Finset V) : Set V) ∩ G.neighborSet u).ncard +
        ∑ u ∈ K, ((K : Set V) ∩ G.neighborSet u).ncard := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum h2
  rw [sum_ncard_inter_self_eq_two_mul] at hsum
  exact_mod_cast hsum

/-- For fixed `K` and `A` (possibly overlapping) with `4 * #K ≤ η * #A` and `0 < η ≤ 1`, the sum
of degrees from `K` into `A` deviates from `#K * #A * p` by at least `η * #K * #A * p` with
probability at most `3 * exp (-(η ^ 2 * #K * #A * p / 24))`. -/
private theorem binomialRandom_real_sum_degreeInto_bad_le [Finite V] (p : I)
    (K A : Finset V) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hKA : 4 * (#K : ℝ) ≤ η * (#A : ℝ)) :
    G(V, p).real ({G | ∑ u ∈ K, (((A : Set V) ∩ G.neighborSet u).ncard : ℝ) ≤
        (1 - η) * ((#K : ℝ) * (#A : ℝ) * (p : ℝ))} ∪
      {G | (1 + η) * ((#K : ℝ) * (#A : ℝ) * (p : ℝ)) ≤
        ∑ u ∈ K, (((A : Set V) ∩ G.neighborSet u).ncard : ℝ)}) ≤
      3 * Real.exp (-(η ^ 2 * (#K : ℝ) * (#A : ℝ) * (p : ℝ) / 24)) := by
  classical
  have hp0 : (0 : ℝ) ≤ p := unitInterval.nonneg p
  have hdisj : Disjoint K (A \ K) := Finset.disjoint_sdiff
  have hcard_le : (#(A \ K) : ℝ) ≤ (#A : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  have hcard_ge : (1 - η / 4) * (#A : ℝ) ≤ (#(A \ K) : ℝ) := by
    have hnat : #A ≤ #(A \ K) + #K := by
      have := Finset.card_sdiff_add_card_inter A K
      have := Finset.card_le_card (Finset.inter_subset_right (s₁ := A) (s₂ := K))
      omega
    have hreal : (#A : ℝ) ≤ (#(A \ K) : ℝ) + (#K : ℝ) := by exact_mod_cast hnat
    linarith
  -- Lower tail via `e(K, A \ K)`.
  have hlow : G(V, p).real {G | ∑ u ∈ K, (((A : Set V) ∩ G.neighborSet u).ncard : ℝ) ≤
      (1 - η) * ((#K : ℝ) * (#A : ℝ) * (p : ℝ))} ≤
      Real.exp (-(η ^ 2 * (#K : ℝ) * (#A : ℝ) * (p : ℝ) / 24)) := by
    let μ₁ : ℝ := (#K : ℝ) * ((1 - η / 4) * (#A : ℝ)) * (p : ℝ)
    have hμ₁ : μ₁ ≤ (#K : ℝ) * (#(A \ K) : ℝ) * (p : ℝ) := by
      dsimp only [μ₁]
      gcongr
    have hsub : {G : SimpleGraph V | ∑ u ∈ K, (((A : Set V) ∩ G.neighborSet u).ncard : ℝ) ≤
        (1 - η) * ((#K : ℝ) * (#A : ℝ) * (p : ℝ))} ⊆
        {G | ∑ u ∈ K, ((((A \ K : Finset V) : Set V) ∩ G.neighborSet u).ncard : ℝ) ≤
          (1 - η / 2) * μ₁} := by
      intro G hG
      simp only [Set.mem_ofPred_eq] at hG ⊢
      have h1 := (bipartite_le_sum_ncard_le_add_internal K A G).1
      have h2 : (1 - η) * ((#K : ℝ) * (#A : ℝ) * (p : ℝ)) ≤ (1 - η / 2) * μ₁ := by
        dsimp only [μ₁]
        have hfac : 1 - η ≤ (1 - η / 2) * (1 - η / 4) := by nlinarith
        have hnonneg : 0 ≤ (#K : ℝ) * (#A : ℝ) * (p : ℝ) := by positivity
        nlinarith
      linarith
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
    refine (binomialRandom_real_bipartiteEdgeCount_le_one_sub_mul p hdisj hμ₁
      (δ := η / 2) (by linarith)).trans ?_
    rw [Real.exp_le_exp, neg_le_neg_iff]
    dsimp only [μ₁]
    have hnonneg : 0 ≤ η ^ 2 * (#K : ℝ) * (#A : ℝ) * (p : ℝ) := by positivity
    nlinarith
  -- Upper tail split between `e(K, A \ K)` and `2 * e(K)`.
  have hhigh : G(V, p).real {G | (1 + η) * ((#K : ℝ) * (#A : ℝ) * (p : ℝ)) ≤
      ∑ u ∈ K, (((A : Set V) ∩ G.neighborSet u).ncard : ℝ)} ≤
      2 * Real.exp (-(η ^ 2 * (#K : ℝ) * (#A : ℝ) * (p : ℝ) / 24)) := by
    let E₁ : Set (SimpleGraph V) :=
      {G | (1 + η / 2) * ((#K : ℝ) * (#A : ℝ) * (p : ℝ)) ≤
        ∑ u ∈ K, ((((A \ K : Finset V) : Set V) ∩ G.neighborSet u).ncard : ℝ)}
    let E₂ : Set (SimpleGraph V) :=
      {G | (1 + 1) * (η / 8 * ((#K : ℝ) * (#A : ℝ) * (p : ℝ))) ≤
        (((internalPairs K : Set (Sym2 V)) ∩ G.edgeSet).ncard : ℝ)}
    have hsub : {G : SimpleGraph V | (1 + η) * ((#K : ℝ) * (#A : ℝ) * (p : ℝ)) ≤
        ∑ u ∈ K, (((A : Set V) ∩ G.neighborSet u).ncard : ℝ)} ⊆ E₁ ∪ E₂ := by
      intro G hG
      simp only [Set.mem_ofPred_eq, Set.mem_union, E₁, E₂] at hG ⊢
      have h2 := (bipartite_le_sum_ncard_le_add_internal K A G).2
      by_contra! hboth
      linarith
    have hE₁ : G(V, p).real E₁ ≤ Real.exp (-(η ^ 2 * (#K : ℝ) * (#A : ℝ) * (p : ℝ) / 24)) := by
      have hμ₁ : (#K : ℝ) * (#(A \ K) : ℝ) * (p : ℝ) ≤ (#K : ℝ) * (#A : ℝ) * (p : ℝ) := by
        gcongr
      refine (binomialRandom_real_bipartiteEdgeCount_ge_one_add_mul_of_le_one p hdisj hμ₁
        (δ := η / 2) (by linarith) (by linarith)).trans ?_
      rw [Real.exp_le_exp, neg_le_neg_iff]
      have hnonneg : 0 ≤ η ^ 2 * (#K : ℝ) * (#A : ℝ) * (p : ℝ) := by positivity
      linarith
    have hE₂ : G(V, p).real E₂ ≤ Real.exp (-(η ^ 2 * (#K : ℝ) * (#A : ℝ) * (p : ℝ) / 24)) := by
      have hμ₂ : (#(internalPairs K) : ℝ) * (p : ℝ) ≤
          η / 8 * ((#K : ℝ) * (#A : ℝ) * (p : ℝ)) := by
        have hci : 2 * (#(internalPairs K) : ℝ) ≤ (#K : ℝ) * (#K : ℝ) := by
          exact_mod_cast card_internalPairs_le K
        have hkk : (#K : ℝ) * (#K : ℝ) ≤ η / 4 * ((#K : ℝ) * (#A : ℝ)) := by
          nlinarith [show (0 : ℝ) ≤ (#K : ℝ) by positivity]
        nlinarith
      refine (binomialRandom_real_edgeCount_ge_one_add_mul_of_le_one p (internalPairs K)
        (fun _ => not_isDiag_of_mem_internalPairs) hμ₂ (δ := 1) zero_le_one le_rfl).trans ?_
      rw [Real.exp_le_exp, neg_le_neg_iff]
      have hηsq : η ^ 2 ≤ η := by nlinarith
      have hnonneg : 0 ≤ (#K : ℝ) * (#A : ℝ) * (p : ℝ) := by positivity
      nlinarith
    have hunion :=
      (measureReal_mono hsub (measure_ne_top G(V, p) _)).trans (measureReal_union_le E₁ E₂)
    linarith
  exact (measureReal_union_le _ _).trans (by linarith)

/-- **Uniform vertex-to-set degree concentration in `G(V, p)`**: for `0 < η ≤ 1` and
`4 k ≤ η a₀`, the probability that there exists a vertex subset `A` of size at least `a₀` for
which at least `2 k` vertices have `|N(u) ∩ A|` deviating from `#A * p` by more than `η * #A * p`
is at most `3 * 4 ^ |V| * exp (-(η ^ 2 * k * a₀ * p / 24))`. -/
theorem binomialRandom_real_exists_many_badDegree_le [Fintype V] (p : I) {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) {a₀ k : ℕ} (hka : 4 * (k : ℝ) ≤ η * (a₀ : ℝ)) :
    G(V, p).real {G | ∃ A : Finset V, a₀ ≤ #A ∧
      2 * k ≤ ({u : V | η * ((#A : ℝ) * (p : ℝ)) <
        |(((A : Set V) ∩ G.neighborSet u).ncard : ℝ) - (#A : ℝ) * (p : ℝ)|} : Set V).ncard} ≤
      3 * (4 : ℝ) ^ Fintype.card V * Real.exp (-(η ^ 2 * (k : ℝ) * (a₀ : ℝ) * (p : ℝ) / 24)) := by
  classical
  have hp0 : (0 : ℝ) ≤ p := unitInterval.nonneg p
  let badPair (A K : Finset V) : Set (SimpleGraph V) :=
    {G | ∑ u ∈ K, (((A : Set V) ∩ G.neighborSet u).ncard : ℝ) ≤
      (1 - η) * ((#K : ℝ) * (#A : ℝ) * (p : ℝ))} ∪
    {G | (1 + η) * ((#K : ℝ) * (#A : ℝ) * (p : ℝ)) ≤
      ∑ u ∈ K, (((A : Set V) ∩ G.neighborSet u).ncard : ℝ)}
  let As : Finset (Finset V) := (univ : Finset (Finset V)).filter fun A => a₀ ≤ #A
  let Ks : Finset (Finset V) := powersetCard k (univ : Finset V)
  have hsub : {G : SimpleGraph V | ∃ A : Finset V, a₀ ≤ #A ∧
      2 * k ≤ ({u : V | η * ((#A : ℝ) * (p : ℝ)) <
        |(((A : Set V) ∩ G.neighborSet u).ncard : ℝ) - (#A : ℝ) * (p : ℝ)|} : Set V).ncard} ⊆
      ⋃ A ∈ As, ⋃ K ∈ Ks, badPair A K := by
    intro G hG
    rcases hG with ⟨A, hA, hbad⟩
    let B : Finset V := univ.filter fun u =>
      η * ((#A : ℝ) * (p : ℝ)) <
        |(((A : Set V) ∩ G.neighborSet u).ncard : ℝ) - (#A : ℝ) * (p : ℝ)|
    let B₁ : Finset V := univ.filter fun u =>
      (((A : Set V) ∩ G.neighborSet u).ncard : ℝ) ≤ (1 - η) * ((#A : ℝ) * (p : ℝ))
    let B₂ : Finset V := univ.filter fun u =>
      (1 + η) * ((#A : ℝ) * (p : ℝ)) ≤ (((A : Set V) ∩ G.neighborSet u).ncard : ℝ)
    have hB_card : 2 * k ≤ #B := by
      have hcoe : ({u : V | η * ((#A : ℝ) * (p : ℝ)) <
          |(((A : Set V) ∩ G.neighborSet u).ncard : ℝ) - (#A : ℝ) * (p : ℝ)|} : Set V) =
          (B : Set V) := by
        ext u; simp [B]
      rwa [hcoe, Set.ncard_coe_finset] at hbad
    have hB_sub : B ⊆ B₁ ∪ B₂ := by
      intro u hu
      simp only [B, B₁, B₂, Finset.mem_filter, Finset.mem_union, mem_univ, true_and] at hu ⊢
      rcases lt_abs.1 hu with hpos | hneg
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    have hsplit : k ≤ #B₁ ∨ k ≤ #B₂ := by
      have := (Finset.card_le_card hB_sub).trans (Finset.card_union_le B₁ B₂)
      omega
    simp only [Set.mem_iUnion, exists_prop, As, Ks, Finset.mem_filter, mem_univ, true_and,
      Finset.mem_powersetCard, subset_univ]
    rcases hsplit with h1 | h2
    · obtain ⟨K, hKB, hKc⟩ := Finset.exists_subset_card_eq h1
      refine ⟨A, hA, K, hKc, Or.inl ?_⟩
      simp only [Set.mem_ofPred_eq]
      calc ∑ u ∈ K, (((A : Set V) ∩ G.neighborSet u).ncard : ℝ)
          ≤ ∑ _u ∈ K, (1 - η) * ((#A : ℝ) * (p : ℝ)) :=
            Finset.sum_le_sum fun u hu => (Finset.mem_filter.1 (hKB hu)).2
        _ = (1 - η) * ((#K : ℝ) * (#A : ℝ) * (p : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
    · obtain ⟨K, hKB, hKc⟩ := Finset.exists_subset_card_eq h2
      refine ⟨A, hA, K, hKc, Or.inr ?_⟩
      simp only [Set.mem_ofPred_eq]
      calc (1 + η) * ((#K : ℝ) * (#A : ℝ) * (p : ℝ))
          = ∑ _u ∈ K, (1 + η) * ((#A : ℝ) * (p : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ ∑ u ∈ K, (((A : Set V) ∩ G.neighborSet u).ncard : ℝ) :=
            Finset.sum_le_sum fun u hu => (Finset.mem_filter.1 (hKB hu)).2
  have hterm : ∀ A ∈ As, ∀ K ∈ Ks,
      G(V, p).real (badPair A K) ≤
        3 * Real.exp (-(η ^ 2 * (k : ℝ) * (a₀ : ℝ) * (p : ℝ) / 24)) := by
    intro A hA K hK
    have hA' : a₀ ≤ #A := (Finset.mem_filter.1 hA).2
    have hK' : #K = k := (Finset.mem_powersetCard.1 hK).2
    have hKA : 4 * (#K : ℝ) ≤ η * (#A : ℝ) := by
      have hA_real : (a₀ : ℝ) ≤ (#A : ℝ) := by exact_mod_cast hA'
      rw [hK']
      nlinarith
    refine (binomialRandom_real_sum_degreeInto_bad_le p K A hη0 hη1 hKA).trans ?_
    rw [hK']
    gcongr
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc ∑ A ∈ As, G(V, p).real (⋃ K ∈ Ks, badPair A K)
      ≤ ∑ A ∈ As, ∑ K ∈ Ks, G(V, p).real (badPair A K) :=
        Finset.sum_le_sum fun A _ => measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _A ∈ As, ∑ _K ∈ Ks,
          3 * Real.exp (-(η ^ 2 * (k : ℝ) * (a₀ : ℝ) * (p : ℝ) / 24)) :=
        Finset.sum_le_sum fun A hA => Finset.sum_le_sum fun K hK => hterm A hA K hK
    _ = (#As : ℝ) * (#Ks : ℝ) *
          (3 * Real.exp (-(η ^ 2 * (k : ℝ) * (a₀ : ℝ) * (p : ℝ) / 24))) := by
        simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ((2 : ℝ) ^ Fintype.card V) * ((2 : ℝ) ^ Fintype.card V) *
          (3 * Real.exp (-(η ^ 2 * (k : ℝ) * (a₀ : ℝ) * (p : ℝ) / 24))) := by
        have hcard (T : Finset (Finset V)) : (#T : ℝ) ≤ (2 : ℝ) ^ Fintype.card V := by
          have : #T ≤ Fintype.card (Finset V) := Finset.card_le_univ T
          rw [Fintype.card_finset] at this
          exact_mod_cast this
        have hAs := hcard As
        have hKs := hcard Ks
        gcongr
    _ = 3 * (4 : ℝ) ^ Fintype.card V *
          Real.exp (-(η ^ 2 * (k : ℝ) * (a₀ : ℝ) * (p : ℝ) / 24)) := by
        rw [← mul_pow, show (2 : ℝ) * 2 = 4 by norm_num]
        ring

/-! ### Bollobás Theorem 2.15 / NRTV Theorem 29.18 -/

/-- **Bollobás's non-neighborhood bound, finite-`n` form** (Bollobás 2001, Theorem 2.15;
[Suri2007], Theorem 29.18, p. 731, and Equation (29.8), p. 732): in `G(V, p)` on `n = |V| ≥ 1`
vertices, if `δ, C > 0`, `C ≤ u * p`, `3 * log n ≤ δ * p * n`, and `3 * log (e / δ) ≤ C`, then
the probability that there exists a vertex set `U` with `u ≤ #U` whose outside non-neighborhood
`{x ∉ U | Disjoint (G.neighborSet x) U}` has size at least `δ * n` is at most
`exp (-(C * δ * n / 3))`. -/
theorem binomialRandom_real_exists_large_nonNeighborhood_le [Fintype V]
    (hn : 0 < Fintype.card V) (p : I) {δ C : ℝ} (hδ : 0 < δ) {u : ℕ}
    (hCu : C ≤ (u : ℝ) * (p : ℝ))
    (hlog : 3 * Real.log (Fintype.card V) ≤ δ * (p : ℝ) * Fintype.card V)
    (hClog : 3 * Real.log (Real.exp 1 / δ) ≤ C) :
    G(V, p).real {G | ∃ U : Finset V, u ≤ #U ∧
      δ * Fintype.card V ≤
        ({x : V | x ∉ U ∧ Disjoint (G.neighborSet x) (U : Set V)} : Set V).ncard} ≤
      Real.exp (-(C * δ * Fintype.card V / 3)) := by
  classical
  set n : ℕ := Fintype.card V
  set t : ℕ := ⌈δ * (n : ℝ)⌉₊
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hδn_pos : 0 < δ * (n : ℝ) := mul_pos hδ hn_pos
  have ht_ge : δ * (n : ℝ) ≤ (t : ℝ) := Nat.le_ceil _
  have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le hδn_pos ht_ge
  let Us : Finset (Finset V) := powersetCard u (univ : Finset V)
  let Ts (U : Finset V) : Finset (Finset V) :=
    (powersetCard t (univ : Finset V)).filter (Disjoint U)
  let noEdge (U T : Finset V) : Set (SimpleGraph V) :=
    {G | Disjoint ((bipartitePairs U T : Finset (Sym2 V)) : Set (Sym2 V)) G.edgeSet}
  have hsub : {G : SimpleGraph V | ∃ U : Finset V, u ≤ #U ∧
      δ * (n : ℝ) ≤
        ({x : V | x ∉ U ∧ Disjoint (G.neighborSet x) (U : Set V)} : Set V).ncard} ⊆
      ⋃ U ∈ Us, ⋃ T ∈ Ts U, noEdge U T := by
    intro G ⟨U, huU, hTU⟩
    obtain ⟨U', hU'sub, hU'card⟩ := Finset.exists_subset_card_eq huU
    let N : Finset V := univ.filter fun x => x ∉ U ∧ Disjoint (G.neighborSet x) (U : Set V)
    have hN_card : t ≤ #N := by
      have hcoe : ({x : V | x ∉ U ∧ Disjoint (G.neighborSet x) (U : Set V)} : Set V) =
          (N : Set V) := by
        ext x; simp [N]
      rw [hcoe, Set.ncard_coe_finset] at hTU
      exact Nat.ceil_le.2 hTU
    obtain ⟨T, hTN, hTcard⟩ := Finset.exists_subset_card_eq hN_card
    have hdisj : Disjoint U' T := Finset.disjoint_left.2 fun x hxU' hxT =>
      (Finset.mem_filter.1 (hTN hxT)).2.1 (hU'sub hxU')
    simp only [Set.mem_iUnion, exists_prop, Us, Ts, Finset.mem_powersetCard, subset_univ, true_and,
      Finset.mem_filter]
    refine ⟨U', hU'card, T, ⟨hTcard, hdisj⟩, ?_⟩
    simp only [noEdge, Set.mem_ofPred_eq, Set.disjoint_left, Finset.mem_coe, bipartitePairs,
      Finset.mem_image, Finset.mem_product]
    rintro _ ⟨⟨w, x⟩, ⟨hw, hx⟩, rfl⟩ hwx
    exact Set.disjoint_left.1 (Finset.mem_filter.1 (hTN hx)).2.2
      ((G.mem_neighborSet x w).2 hwx.symm) (hU'sub hw)
  have hnoEdge : ∀ U ∈ Us, ∀ T ∈ Ts U, G(V, p).real (noEdge U T) = (1 - (p : ℝ)) ^ (u * t) := by
    intro U hU T hT
    have hUc : #U = u := (Finset.mem_powersetCard.1 hU).2
    have hT' := Finset.mem_filter.1 hT
    have hTc : #T = t := (Finset.mem_powersetCard.1 hT'.1).2
    rw [binomialRandom_real_disjoint_edgeSet p (bipartitePairs U T)
      (fun _ => not_isDiag_of_mem_bipartitePairs hT'.2), card_bipartitePairs hT'.2, hUc, hTc]
  have hbound : G(V, p).real (⋃ U ∈ Us, ⋃ T ∈ Ts U, noEdge U T) ≤
      (n.choose u : ℝ) * (n.choose t : ℝ) * (1 - (p : ℝ)) ^ (u * t) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    calc ∑ U ∈ Us, G(V, p).real (⋃ T ∈ Ts U, noEdge U T)
        ≤ ∑ U ∈ Us, ∑ T ∈ Ts U, G(V, p).real (noEdge U T) :=
          Finset.sum_le_sum fun U _ => measureReal_biUnion_finset_le _ _
      _ = ∑ U ∈ Us, (#(Ts U) : ℝ) * (1 - (p : ℝ)) ^ (u * t) := by
          refine Finset.sum_congr rfl fun U hU => ?_
          rw [Finset.sum_congr rfl fun T hT => hnoEdge U hU T hT, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ _U ∈ Us, (n.choose t : ℝ) * (1 - (p : ℝ)) ^ (u * t) := by
          refine Finset.sum_le_sum fun U _ => ?_
          have hTs_le : (#(Ts U) : ℝ) ≤ (n.choose t : ℝ) := by
            have := Finset.card_le_card (Finset.filter_subset (Disjoint U)
              (powersetCard t (univ : Finset V)))
            rw [Finset.card_powersetCard, Finset.card_univ] at this
            exact_mod_cast this
          have hq : 0 ≤ (1 - (p : ℝ)) ^ (u * t) :=
            pow_nonneg (sub_nonneg.2 (unitInterval.le_one p)) _
          exact mul_le_mul_of_nonneg_right hTs_le hq
      _ = (n.choose u : ℝ) * (n.choose t : ℝ) * (1 - (p : ℝ)) ^ (u * t) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_univ]
          ring
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans (hbound.trans ?_)
  -- Bound each of the three factors by an exponential.
  have h1 : (n.choose u : ℝ) ≤ Real.exp ((u : ℝ) * Real.log n) := by
    have hpow_nat : n.choose u ≤ n ^ u := Nat.choose_le_pow n u
    have hpow : (n.choose u : ℝ) ≤ (n : ℝ) ^ u := by exact_mod_cast hpow_nat
    calc (n.choose u : ℝ) ≤ (n : ℝ) ^ u := hpow
      _ = (Real.exp (Real.log n)) ^ u := by rw [Real.exp_log hn_pos]
      _ = Real.exp ((u : ℝ) * Real.log n) := by rw [← Real.exp_nat_mul]
  have h2 : (n.choose t : ℝ) ≤ Real.exp ((t : ℝ) * Real.log (Real.exp 1 / δ)) := by
    have hdiv : Real.exp 1 * (n : ℝ) / (t : ℝ) ≤ Real.exp 1 / δ := by
      rw [div_le_div_iff₀ ht_pos hδ]
      have : Real.exp 1 * (n : ℝ) * δ = Real.exp 1 * (δ * (n : ℝ)) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left ht_ge (Real.exp_pos 1).le
    calc (n.choose t : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (t : ℝ)) ^ t :=
          Nat.choose_le_exp_mul_div_pow n t
      _ ≤ (Real.exp 1 / δ) ^ t := pow_le_pow_left₀ (by positivity) hdiv t
      _ = (Real.exp (Real.log (Real.exp 1 / δ))) ^ t := by rw [Real.exp_log (by positivity)]
      _ = Real.exp ((t : ℝ) * Real.log (Real.exp 1 / δ)) := by rw [← Real.exp_nat_mul]
  have h3 : (1 - (p : ℝ)) ^ (u * t) ≤ Real.exp (-((u : ℝ) * (t : ℝ) * (p : ℝ))) :=
    Real.one_sub_pow_le_exp (unitInterval.le_one p) (by push_cast; linarith)
  calc (n.choose u : ℝ) * (n.choose t : ℝ) * (1 - (p : ℝ)) ^ (u * t)
      ≤ Real.exp ((u : ℝ) * Real.log n) * Real.exp ((t : ℝ) * Real.log (Real.exp 1 / δ)) *
          Real.exp (-((u : ℝ) * (t : ℝ) * (p : ℝ))) := by
        have hq : 0 ≤ (1 - (p : ℝ)) ^ (u * t) :=
          pow_nonneg (sub_nonneg.2 (unitInterval.le_one p)) _
        exact mul_le_mul (mul_le_mul h1 h2 (Nat.cast_nonneg _) (Real.exp_pos _).le) h3 hq
          (by positivity)
    _ = Real.exp ((u : ℝ) * Real.log n + (t : ℝ) * Real.log (Real.exp 1 / δ) -
          (u : ℝ) * (t : ℝ) * (p : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add, sub_eq_add_neg]
    _ ≤ Real.exp (-(C * δ * (n : ℝ) / 3)) := by
        apply Real.exp_le_exp.2
        have hpt : 3 * Real.log n ≤ (t : ℝ) * (p : ℝ) := by
          have : δ * (p : ℝ) * (n : ℝ) ≤ (t : ℝ) * (p : ℝ) := by
            have := mul_le_mul_of_nonneg_right ht_ge (unitInterval.nonneg p)
            linarith
          linarith
        have hterm1 : (u : ℝ) * Real.log n ≤ (u : ℝ) * (t : ℝ) * (p : ℝ) / 3 := by
          have := mul_le_mul_of_nonneg_left hpt (Nat.cast_nonneg u)
          linarith
        have hterm2 : (t : ℝ) * Real.log (Real.exp 1 / δ) ≤ (u : ℝ) * (t : ℝ) * (p : ℝ) / 3 := by
          have := mul_le_mul_of_nonneg_left (hClog.trans hCu) ht_pos.le
          linarith
        have hterm3 : C * δ * (n : ℝ) ≤ (u : ℝ) * (t : ℝ) * (p : ℝ) := by
          have h1' : C * (δ * (n : ℝ)) ≤ ((u : ℝ) * (p : ℝ)) * (t : ℝ) :=
            mul_le_mul hCu ht_ge hδn_pos.le (mul_nonneg (Nat.cast_nonneg u) (unitInterval.nonneg p))
          linarith
        linarith

/-- **Bollobás's non-neighborhood theorem** (Bollobás 2001, Theorem 2.15; [Suri2007],
Theorem 29.18, p. 731): suppose `δ n > 0` and `C n` eventually satisfy
`3 * log n ≤ δ n * p n * n`, `3 * log (e / δ n) ≤ C n`, and `C n * δ n * n → ∞`. Then with
probability tending to `1`, every vertex subset `U` of `G(Fin n, p n)` of size `⌈C n / p n⌉₊`
leaves at most `δ n * n` outside vertices with no neighbor in `U`. -/
theorem tendsto_binomialRandom_real_forall_nonNeighborhood_le {p : ℕ → I} {δ C : ℕ → ℝ}
    (hδ : ∀ᶠ n : ℕ in atTop, 0 < δ n)
    (hlog : ∀ᶠ n : ℕ in atTop, 3 * Real.log n ≤ δ n * (p n : ℝ) * n)
    (hClog : ∀ᶠ n : ℕ in atTop, 3 * Real.log (Real.exp 1 / δ n) ≤ C n)
    (hinf : Tendsto (fun n : ℕ => C n * δ n * n) atTop atTop) :
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | ∀ U : Finset (Fin n),
      #U = ⌈C n / (p n : ℝ)⌉₊ →
        (({x : Fin n | x ∉ U ∧
          Disjoint (G.neighborSet x) (U : Set (Fin n))} : Set (Fin n)).ncard : ℝ) ≤
          δ n * n}) atTop (𝓝 1) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(C n * δ n * n / 3))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (hinf.atTop_div_const (by norm_num : (0 : ℝ) < 3))
  have hbad : Tendsto (fun n : ℕ => G(Fin n, p n).real {G | ∃ U : Finset (Fin n),
      #U = ⌈C n / (p n : ℝ)⌉₊ ∧
        δ n * n <
          (({x : Fin n | x ∉ U ∧
            Disjoint (G.neighborSet x) (U : Set (Fin n))} : Set (Fin n)).ncard : ℝ)})
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
      (Eventually.of_forall fun _ => measureReal_nonneg) ?_
    filter_upwards [hδ, hlog, hClog, eventually_ge_atTop 2] with n hδn hlogn hClogn hn2
    have hn_pos : 0 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
    have hlog2 : 0 < 3 * Real.log (n : ℝ) := by
      have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      exact mul_pos (by norm_num) (Real.log_pos this)
    have hp_pos : 0 < (p n : ℝ) := by
      by_contra! hp0
      have hp_eq : (p n : ℝ) = 0 := le_antisymm hp0 (unitInterval.nonneg (p n))
      rw [hp_eq, mul_zero, zero_mul] at hlogn
      linarith
    have hCu : C n ≤ (⌈C n / (p n : ℝ)⌉₊ : ℝ) * (p n : ℝ) :=
      (div_le_iff₀ hp_pos).1 (Nat.le_ceil _)
    have hsub : {G : SimpleGraph (Fin n) | ∃ U : Finset (Fin n), #U = ⌈C n / (p n : ℝ)⌉₊ ∧
        δ n * n <
          (({x : Fin n | x ∉ U ∧
            Disjoint (G.neighborSet x) (U : Set (Fin n))} : Set (Fin n)).ncard : ℝ)} ⊆
        {G | ∃ U : Finset (Fin n), ⌈C n / (p n : ℝ)⌉₊ ≤ #U ∧
          δ n * Fintype.card (Fin n) ≤
            ({x : Fin n | x ∉ U ∧ Disjoint (G.neighborSet x) (U : Set (Fin n))} :
              Set (Fin n)).ncard} := by
      rintro G ⟨U, hUc, hlt⟩
      exact ⟨U, hUc.ge, by simpa [Fintype.card_fin] using hlt.le⟩
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
    simpa [Fintype.card_fin] using
      binomialRandom_real_exists_large_nonNeighborhood_le hn_pos (p n) hδn hCu
        (by simpa [Fintype.card_fin] using hlogn) hClogn
  have h1 := hbad.const_sub 1
  rw [sub_zero] at h1
  refine h1.congr fun n => ?_
  rw [← probReal_compl_eq_one_sub .of_discrete]
  congr 1
  ext G
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_and, not_lt]

end SimpleGraph
