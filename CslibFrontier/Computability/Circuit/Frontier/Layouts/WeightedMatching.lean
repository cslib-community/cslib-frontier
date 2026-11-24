/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Matching
public import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.CubicMatching
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Support
import CslibFrontier.Foundations.Data.Nat.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weighted pair-node layouts and effective-cut bounds on cubic multigraphs

Extends `CslibFrontier.Computability.Circuit.Frontier.Layouts.Matching` to fractional `(1, 1)`
straddle weights `λ ∈ [0, 1]` on a clean sub-matching `M_clean ⊆ M` of a loopless cubic multigraph:

* Lifting `SimpleGraph.exists_isMatching_mul_eight_ge` to loopless edge-simple cubic multigraphs
  (`Multigraph.exists_isMatching_mul_eight_ge`).
* An exact natural-number prefix slack bound (`ncard_edgeCut_add_inactive_le_matchingCost`) showing
  that every clean `(1, 1)` pair whose high-score outer edges do *not* both stay on the prefix cut
  already saves at least `1` cut edge below `matchingCost`.
* Grouping equal-key clean pairs into `PairNode`s and sorting by `pairNodeKey`, bounding the
  `(1 - λ)`-discounted effective cut at every prefix across a score grid
  (`exists_u2_pairNode_layout`), packaged at `λ = log₂ 3 - 1` as `U2CubicPairBound`.

The fractional prefix-slack reduction (`ncard_edgeCut_add_inactive_le_matchingCost`) and
equal-key `PairNode` layout (`exists_u2_pairNode_layout`) are original to this library.

## Main definitions

* `Cslib.Circuits.Frontier.Multigraph.outerLow`,
  `Cslib.Circuits.Frontier.Multigraph.outerHigh`: ordered outer incident edges at a cubic endpoint.
* `Cslib.Circuits.Frontier.Multigraph.activeCleanPairs`: clean matched pairs in a prefix `P` whose
  two high-score outer edges both cross `G.edgeCut P`.
* `Cslib.Circuits.Frontier.Multigraph.weightedMatchingCost`: threshold cost assigning weight `λ` to
  `PairStraddlesBoth` on `M_clean` and `1` on `M \ M_clean`.
* `Cslib.Circuits.Frontier.Multigraph.PairNode`,
  `Cslib.Circuits.Frontier.Multigraph.pairNodeVerts`: equal-key pair/singleton quotient nodes and
  their expanded vertex sets.
* `Cslib.Circuits.Frontier.U2CubicPairBound`: cubic pair-node effective-cut layout hypothesis at
  `1 - λ = 2 - log₂ 3`.

## Main results

* `Cslib.Circuits.Frontier.Multigraph.exists_isMatching_mul_eight_ge`: `7/8` vertex-coverage
  matching on loopless edge-simple cubic multigraphs.
* `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_add_inactive_le_matchingCost`,
  `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_sub_active_le_weightedMatchingCost`:
  natural-number prefix slack and real effective-cut bounds.
* `Cslib.Circuits.Frontier.Multigraph.exists_u2_pairNode_layout`: grid reduction for `PairNode`
  threshold layouts.
-/

public section

namespace Cslib.Circuits.Frontier.Multigraph

open Set

section CubicMatching

variable {V E : Type*} (G : Multigraph V E)

/-- Lift the `7/8` vertex-coverage matching theorem from `SimpleGraph` to a cubic `Multigraph`
without loops or parallel edges. -/
theorem exists_isMatching_mul_eight_ge [Finite V] (hloop : G.Loopless)
    (hinj : Function.Injective G.ends) (h3 : ∀ v, (G.incidenceSet v).ncard = 3) :
    ∃ M : Set E, G.IsMatching M ∧ 7 * Nat.card V ≤ 8 * (G.matchedVertices M).ncard := by
  classical
  let otherEnd (v : V) (e : E) : V := if G.src e = v then G.tgt e else G.src e
  have hends_other {v : V} {e : E} (he : e ∈ G.incidenceSet v) :
      G.ends e = s(v, otherEnd v e) := by
    rcases he with h | h
    · rw [← h]; simp [otherEnd, ends]
    · rw [← h, ends]
      simp only [otherEnd, hloop e, ↓reduceIte, Sym2.eq_swap]
  have h3_simple (v : V) : (G.toSimpleGraph.neighborSet v).ncard = 3 := by
    rw [← h3 v]
    symm
    refine Set.ncard_congr (fun e _ => otherEnd v e) (fun e he => ?_)
      (fun e₁ e₂ he₁ he₂ h => hinj ((hends_other he₁).trans (h ▸ (hends_other he₂).symm)))
      fun w hw => ?_
    · rw [SimpleGraph.mem_neighborSet, toSimpleGraph_adj]
      refine ⟨?_, e, hends_other he⟩
      rcases he with h | h
      · rw [← h]; simp only [otherEnd, ↓reduceIte]; exact hloop e
      · rw [← h]; simp only [otherEnd, hloop e, ↓reduceIte]; exact (hloop e).symm
    · rw [SimpleGraph.mem_neighborSet, toSimpleGraph_adj] at hw
      obtain ⟨hvw, e, he⟩ := hw
      rcases Sym2.eq_iff.mp he with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact ⟨e, Or.inl hs, by simp only [otherEnd, hs, ↓reduceIte, ht]⟩
      · exact ⟨e, Or.inr ht, by simp only [otherEnd, hs, hvw.symm, ↓reduceIte]⟩
  obtain ⟨M_sg, hM_sg, h78⟩ := G.toSimpleGraph.exists_isMatching_mul_eight_ge h3_simple
  let M : Set E := {e | M_sg.Adj (G.src e) (G.tgt e)}
  have hM : G.IsMatching M := by
    intro e₁ he₁ e₂ he₂ hne
    change M_sg.Adj (G.src e₁) (G.tgt e₁) at he₁
    change M_sg.Adj (G.src e₂) (G.tgt e₂) at he₂
    refine Set.disjoint_left.mpr fun v hv₁ hv₂ => hne ?_
    have hadj₁ : M_sg.Adj v (otherEnd v e₁) := by
      rcases hv₁ with rfl | rfl
      · simp only [otherEnd, ↓reduceIte]; exact he₁
      · simp only [otherEnd, hloop e₁, ↓reduceIte]; exact M_sg.symm.symm _ _ he₁
    have hadj₂ : M_sg.Adj v (otherEnd v e₂) := by
      rcases hv₂ with rfl | rfl
      · simp only [otherEnd, ↓reduceIte]; exact he₂
      · simp only [otherEnd, hloop e₂, ↓reduceIte]; exact M_sg.symm.symm _ _ he₂
    have heq : otherEnd v e₁ = otherEnd v e₂ := hM_sg.eq_of_adj_left hadj₁ hadj₂
    have hi₁ : e₁ ∈ G.incidenceSet v := by
      rcases hv₁ with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
    have hi₂ : e₂ ∈ G.incidenceSet v := by
      rcases hv₂ with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
    exact hinj ((hends_other hi₁).trans (heq ▸ (hends_other hi₂).symm))
  have hverts : G.matchedVertices M = M_sg.verts := by
    ext v
    simp only [matchedVertices, mem_ofPred_eq]
    constructor
    · rintro ⟨e, heM, rfl | rfl⟩
      · exact M_sg.edge_vert heM
      · exact M_sg.edge_vert (M_sg.symm.symm _ _ heM)
    · intro hv
      obtain ⟨w, hvw, -⟩ := hM_sg hv
      obtain ⟨_, e, he⟩ := toSimpleGraph_adj.mp (M_sg.adj_sub hvw)
      rcases Sym2.eq_iff.mp he with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact ⟨e, by change M_sg.Adj _ _; rwa [hs, ht], Or.inl hs⟩
      · exact ⟨e, by change M_sg.Adj _ _; rw [hs, ht]; exact M_sg.symm.symm _ _ hvw, Or.inr ht⟩
  rw [← hverts] at h78
  exact ⟨M, hM, h78⟩

end CubicMatching

/-! ### Weighted matching cost and prefix slack on `(1, 1)` matched pairs -/

section WeightedMatching

variable {V E : Type*}

/-- Lower-scoring outer edge at `v` excluding `e` (falling back to `e` outside degree `3`). -/
noncomputable def outerLow (G : Multigraph V E) (score : E → ℝ) (v : V) (e : E) : E :=
  letI := Classical.dec
  if hs : (G.incidenceSet v \ {e}).ncard = 2 then
    let p := (ncard_eq_two.mp hs).choose
    let q := (ncard_eq_two.mp hs).choose_spec.choose
    if score p ≤ score q then p else q
  else e

/-- Higher-scoring outer edge at `v` excluding `e` (falling back to `e` outside degree `3`). -/
noncomputable def outerHigh (G : Multigraph V E) (score : E → ℝ) (v : V) (e : E) : E :=
  letI := Classical.dec
  if hs : (G.incidenceSet v \ {e}).ncard = 2 then
    let p := (ncard_eq_two.mp hs).choose
    let q := (ncard_eq_two.mp hs).choose_spec.choose
    if score p ≤ score q then q else p
  else e

/-- Clean matched edges `e ∈ M_clean` whose endpoints share their `matchingKey`, both lie in `P`,
and whose two high-score outer edges both cross `G.edgeCut P`. -/
@[expose]
def activeCleanPairs (G : Multigraph V E) (M M_clean : Set E) (score : E → ℝ) (P : Set V) :
    Set E :=
  {e | e ∈ M_clean ∧ G.matchingKey M score (G.src e) = G.matchingKey M score (G.tgt e) ∧
    G.src e ∈ P ∧ G.tgt e ∈ P ∧
    G.outerHigh score (G.src e) e ∈ G.edgeCut P ∧
    G.outerHigh score (G.tgt e) e ∈ G.edgeCut P}

/-- Weighted matching cost at threshold `t`: unpaired straddling vertices pay `1`, matched edges
satisfying `PairStraddlesAny` pay `1`, dirty matched edges (`M \ M_clean`) satisfying
`PairStraddlesBoth` pay `1`, and clean matched edges (`M_clean`) satisfying `PairStraddlesBoth` pay
`lam`. -/
@[expose]
noncomputable def weightedMatchingCost (G : Multigraph V E) (M M_clean : Set E) (lam : ℝ)
    (score : E → ℝ) (t : ℝ) : ℝ :=
  ({v | v ∉ G.matchedVertices M ∧ G.EdgeStraddles score t v}.ncard : ℝ) +
    ({e | e ∈ M ∧ G.PairStraddlesAny score t e}.ncard : ℝ) +
    ({e | e ∈ M \ M_clean ∧ G.PairStraddlesBoth score t e}.ncard : ℝ) +
    lam * ({e | e ∈ M_clean ∧ G.PairStraddlesBoth score t e}.ncard : ℝ)

/-- The two non-`e` incident edges at a degree-`3` vertex `v` are `{outerLow, outerHigh}` in
nondecreasing `score` order. -/
theorem outerLow_outerHigh_spec [Finite E] {G : Multigraph V E}
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (score : E → ℝ) {v : V} {e : E}
    (hev : e ∈ G.incidenceSet v) :
    G.outerLow score v e ≠ G.outerHigh score v e ∧
      G.incidenceSet v \ {e} = {G.outerLow score v e, G.outerHigh score v e} ∧
      score (G.outerLow score v e) ≤ score (G.outerHigh score v e) := by
  have hs : (G.incidenceSet v \ {e}).ncard = 2 := by
    have := ncard_sdiff_singleton_add_one hev (s := G.incidenceSet v)
    have := h3 v
    omega
  set p := (ncard_eq_two.mp hs).choose
  set q := (ncard_eq_two.mp hs).choose_spec.choose
  have hspec : p ≠ q ∧ G.incidenceSet v \ {e} = {p, q} :=
    (ncard_eq_two.mp hs).choose_spec.choose_spec
  dsimp only [outerLow, outerHigh]
  rw [dite_eq_left hs, dite_eq_left hs]
  by_cases hpq : score p ≤ score q
  · rw [ite_eq_left hpq, ite_eq_left hpq]
    exact ⟨hspec.1, hspec.2, hpq⟩
  · rw [ite_eq_right hpq, ite_eq_right hpq]
    exact ⟨hspec.1.symm, hspec.2.trans (pair_comm p q), le_of_not_ge hpq⟩

/-- High-score outer edge pairs `{b_e, d_e}` of `activeCleanPairs` have `2` distinct edges each. -/
theorem outerHigh_src_ne_tgt [Finite E] {G : Multigraph V E} (hloop : G.Loopless)
    (hinj : Function.Injective G.ends) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    (score : E → ℝ) (e : E) :
    G.outerHigh score (G.src e) e ≠ G.outerHigh score (G.tgt e) e := by
  set b := G.outerHigh score (G.src e) e
  set d := G.outerHigh score (G.tgt e) e
  intro heq
  have hbs := (outerLow_outerHigh_spec h3 score (v := G.src e) (Or.inl rfl)).2.1
  have hdt := (outerLow_outerHigh_spec h3 score (v := G.tgt e) (Or.inr rfl)).2.1
  have hb_mem : b ∈ G.incidenceSet (G.src e) \ {e} := by rw [hbs]; simp [b]
  have hd_mem : b ∈ G.incidenceSet (G.tgt e) \ {e} := by rw [heq, hdt]; simp [d]
  rcases hb_mem.1 with hs | ht <;> rcases hd_mem.1 with hs' | ht'
  · exact hloop e (hs.symm.trans hs')
  · exact hb_mem.2 (hinj (by simp [ends, hs, ht']))
  · exact hb_mem.2 (hinj (by simp [ends, ht, hs', Sym2.eq_swap]))
  · exact hloop e (ht.symm.trans ht')

/-- High-score outer edge pairs `{b_e, d_e}` of `activeCleanPairs` are pairwise disjoint across
distinct active pairs. -/
theorem pairwiseDisjoint_activeCleanPairs [Finite E] {G : Multigraph V E}
    {M M_clean : Set E} (hM : G.IsMatching M) (hclean : M_clean ⊆ M)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (score : E → ℝ) (P : Set V) :
    (G.activeCleanPairs M M_clean score P).PairwiseDisjoint fun e =>
      ({G.outerHigh score (G.src e) e, G.outerHigh score (G.tgt e) e} : Set E) := by
  intro e₁ he₁ e₂ he₂ hne
  refine Set.disjoint_left.mpr fun f hf₁ hf₂ => ?_
  have hf_cut : f ∈ G.edgeCut P := by
    rcases hf₁ with rfl | rfl
    · exact he₁.2.2.2.2.1
    · exact he₁.2.2.2.2.2
  have end_in (e : E) (he : e ∈ G.activeCleanPairs M M_clean score P)
      (hf : f ∈ ({G.outerHigh score (G.src e) e, G.outerHigh score (G.tgt e) e} : Set E)) :
      ∃ u ∈ ({G.src e, G.tgt e} : Set V), u ∈ P ∧ f ∈ G.incidenceSet u := by
    rcases hf with rfl | rfl
    · have hb := (outerLow_outerHigh_spec h3 score (v := G.src e) (Or.inl rfl)).2.1
      have hmem : G.outerHigh score (G.src e) e ∈ G.incidenceSet (G.src e) \ {e} := by
        rw [hb]; simp
      exact ⟨G.src e, Or.inl rfl, he.2.2.1, hmem.1⟩
    · have hd := (outerLow_outerHigh_spec h3 score (v := G.tgt e) (Or.inr rfl)).2.1
      have hmem : G.outerHigh score (G.tgt e) e ∈ G.incidenceSet (G.tgt e) \ {e} := by
        rw [hd]; simp
      exact ⟨G.tgt e, Or.inr rfl, he.2.2.2.1, hmem.1⟩
  obtain ⟨u₁, hu₁_end, hu₁_P, hu₁_inc⟩ := end_in e₁ he₁ hf₁
  obtain ⟨u₂, hu₂_end, hu₂_P, hu₂_inc⟩ := end_in e₂ he₂ hf₂
  have hu_ne : u₁ ≠ u₂ := fun h =>
    Set.disjoint_left.mp (hM (hclean he₁.1) (hclean he₂.1) hne) hu₁_end (h ▸ hu₂_end)
  have hboth : G.src f ∈ P ∧ G.tgt f ∈ P := by
    rcases hu₁_inc with rfl | rfl <;> rcases hu₂_inc with h2 | h2
    · exact (hu_ne h2).elim
    · exact ⟨hu₁_P, h2 ▸ hu₂_P⟩
    · exact ⟨h2 ▸ hu₂_P, hu₁_P⟩
    · exact (hu_ne h2).elim
  exact hf_cut (iff_of_true hboth.1 hboth.2)

/-- Refined subset cut inequality: edges in `G.edgeCut P₀ \ G.edgeCut P` yield `2` units of slack
against `3 * (P \ P₀).ncard`. -/
private theorem ncard_edgeCut_add_two_mul_sdiff_le [Finite V] [Finite E]
    {G : Multigraph V E} (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {P₀ P : Set V} (hsub : P₀ ⊆ P) :
    (G.edgeCut P).ncard + 2 * (G.edgeCut P₀ \ G.edgeCut P).ncard ≤
      (G.edgeCut P₀).ncard + 3 * (P \ P₀).ncard := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  have hinc_sum : ∑ f : E, ((if G.src f ∈ P \ P₀ then 1 else 0) +
      (if G.tgt f ∈ P \ P₀ then 1 else 0)) = 3 * (P \ P₀).ncard := by
    have hpair (f : E) : (if G.src f ∈ P \ P₀ then 1 else 0) +
        (if G.tgt f ∈ P \ P₀ then 1 else 0) =
        ∑ v ∈ (P \ P₀).toFinset, if f ∈ G.incidenceSet v then 1 else 0 := by
      have hfilt : ((P \ P₀).toFinset.filter fun v => f ∈ G.incidenceSet v) =
          ({G.src f, G.tgt f} : Finset V).filter (· ∈ P \ P₀) := by
        ext v; simp [mem_incidenceSet, eq_comm, and_comm]
      rw [← Finset.card_filter, hfilt, Finset.filter_insert, Finset.filter_singleton]
      by_cases hs : G.src f ∈ P \ P₀ <;> by_cases ht : G.tgt f ∈ P \ P₀ <;>
        simp [hs, ht, hloop f]
    simp_rw [hpair]
    rw [Finset.sum_comm]
    have hv3 (v : V) : (∑ f : E, if f ∈ G.incidenceSet v then 1 else 0) = 3 := by
      rw [← Finset.card_filter, ← Set.ncard_coe_finset]
      have : ((Finset.univ.filter (· ∈ G.incidenceSet v) : Finset E) : Set E) =
          G.incidenceSet v := by ext f; simp
      rw [this, h3 v]
    simp only [hv3, Finset.sum_const, smul_eq_mul, mul_comm _ 3, Set.ncard_eq_toFinset_card']
  have hcard_eq (S : Set E) [DecidablePred (· ∈ S)] :
      S.ncard = ∑ f : E, if f ∈ S then 1 else 0 := by
    rw [← Finset.card_filter, ← Set.ncard_coe_finset]
    congr 1; ext f; simp
  rw [hcard_eq (G.edgeCut P), hcard_eq (G.edgeCut P₀ \ G.edgeCut P), hcard_eq (G.edgeCut P₀),
    ← hinc_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun f _ => ?_
  by_cases hs₀ : G.src f ∈ P₀ <;> by_cases hs : G.src f ∈ P <;>
    by_cases ht₀ : G.tgt f ∈ P₀ <;> by_cases ht : G.tgt f ∈ P
  all_goals first
    | exact (hs (hsub hs₀)).elim
    | exact (ht (hsub ht₀)).elim
    | (simp only [mem_edgeCut, mem_sdiff, hs₀, hs, ht₀, ht, not_true_eq_false, not_false_eq_true,
        and_self, and_true, and_false, iff_self, iff_true, iff_false, ↓reduceIte]; omega)

private theorem matchingKey_outer [Finite E] {G : Multigraph V E}
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M : Set E} (hM : G.IsMatching M) (score : E → ℝ) {e : E} (heM : e ∈ M) :
    let a := G.outerLow score (G.src e) e
    let b := G.outerHigh score (G.src e) e
    let c := G.outerLow score (G.tgt e) e
    let d := G.outerHigh score (G.tgt e) e
    G.matchingKey M score (G.src e) = pairKey (score a) (score b) (score c) (score d) ∧
      G.matchingKey M score (G.tgt e) = pairKey (score c) (score d) (score a) (score b) :=
  matchingKey_matched hM hloop h3 score heM
    (outerLow_outerHigh_spec h3 score (Or.inl rfl)).2.1
    (outerLow_outerHigh_spec h3 score (Or.inr rfl)).2.1

/-- On a `(1, 1)`-straddling matched edge `e ∈ M`, both endpoints' outer pairs satisfy
`score outerLow < t ≤ score outerHigh`, and both endpoints share equal `matchingKey < t`. -/
private theorem pairStraddlesBoth_spec [Finite E] {G : Multigraph V E} (hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) {M : Set E} (hM : G.IsMatching M)
    (score : E → ℝ) (t : ℝ) {e : E} (heM : e ∈ M) (hboth : G.PairStraddlesBoth score t e) :
    (score (G.outerLow score (G.src e) e) < t ∧ t ≤ score (G.outerHigh score (G.src e) e)) ∧
    (score (G.outerLow score (G.tgt e) e) < t ∧ t ≤ score (G.outerHigh score (G.tgt e) e)) ∧
    G.matchingKey M score (G.src e) = G.matchingKey M score (G.tgt e) ∧
    G.matchingKey M score (G.src e) < t ∧ G.matchingKey M score (G.tgt e) < t := by
  have hbs := outerLow_outerHigh_spec h3 score (v := G.src e) (Or.inl rfl)
  have hdt := outerLow_outerHigh_spec h3 score (v := G.tgt e) (Or.inr rfl)
  set a := G.outerLow score (G.src e) e
  set b := G.outerHigh score (G.src e) e
  set c := G.outerLow score (G.tgt e) e
  set d := G.outerHigh score (G.tgt e) e
  have hstr_s : score a < t ∧ t ≤ score b := by
    obtain ⟨⟨f₁, hf₁, hlt⟩, ⟨f₂, hf₂, hge⟩⟩ := hboth.1
    rw [hbs.2.1] at hf₁ hf₂
    rcases hf₁ with rfl | rfl <;> rcases hf₂ with rfl | rfl
    · linarith
    · exact ⟨hlt, hge⟩
    · linarith [hbs.2.2]
    · linarith
  have hstr_t : score c < t ∧ t ≤ score d := by
    obtain ⟨⟨f₁, hf₁, hlt⟩, ⟨f₂, hf₂, hge⟩⟩ := hboth.2
    rw [hdt.2.1] at hf₁ hf₂
    rcases hf₁ with rfl | rfl <;> rcases hf₂ with rfl | rfl
    · linarith
    · exact ⟨hlt, hge⟩
    · linarith [hdt.2.2]
    · linarith
  obtain ⟨hks, hkt⟩ := matchingKey_outer hloop h3 hM score heM
  change G.matchingKey M score (G.src e) = pairKey (score a) (score b) (score c) (score d) at hks
  change G.matchingKey M score (G.tgt e) = pairKey (score c) (score d) (score a) (score b) at hkt
  have hks_eq : pairKey (score a) (score b) (score c) (score d) = max (score a) (score c) := by
    have hm1 : min (score a) (score b) = score a := min_eq_left hbs.2.2
    have hm2 : min (score c) (score d) = score c := min_eq_left hdt.2.2
    have hmx1 : max (score a) (score b) = score b := max_eq_right hbs.2.2
    simp only [pairKey, hm1, hm2, hmx1]
    exact min_eq_right (max_le hbs.2.2 (hstr_t.1.le.trans hstr_s.2))
  have hkt_eq : pairKey (score c) (score d) (score a) (score b) = max (score a) (score c) := by
    have hm1 : min (score c) (score d) = score c := min_eq_left hdt.2.2
    have hm2 : min (score a) (score b) = score a := min_eq_left hbs.2.2
    have hmx1 : max (score c) (score d) = score d := max_eq_right hdt.2.2
    simp only [pairKey, hm1, hm2, hmx1, max_comm (score c) (score a)]
    exact min_eq_right (max_le (hstr_s.1.le.trans hstr_t.2) hdt.2.2)
  have hmax_lt : max (score a) (score c) < t := max_lt hstr_s.1 hstr_t.1
  exact ⟨hstr_s, hstr_t, by rw [hks, hkt, hks_eq, hkt_eq],
    by rw [hks, hks_eq]; exact hmax_lt, by rw [hkt, hkt_eq]; exact hmax_lt⟩

/-- **Exact natural-number prefix slack.** For `P₀ = {v | matchingKey v < t} ⊆ P`, every clean
`(1, 1)` pair `e ∈ M_clean` whose two high-score outer edges do *not* both lie in `G.edgeCut P`
contributes at least `1` unit of slack below `G.matchingCost M score t + 3 * (P \ P₀).ncard`. -/
theorem ncard_edgeCut_add_inactive_le_matchingCost [Finite V] [Finite E]
    {G : Multigraph V E} (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M M_clean : Set E} (hM : G.IsMatching M) (hclean : M_clean ⊆ M) (score : E → ℝ) (t : ℝ)
    {P : Set V} (hP₀ : {v | G.matchingKey M score v < t} ⊆ P) :
    let P₀ := {v | G.matchingKey M score v < t}
    (G.edgeCut P).ncard +
      {e | e ∈ M_clean ∧ G.PairStraddlesBoth score t e ∧
        ¬(G.outerHigh score (G.src e) e ∈ G.edgeCut P ∧
          G.outerHigh score (G.tgt e) e ∈ G.edgeCut P)}.ncard ≤
      G.matchingCost M score t + 3 * (P \ P₀).ncard := by
  classical
  intro P₀
  set A_set : Set E := G.edgeCut P₀ \ G.edgeCut P
  set B_set : Set E := {f | f ∉ M ∧ G.src f ∈ P₀ ∧ G.tgt f ∈ P₀ ∧ t ≤ score f}
  set S₂ : Set E := {e | e ∈ M_clean ∧ G.PairStraddlesBoth score t e ∧
    ¬(G.outerHigh score (G.src e) e ∈ G.edgeCut P ∧
      G.outerHigh score (G.tgt e) e ∈ G.edgeCut P)}
  have hAB := Nat.add_le_add (ncard_edgeCut_add_two_mul_sdiff_le hloop h3 hP₀)
    (ncard_edgeCut_threshold_add_slack_le_matchingCost hloop h3 hM score t)
  -- Each `e ∈ S₂` has an endpoint in `P₀` whose high-score outer edge lies in `A_set ∪ B_set`.
  have hS₂_witness : ∀ e ∈ S₂, ∃ f ∈ A_set ∪ B_set,
      f ∈ ({G.outerHigh score (G.src e) e, G.outerHigh score (G.tgt e) e} : Set E) ∧
      (G.src f ∈ ({G.src e, G.tgt e} : Set V) ∨ G.tgt f ∈ ({G.src e, G.tgt e} : Set V)) := by
    intro e ⟨he_cl, hboth, hnot_act⟩
    have heM : e ∈ M := hclean he_cl
    have hbs := outerLow_outerHigh_spec h3 score (v := G.src e) (Or.inl rfl)
    have hdt := outerLow_outerHigh_spec h3 score (v := G.tgt e) (Or.inr rfl)
    set b := G.outerHigh score (G.src e) e
    set d := G.outerHigh score (G.tgt e) e
    obtain ⟨hstr_s, hstr_t, -, hks_lt, hkt_lt⟩ :=
      pairStraddlesBoth_spec hloop h3 hM score t heM hboth
    have hkey_lt : G.src e ∈ P₀ ∧ G.tgt e ∈ P₀ := ⟨hks_lt, hkt_lt⟩
    have check_outer (u : V) (huP₀ : u ∈ P₀) (hu_end : u ∈ ({G.src e, G.tgt e} : Set V))
        (f : E) (hf_mem : f ∈ G.incidenceSet u \ {e}) (hf_ge : t ≤ score f)
        (hf_not_cut : f ∉ G.edgeCut P) :
        f ∈ A_set ∪ B_set ∧ (G.src f ∈ ({G.src e, G.tgt e} : Set V) ∨
          G.tgt f ∈ ({G.src e, G.tgt e} : Set V)) := by
      have hf_notM : f ∉ M := fun hfM => by
        refine hf_mem.2 ?_
        by_contra hfe
        exact Set.disjoint_left.mp (hM hfM heM hfe)
          (hf_mem.1.imp Eq.symm Eq.symm) hu_end
      have hf_end : G.src f ∈ ({G.src e, G.tgt e} : Set V) ∨
          G.tgt f ∈ ({G.src e, G.tgt e} : Set V) :=
        hf_mem.1.imp (fun h => by rw [h]; exact hu_end) (fun h => by rw [h]; exact hu_end)
      refine ⟨?_, hf_end⟩
      by_cases hallP₀ : G.src f ∈ P₀ ∧ G.tgt f ∈ P₀
      · exact Or.inr ⟨hf_notM, hallP₀.1, hallP₀.2, hf_ge⟩
      · left
        refine ⟨?_, hf_not_cut⟩
        simp only [mem_edgeCut]
        rcases hf_mem.1 with h | h
        · intro hiff; exact hallP₀ ⟨by rwa [h], hiff.mp (by rwa [h])⟩
        · intro hiff; exact hallP₀ ⟨hiff.mpr (by rwa [h]), by rwa [h]⟩
    by_cases hb_cut : b ∈ G.edgeCut P
    · have hd_not : d ∉ G.edgeCut P := fun hd_cut => hnot_act ⟨hb_cut, hd_cut⟩
      have hd_mem : d ∈ G.incidenceSet (G.tgt e) \ {e} := by rw [hdt.2.1]; simp
      obtain ⟨hAB_d, hend_d⟩ := check_outer (G.tgt e) hkey_lt.2 (Or.inr rfl) d hd_mem
        hstr_t.2 hd_not
      exact ⟨d, hAB_d, Or.inr rfl, hend_d⟩
    · have hb_mem : b ∈ G.incidenceSet (G.src e) \ {e} := by rw [hbs.2.1]; simp
      obtain ⟨hAB_b, hend_b⟩ := check_outer (G.src e) hkey_lt.1 (Or.inl rfl) b hb_mem
        hstr_s.2 hb_cut
      exact ⟨b, hAB_b, Or.inl rfl, hend_b⟩
  choose f_of hf_mem _ hf_end using fun e : S₂ => hS₂_witness e.1 e.2
  let side (e : S₂) : Bool := decide (G.src (f_of e) ∈ ({G.src e.1, G.tgt e.1} : Set V))
  have hinj_S₂ : Function.Injective fun e : S₂ =>
      ((⟨f_of e, hf_mem e⟩ : ↑(A_set ∪ B_set)), side e) := by
    rintro e₁ e₂ hpair
    obtain ⟨hf_eq, hs_eq⟩ := Prod.mk.inj hpair
    have hf_val : f_of e₁ = f_of e₂ := congrArg Subtype.val hf_eq
    by_contra hne
    have hne_val : e₁.1 ≠ e₂.1 := fun h => hne (Subtype.ext h)
    have hdisj := hM (hclean e₁.2.1) (hclean e₂.2.1) hne_val
    by_cases hs₁ : G.src (f_of e₁) ∈ ({G.src e₁.1, G.tgt e₁.1} : Set V)
    · have hs₂ : G.src (f_of e₁) ∈ ({G.src e₂.1, G.tgt e₂.1} : Set V) := by
        have htrue : side e₂ = true := hs_eq.symm.trans (decide_eq_true hs₁)
        rw [hf_val]
        exact of_decide_eq_true htrue
      exact Set.disjoint_left.mp hdisj hs₁ hs₂
    · have ht₁ : G.tgt (f_of e₁) ∈ ({G.src e₁.1, G.tgt e₁.1} : Set V) :=
        (hf_end e₁).resolve_left hs₁
      have hs₂_false : ¬G.src (f_of e₂) ∈ ({G.src e₂.1, G.tgt e₂.1} : Set V) :=
        of_decide_eq_false (hs_eq.symm.trans (decide_eq_false hs₁))
      have ht₂ : G.tgt (f_of e₁) ∈ ({G.src e₂.1, G.tgt e₂.1} : Set V) := by
        rw [hf_val]; exact (hf_end e₂).resolve_left hs₂_false
      exact Set.disjoint_left.mp hdisj ht₁ ht₂
  have hS₂_le : S₂.ncard ≤ 2 * (A_set.ncard + B_set.ncard) := by
    have h1 := Nat.card_le_card_of_injective _ hinj_S₂
    rw [Nat.card_coe_set_eq, Nat.card_prod, Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
      Fintype.card_bool, mul_comm] at h1
    exact h1.trans (Nat.mul_le_mul_left 2 (ncard_union_le A_set B_set))
  have hAB' : (G.edgeCut P).ncard + 2 * A_set.ncard +
      ((G.edgeCut P₀).ncard + 2 * B_set.ncard) ≤
      (G.edgeCut P₀).ncard + 3 * (P \ P₀).ncard + G.matchingCost M score t := hAB
  omega

/-- **Effective real cut bound.** For `0 ≤ lam ≤ 1` and `P₀ = {v | matchingKey v < t} ⊆ P`,
`|edgeCut P| - (1 - lam) |activeCleanPairs P| ≤ weightedMatchingCost + 3 |P \ P₀|`. -/
theorem ncard_edgeCut_sub_active_le_weightedMatchingCost [Finite V] [Finite E]
    {G : Multigraph V E} (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M M_clean : Set E} (hM : G.IsMatching M) (hclean : M_clean ⊆ M)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (score : E → ℝ) (t : ℝ)
    {P : Set V} (hP₀ : {v | G.matchingKey M score v < t} ⊆ P) :
    let P₀ := {v | G.matchingKey M score v < t}
    ((G.edgeCut P).ncard : ℝ) - (1 - lam) * ((G.activeCleanPairs M M_clean score P).ncard : ℝ) ≤
      G.weightedMatchingCost M M_clean lam score t + 3 * ((P \ P₀).ncard : ℝ) := by
  classical
  intro P₀
  set S_both : Set E := {e | e ∈ M_clean ∧ G.PairStraddlesBoth score t e}
  set S₁ : Set E := {e | e ∈ M_clean ∧ G.PairStraddlesBoth score t e ∧
    G.outerHigh score (G.src e) e ∈ G.edgeCut P ∧
    G.outerHigh score (G.tgt e) e ∈ G.edgeCut P}
  set S₂ : Set E := {e | e ∈ M_clean ∧ G.PairStraddlesBoth score t e ∧
    ¬(G.outerHigh score (G.src e) e ∈ G.edgeCut P ∧
      G.outerHigh score (G.tgt e) e ∈ G.edgeCut P)}
  have hS₁_sub : S₁ ⊆ G.activeCleanPairs M M_clean score P := by
    intro e ⟨he_cl, hboth, hb_cut, hd_cut⟩
    obtain ⟨-, -, hkey_eq, hks_lt, hkt_lt⟩ :=
      pairStraddlesBoth_spec hloop h3 hM score t (hclean he_cl) hboth
    exact ⟨he_cl, hkey_eq, hP₀ hks_lt, hP₀ hkt_lt, hb_cut, hd_cut⟩
  have hS_part : S₁.ncard + S₂.ncard = S_both.ncard := by
    have hu : S₁ ∪ S₂ = S_both := by
      ext e
      simp only [S₁, S₂, S_both, mem_union, mem_ofPred_eq]
      tauto
    have hd : Disjoint S₁ S₂ := Set.disjoint_left.mpr fun e h1 h2 => h2.2.2 h1.2.2
    rw [← hu, ncard_union_eq hd]
  have hM_part : {e | e ∈ M ∧ G.PairStraddlesBoth score t e}.ncard =
      {e | e ∈ M \ M_clean ∧ G.PairStraddlesBoth score t e}.ncard + S_both.ncard := by
    have hu : {e | e ∈ M \ M_clean ∧ G.PairStraddlesBoth score t e} ∪ S_both =
        {e | e ∈ M ∧ G.PairStraddlesBoth score t e} := by
      ext e
      simp only [S_both, mem_union, mem_ofPred_eq, mem_sdiff]
      exact ⟨fun h => h.elim (fun h1 => ⟨h1.1.1, h1.2⟩) (fun h2 => ⟨hclean h2.1, h2.2⟩),
        fun ⟨heM, hb⟩ => if hc : e ∈ M_clean then Or.inr ⟨hc, hb⟩ else Or.inl ⟨⟨heM, hc⟩, hb⟩⟩
    have hd : Disjoint {e | e ∈ M \ M_clean ∧ G.PairStraddlesBoth score t e} S_both :=
      Set.disjoint_left.mpr fun e h1 h2 => h1.1.2 h2.1
    rw [← hu, ncard_union_eq hd]
  have hnat : (G.edgeCut P).ncard + S₂.ncard ≤
      G.matchingCost M score t + 3 * (P \ P₀).ncard :=
    ncard_edgeCut_add_inactive_le_matchingCost hloop h3 hM hclean score t hP₀
  have hnatR : ((G.edgeCut P).ncard : ℝ) + (S₂.ncard : ℝ) ≤
      (G.matchingCost M score t : ℝ) + 3 * ((P \ P₀).ncard : ℝ) := by exact_mod_cast hnat
  have hS₁_le : (S₁.ncard : ℝ) ≤ ((G.activeCleanPairs M M_clean score P).ncard : ℝ) := by
    exact_mod_cast ncard_le_ncard hS₁_sub
  have hS_partR : (S₁.ncard : ℝ) + (S₂.ncard : ℝ) = (S_both.ncard : ℝ) := by
    exact_mod_cast hS_part
  have hcost_eq : (G.matchingCost M score t : ℝ) - (1 - lam) * (S_both.ncard : ℝ) =
      G.weightedMatchingCost M M_clean lam score t := by
    unfold matchingCost weightedMatchingCost
    rw [hM_part]
    push_cast
    ring
  have h1lam : 0 ≤ 1 - lam := by linarith
  have hS₂_mul : (1 - lam) * (S₂.ncard : ℝ) ≤ (S₂.ncard : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) S₂.ncard]
  have hS₁_mul : (1 - lam) * (S₁.ncard : ℝ) ≤
      (1 - lam) * ((G.activeCleanPairs M M_clean score P).ncard : ℝ) := by gcongr
  have hsplit_mul : (1 - lam) * (S_both.ncard : ℝ) =
      (1 - lam) * (S₁.ncard : ℝ) + (1 - lam) * (S₂.ncard : ℝ) := by
    rw [← hS_partR, mul_add]
  linarith

/-- Clean matched edges whose endpoints share the same `matchingKey`. -/
@[expose]
def equalKeyPairs (G : Multigraph V E) (M M_clean : Set E) (score : E → ℝ) : Set E :=
  {e | e ∈ M_clean ∧ G.matchingKey M score (G.src e) = G.matchingKey M score (G.tgt e)}

/-- Super-nodes contracting each equal-key clean matched edge into one node while keeping all
remaining vertices individual. -/
abbrev PairNode (G : Multigraph V E) (M M_clean : Set E) (score : E → ℝ) : Type _ :=
  {v : V // v ∉ G.matchedVertices (G.equalKeyPairs M M_clean score)} ⊕
    ↑(G.equalKeyPairs M M_clean score)

/-- Key assigned to each `PairNode`: `matchingKey` on individual vertices and the shared endpoint
`matchingKey` on equal-key clean pairs. -/
noncomputable def pairNodeKey (G : Multigraph V E) (M M_clean : Set E) (score : E → ℝ) :
    G.PairNode M M_clean score → ℝ
  | .inl v => G.matchingKey M score v.1
  | .inr e => G.matchingKey M score (G.src e.1)

/-- Vertex subset of `V` expanded from a set of `PairNode`s. -/
@[expose]
def pairNodeVerts (G : Multigraph V E) (M M_clean : Set E) (score : E → ℝ)
    (S : Set (G.PairNode M M_clean score)) : Set V :=
  {v | (∃ hv : v ∉ G.matchedVertices (G.equalKeyPairs M M_clean score), .inl ⟨v, hv⟩ ∈ S) ∨
    ∃ e : G.equalKeyPairs M M_clean score, (G.src e.1 = v ∨ G.tgt e.1 = v) ∧ .inr e ∈ S}

theorem mem_pairNodeVerts_of_notMem {G : Multigraph V E} {M M_clean : Set E} {score : E → ℝ}
    {S : Set (G.PairNode M M_clean score)} {v : V}
    (hv : v ∉ G.matchedVertices (G.equalKeyPairs M M_clean score)) :
    v ∈ G.pairNodeVerts M M_clean score S ↔ .inl ⟨v, hv⟩ ∈ S := by
  simp only [pairNodeVerts, mem_ofPred_eq]
  exact ⟨fun h => h.elim (fun ⟨_, hm⟩ => hm) (fun ⟨e, hev, _⟩ => (hv ⟨e.1, e.2, hev⟩).elim),
    fun hm => Or.inl ⟨hv, hm⟩⟩

theorem mem_pairNodeVerts_of_mem {G : Multigraph V E} {M M_clean : Set E}
    (hM : G.IsMatching M) (hclean : M_clean ⊆ M) {score : E → ℝ}
    {S : Set (G.PairNode M M_clean score)} (e : G.equalKeyPairs M M_clean score) {v : V}
    (hev : G.src e.1 = v ∨ G.tgt e.1 = v) :
    v ∈ G.pairNodeVerts M M_clean score S ↔ .inr e ∈ S := by
  have hv_mat : v ∈ G.matchedVertices (G.equalKeyPairs M M_clean score) := ⟨e.1, e.2, hev⟩
  simp only [pairNodeVerts, mem_ofPred_eq]
  refine ⟨fun h => ?_, fun hm => Or.inr ⟨e, hev, hm⟩⟩
  rcases h with ⟨hnot, _⟩ | ⟨e', he'v, hm⟩
  · exact (hnot hv_mat).elim
  · suffices h_eq : e' = e by rwa [h_eq] at hm
    by_contra hne
    have hne_val : e'.1 ≠ e.1 := fun h => hne (Subtype.ext h)
    exact Set.disjoint_left.mp (hM (hclean e'.2.1) (hclean e.2.1) hne_val)
      (he'v.imp Eq.symm Eq.symm) (hev.imp Eq.symm Eq.symm)

/-- **Grid bound on `PairNode` prefixes.** Sorting `PairNode G M M_clean score` by `pairNodeKey`
yields a layout `σ` whose every expanded prefix `P = pairNodeVerts (σ.initial s)` satisfies
`|edgeCut P| - (1 - lam) |activeCleanPairs P| ≤ B` over any grid `a, a + δ, ..., a + K δ`. -/
theorem exists_u2_pairNode_layout [Finite V] [Finite E]
    {G : Multigraph V E} (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M M_clean : Set E} (hM : G.IsMatching M) (hclean : M_clean ⊆ M)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (score : E → ℝ)
    {a δ : ℝ} (hδ : 0 < δ) (K : ℕ) {B : ℝ}
    (low : 12 * ({e | score e < a}.ncard : ℝ) ≤ B)
    (high : 12 * ({e | a + K * δ ≤ score e}.ncard : ℝ) ≤ B)
    (mid : ∀ i < K, G.weightedMatchingCost M M_clean lam score (a + i * δ) +
      12 * ({e | a + i * δ ≤ score e ∧ score e < a + (i + 1) * δ}.ncard : ℝ) ≤ B) :
    ∃ σ : Layout (G.PairNode M M_clean score), ∀ s : ℕ,
      let P := G.pairNodeVerts M M_clean score (σ.initial s)
      ((G.edgeCut P).ncard : ℝ) - (1 - lam) * ((G.activeCleanPairs M M_clean score P).ncard : ℝ) ≤
        B := by
  have hB0 : 0 ≤ B := le_trans (by positivity) low
  have h1lam : 0 ≤ 1 - lam := by linarith
  have := Finite.of_injective
    (fun x : {v : V // v ∉ G.matchedVertices (G.equalKeyPairs M M_clean score)} => x.1)
    Subtype.val_injective
  obtain ⟨σ, hσ⟩ := Layout.exists_threshold (G.pairNodeKey M M_clean score)
  refine ⟨σ, fun s => ?_⟩
  intro P
  rcases lt_or_ge s (Nat.card (G.PairNode M M_clean score)) with hs | hs
  · obtain ⟨m, hm_le, hm_ge⟩ := hσ s hs
    have hP_le : ∀ v ∈ P, G.matchingKey M score v ≤ m := by
      intro v hv
      by_cases hv_mat : v ∈ G.matchedVertices (G.equalKeyPairs M M_clean score)
      · obtain ⟨e, he_eq, hev⟩ := hv_mat
        have hinr : .inr ⟨e, he_eq⟩ ∈ σ.initial s :=
          (mem_pairNodeVerts_of_mem hM hclean ⟨e, he_eq⟩ hev).mp hv
        have hk := hm_le (.inr ⟨e, he_eq⟩) hinr
        dsimp only [pairNodeKey] at hk
        rcases hev with rfl | rfl
        · exact hk
        · rwa [← he_eq.2]
      · have hinl : .inl ⟨v, hv_mat⟩ ∈ σ.initial s :=
          (mem_pairNodeVerts_of_notMem hv_mat).mp hv
        exact hm_le (.inl ⟨v, hv_mat⟩) hinl
    have hP_ge : ∀ v ∉ P, m ≤ G.matchingKey M score v := by
      intro v hv
      by_cases hv_mat : v ∈ G.matchedVertices (G.equalKeyPairs M M_clean score)
      · obtain ⟨e, he_eq, hev⟩ := hv_mat
        have hinr : .inr ⟨e, he_eq⟩ ∉ σ.initial s := fun h =>
          hv ((mem_pairNodeVerts_of_mem hM hclean ⟨e, he_eq⟩ hev).mpr h)
        have hk := hm_ge (.inr ⟨e, he_eq⟩) hinr
        dsimp only [pairNodeKey] at hk
        rcases hev with rfl | rfl
        · exact hk
        · rwa [← he_eq.2]
      · have hinl : .inl ⟨v, hv_mat⟩ ∉ σ.initial s := fun h =>
          hv ((mem_pairNodeVerts_of_notMem hv_mat).mpr h)
        exact hm_ge (.inl ⟨v, hv_mat⟩) hinl
    exact G.le_of_matchingKey_separated_grid hloop h3 hM score hP_le hP_ge
      (sub_le_self _ (mul_nonneg h1lam (Nat.cast_nonneg _))) hδ
      (G.weightedMatchingCost M M_clean lam score)
      (fun t hP₀ =>
        ncard_edgeCut_sub_active_le_weightedMatchingCost hloop h3 hM hclean hlam0 hlam1 score t hP₀)
      low high mid
  · have hinit : σ.initial s = univ := σ.initial_of_card_le hs
    have hP_univ : P = univ := by
      ext v
      simp only [mem_univ, iff_true]
      by_cases hv_mat : v ∈ G.matchedVertices (G.equalKeyPairs M M_clean score)
      · obtain ⟨e, he_eq, hev⟩ := hv_mat
        exact (mem_pairNodeVerts_of_mem hM hclean ⟨e, he_eq⟩ hev).mpr (by simp [hinit])
      · exact (mem_pairNodeVerts_of_notMem hv_mat).mpr (by simp [hinit])
    have hcut0 : G.edgeCut P = ∅ := by ext e; simp [hP_univ]
    have hact0 : G.activeCleanPairs M M_clean score P = ∅ := by
      ext e; simp [activeCleanPairs, hcut0]
    simp only [hcut0, hact0, ncard_empty, Nat.cast_zero, mul_zero, sub_zero]
    exact hB0

end WeightedMatching

end Cslib.Circuits.Frontier.Multigraph

namespace Cslib.Circuits.Frontier

/-- **`U₂` cubic pair-node layout hypothesis** with unmatched per-vertex cost `p` and per-matched
clean-pair cost `B_pair` at weight `λ = log₂ 3 - 1` (`1 - λ = 2 - log₂ 3`). -/
@[expose]
def U2CubicPairBound (p B_pair : ℝ) : Prop :=
  ∀ ξ > 0, ∃ N₀ : ℕ, ∀ (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
    G.Loopless → G.ends.Injective → (∀ v, (G.incidenceSet v).ncard = 3) →
    N₀ < Nat.card V → ∀ (M M_clean : Set E), G.IsMatching M → M_clean ⊆ M →
      ∃ (score : E → ℝ) (σ : Layout (G.PairNode M M_clean score)),
        ∀ t : ℕ,
          let P := G.pairNodeVerts M M_clean score (σ.initial t)
          ((G.edgeCut P).ncard : ℝ) -
              (2 - Real.logb 2 3) * ((G.activeCleanPairs M M_clean score P).ncard : ℝ) ≤
            ((Nat.card V : ℝ) - 2 * M_clean.ncard) * p + (M_clean.ncard : ℝ) * B_pair +
              ξ * Nat.card V


end Cslib.Circuits.Frontier
