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
      G.matchingKey M score (G.tgt e) = pairKey (score c) (score d) (score a) (score b) := by
  classical
  have hbs := outerLow_outerHigh_spec h3 score (v := G.src e) (Or.inl rfl)
  have hdt := outerLow_outerHigh_spec h3 score (v := G.tgt e) (Or.inr rfl)
  set a := G.outerLow score (G.src e) e
  set b := G.outerHigh score (G.src e) e
  set c := G.outerLow score (G.tgt e) e
  set d := G.outerHigh score (G.tgt e) e
  have eq_match {e' f : E} (he' : e' ∈ M) (hf : f ∈ M) {v : V}
      (he'v : e' ∈ G.incidenceSet v) (hfv : f ∈ G.incidenceSet v) : e' = f := by
    by_contra hne
    exact Set.disjoint_left.mp (hM he' hf hne)
      (he'v.imp Eq.symm Eq.symm) (hfv.imp Eq.symm Eq.symm)
  have hex_s : ∃ f ∈ M, f ∈ G.incidenceSet (G.src e) := ⟨e, heM, Or.inl rfl⟩
  have hex_t : ∃ f ∈ M, f ∈ G.incidenceSet (G.tgt e) := ⟨e, heM, Or.inr rfl⟩
  have huniq_s : hex_s.choose = e :=
    eq_match hex_s.choose_spec.1 heM hex_s.choose_spec.2 (Or.inl rfl)
  have huniq_t : hex_t.choose = e :=
    eq_match hex_t.choose_spec.1 heM hex_t.choose_spec.2 (Or.inr rfl)
  have hns : (G.incidenceSet (G.src e) \ {e}).ncard = 2 := by rw [hbs.2.1, ncard_pair hbs.1]
  have hnt : (G.incidenceSet (G.tgt e) \ {e}).ncard = 2 := by rw [hdt.2.1, ncard_pair hdt.1]
  have pair_eq {p₁ q₁ p₂ q₂ x₁ y₁ x₂ y₂ : E} (h1 : ({x₁, y₁} : Set E) = {p₁, q₁})
      (hne1 : p₁ ≠ q₁) (h2 : ({x₂, y₂} : Set E) = {p₂, q₂}) (hne2 : p₂ ≠ q₂) :
      pairKey (score p₁) (score q₁) (score p₂) (score q₂) =
        pairKey (score x₁) (score y₁) (score x₂) (score y₂) := by
    have hm1 : p₁ = x₁ ∨ p₁ = y₁ := by
      have : p₁ ∈ ({x₁, y₁} : Set E) := h1 ▸ by simp
      simpa using this
    have hm1' : q₁ = x₁ ∨ q₁ = y₁ := by
      have : q₁ ∈ ({x₁, y₁} : Set E) := h1 ▸ by simp
      simpa using this
    have hm2 : p₂ = x₂ ∨ p₂ = y₂ := by
      have : p₂ ∈ ({x₂, y₂} : Set E) := h2 ▸ by simp
      simpa using this
    have hm2' : q₂ = x₂ ∨ q₂ = y₂ := by
      have : q₂ ∈ ({x₂, y₂} : Set E) := h2 ▸ by simp
      simpa using this
    have hright (u v : ℝ) :
        pairKey u v (score p₂) (score q₂) = pairKey u v (score x₂) (score y₂) := by
      rcases hm2 with rfl | rfl <;> rcases hm2' with rfl | rfl
      · exact (hne2 rfl).elim
      · rfl
      · exact pairKey_comm_right _ _ _ _
      · exact (hne2 rfl).elim
    rcases hm1 with rfl | rfl <;> rcases hm1' with rfl | rfl
    · exact (hne1 rfl).elim
    · exact hright _ _
    · rw [pairKey_comm_left]; exact hright _ _
    · exact (hne1 rfl).elim
  constructor
  · have hhs : (G.incidenceSet (G.src e) \ {hex_s.choose}).ncard = 2 ∧
        (G.incidenceSet
          (if G.src hex_s.choose = G.src e then G.tgt hex_s.choose else G.src hex_s.choose) \
          {hex_s.choose}).ncard = 2 := by
      simp only [huniq_s, ↓reduceIte]; exact ⟨hns, hnt⟩
    simp only [matchingKey, hex_s, ↓reduceDIte, hhs]
    have hp := (ncard_eq_two.mp hhs.1).choose_spec.choose_spec
    have hq := (ncard_eq_two.mp hhs.2).choose_spec.choose_spec
    exact pair_eq (hbs.2.1.symm.trans (by simpa [huniq_s] using hp.2)) hp.1
      (hdt.2.1.symm.trans (by simpa [huniq_s] using hq.2)) hq.1
  · have hht : (G.incidenceSet (G.tgt e) \ {hex_t.choose}).ncard = 2 ∧
        (G.incidenceSet
          (if G.src hex_t.choose = G.tgt e then G.tgt hex_t.choose else G.src hex_t.choose) \
          {hex_t.choose}).ncard = 2 := by
      simp only [huniq_t, hloop e, ↓reduceIte]; exact ⟨hnt, hns⟩
    simp only [matchingKey, hex_t, ↓reduceDIte, hht]
    have hp := (ncard_eq_two.mp hht.1).choose_spec.choose_spec
    have hq := (ncard_eq_two.mp hht.2).choose_spec.choose_spec
    exact pair_eq (hdt.2.1.symm.trans (by simpa [huniq_t] using hp.2)) hp.1
      (hbs.2.1.symm.trans (by simpa [huniq_t, hloop e] using hq.2)) hq.1

private theorem boolDiff_slack (x y m : Bool) :
    (if x = y then 0 else 1) + 2 * (if x = true ∧ y = true ∧ m = false then 1 else 0) ≤
      (if x = m then 0 else 1) + (if y = m then 0 else 1) := by
  cases x <;> cases y <;> cases m <;> decide

/-- Refined threshold cut inequality at `P₀`: unmatched edges with both endpoints in `P₀` and
`t ≤ score f` yield `2` units of slack against `G.matchingCost M score t`. -/
private theorem ncard_edgeCut_threshold_add_slack_le_matchingCost [Finite V] [Finite E]
    {G : Multigraph V E} (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M : Set E} (hM : G.IsMatching M) (score : E → ℝ) (t : ℝ) :
    let P₀ := {v | G.matchingKey M score v < t}
    (G.edgeCut P₀).ncard +
      2 * {f | f ∉ M ∧ G.src f ∈ P₀ ∧ G.tgt f ∈ P₀ ∧ t ≤ score f}.ncard ≤
      G.matchingCost M score t := by
  classical
  intro P₀
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  let col : V → Bool := fun v => decide (G.matchingKey M score v < t)
  let ecol : E → Bool := fun e => decide (score e < t)
  let bdiff (x y : Bool) : ℕ := if x = y then 0 else 1
  let slack (e : E) : ℕ :=
    if col (G.src e) = true ∧ col (G.tgt e) = true ∧ ecol e = false then 1 else 0
  let Mfin : Finset E := Finset.univ.filter (· ∈ M)
  have hcut : (G.edgeCut P₀).ncard = ∑ e : E, bdiff (col (G.src e)) (col (G.tgt e)) := by
    have hset : G.edgeCut P₀ = ((Finset.univ.filter (· ∈ G.edgeCut P₀)) : Set E) := by
      ext e; simp
    rw [hset, ncard_coe_finset, Finset.card_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [P₀, col, bdiff, mem_edgeCut, mem_ofPred_eq]
    by_cases hs : G.matchingKey M score (G.src e) < t <;>
      by_cases ht : G.matchingKey M score (G.tgt e) < t <;> simp [hs, ht]
  have hslack : {f | f ∉ M ∧ G.src f ∈ P₀ ∧ G.tgt f ∈ P₀ ∧ t ≤ score f}.ncard =
      ∑ e ∈ Mfinᶜ, slack e := by
    have hset : {f | f ∉ M ∧ G.src f ∈ P₀ ∧ G.tgt f ∈ P₀ ∧ t ≤ score f} =
        ((Mfinᶜ.filter fun e => slack e = 1) : Set E) := by
      ext e
      simp only [mem_ofPred_eq, Finset.coe_filter, Finset.mem_compl, Mfin, Finset.mem_filter,
        Finset.mem_univ, true_and, slack, col, ecol, P₀, decide_eq_true_eq,
        decide_eq_false_iff_not, not_lt]
      constructor
      · rintro ⟨hm, hs, ht, hsc⟩
        exact ⟨hm, ite_eq_left ⟨hs, ht, hsc⟩⟩
      · rintro ⟨hm, h1⟩
        refine ⟨hm, ?_⟩
        by_contra hnot
        have h0 : (if G.matchingKey M score (G.src e) < t ∧
            G.matchingKey M score (G.tgt e) < t ∧ t ≤ score e then 1 else 0) = 0 :=
          ite_eq_right hnot
        omega
    rw [hset, ncard_coe_finset, Finset.card_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    dsimp only [slack]
    split_ifs <;> omega
  have hstep1 : (∑ e : E, bdiff (col (G.src e)) (col (G.tgt e))) + 2 * ∑ e ∈ Mfinᶜ, slack e ≤
      (∑ e ∈ Mfin, bdiff (col (G.src e)) (col (G.tgt e))) +
      ∑ e ∈ Mfinᶜ, (bdiff (col (G.src e)) (ecol e) + bdiff (col (G.tgt e)) (ecol e)) := by
    rw [← (Finset.sum_add_sum_compl Mfin (fun e => bdiff (col (G.src e)) (col (G.tgt e)))),
      add_assoc, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Nat.add_le_add_left (Finset.sum_le_sum fun e _ => boolDiff_slack _ _ _) _
  -- Reuse the exact RHS identity from `ncard_edgeCut_threshold_le_matchingCost` by comparing with
  -- a virtual graph or evaluating the endpoint sum directly.
  have hgroup :
      ∑ e ∈ Mfinᶜ, (bdiff (col (G.src e)) (ecol e) + bdiff (col (G.tgt e)) (ecol e)) =
      ∑ v : V, ∑ e ∈ Finset.univ.filter (fun e => e ∉ M ∧ e ∈ G.incidenceSet v),
        bdiff (col v) (ecol e) := by
    have hinner (e : E) :
        bdiff (col (G.src e)) (ecol e) + bdiff (col (G.tgt e)) (ecol e) =
        ∑ v : V, if e ∈ G.incidenceSet v then bdiff (col v) (ecol e) else 0 := by
      have hpair : (Finset.univ.filter fun v : V => e ∈ G.incidenceSet v) =
          {G.src e, G.tgt e} := by ext v; simp [mem_incidenceSet, eq_comm]
      rw [← Finset.sum_filter, hpair, Finset.sum_pair (hloop e)]
    have hmf : Mfinᶜ = Finset.univ.filter (· ∉ M) := by ext e; simp [Mfin]
    rw [hmf, Finset.sum_filter]
    calc ∑ e : E, (if e ∉ M then bdiff (col (G.src e)) (ecol e) +
            bdiff (col (G.tgt e)) (ecol e) else 0)
        = ∑ e : E, ∑ v : V, if e ∉ M ∧ e ∈ G.incidenceSet v then bdiff (col v) (ecol e) else 0 := by
          refine Finset.sum_congr rfl fun e _ => ?_
          by_cases he : e ∈ M <;> simp [he, hinner]
      _ = ∑ v : V, ∑ e : E, if e ∉ M ∧ e ∈ G.incidenceSet v then bdiff (col v) (ecol e) else 0 :=
          Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun v _ => (Finset.sum_filter _ _).symm
  let vsum (v : V) : ℕ :=
    ∑ e ∈ Finset.univ.filter (fun e => e ∉ M ∧ e ∈ G.incidenceSet v), bdiff (col v) (ecol e)
  have hpart_v : ∑ v : V, vsum v =
      (∑ v ∈ Finset.univ.filter (· ∉ G.matchedVertices M), vsum v) +
      ∑ e ∈ Mfin, (vsum (G.src e) + vsum (G.tgt e)) := by
    have hbi : Finset.univ.filter (· ∈ G.matchedVertices M) =
        Mfin.biUnion fun e => ({G.src e, G.tgt e} : Finset V) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, matchedVertices, mem_ofPred_eq,
        Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, mem_incidenceSet, Mfin]
      exact ⟨fun ⟨e, he, h⟩ => ⟨e, he, h.imp Eq.symm Eq.symm⟩,
        fun ⟨e, he, h⟩ => ⟨e, he, h.imp Eq.symm Eq.symm⟩⟩
    have hdisj : (Mfin : Set E).PairwiseDisjoint
        (fun e => ({G.src e, G.tgt e} : Finset V)) := fun e he f hf hne =>
      Finset.disjoint_left.mpr fun u hu hv => by
        exact Set.disjoint_left.mp (hM (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2 hne)
          (by simpa using hu) (by simpa using hv)
    have hcompl := (Finset.sum_add_sum_compl (Finset.univ.filter (· ∈ G.matchedVertices M))
      vsum).symm
    have hcf : (Finset.univ.filter (· ∈ G.matchedVertices M))ᶜ =
        Finset.univ.filter (· ∉ G.matchedVertices M) := by ext v; simp
    rw [hcompl, hcf, add_comm, hbi, Finset.sum_biUnion hdisj]
    exact congrArg _ (Finset.sum_congr rfl fun e _ => Finset.sum_pair (hloop e))
  have hsingle : ∑ v ∈ Finset.univ.filter (· ∉ G.matchedVertices M), vsum v ≤
      {v | v ∉ G.matchedVertices M ∧ G.EdgeStraddles score t v}.ncard := by
    have hset : {v | v ∉ G.matchedVertices M ∧ G.EdgeStraddles score t v} =
        ((Finset.univ.filter fun v => v ∉ G.matchedVertices M ∧ G.EdgeStraddles score t v) :
          Set V) := by ext v; simp
    rw [hset, ncard_coe_finset, Finset.card_filter, Finset.sum_filter]
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases hv : v ∉ G.matchedVertices M
    · rw [ite_eq_left hv]
      have hnc := h3 v
      have hex3 : ∃ e₀ e₁ e₂ : E, e₀ ≠ e₁ ∧ e₀ ≠ e₂ ∧ e₁ ≠ e₂ ∧ G.incidenceSet v = {e₀, e₁, e₂} ∧
          G.matchingKey M score v = median3 (score e₀) (score e₁) (score e₂) := by
        have hnot : ¬∃ e ∈ M, e ∈ G.incidenceSet v := hv
        simp only [matchingKey, hnot, ↓reduceDIte, hnc]
        exact ⟨_, _, _, (ncard_eq_three.mp hnc).choose_spec.choose_spec.choose_spec.1,
          (ncard_eq_three.mp hnc).choose_spec.choose_spec.choose_spec.2.1,
          (ncard_eq_three.mp hnc).choose_spec.choose_spec.choose_spec.2.2.1,
          (ncard_eq_three.mp hnc).choose_spec.choose_spec.choose_spec.2.2.2, rfl⟩
      obtain ⟨e₀, e₁, e₂, h01, h02, h12, hinc, hkey⟩ := hex3
      have hfilt : Finset.univ.filter (fun e => e ∉ M ∧ e ∈ G.incidenceSet v) = {e₀, e₁, e₂} := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        exact ⟨fun ⟨_, hm⟩ => by rwa [hinc] at hm,
          fun hm => ⟨fun heM => hv ⟨e, heM, by rwa [hinc]⟩, by rwa [hinc]⟩⟩
      dsimp only [vsum]
      have hn0 : e₀ ∉ ({e₁, e₂} : Finset E) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h01, h02⟩
      have hn1 : e₁ ∉ ({e₂} : Finset E) := by simp only [Finset.mem_singleton]; exact h12
      rw [hfilt, Finset.sum_insert hn0, Finset.sum_insert hn1, Finset.sum_singleton]
      have hcol : col v = decide (median3 (score e₀) (score e₁) (score e₂) < t) := by
        simp only [col, hkey]
      have hmed := starEnergy_median3 (score e₀) (score e₁) (score e₂) t
      have hiff : G.EdgeStraddles score t v ↔
          ¬(decide (score e₀ < t) = decide (score e₁ < t) ∧
            decide (score e₁ < t) = decide (score e₂ < t)) := by
        simp only [EdgeStraddles, StraddlesOn, hinc, mem_insert_iff, mem_singleton_iff]
        by_cases h0 : score e₀ < t <;> by_cases h1 : score e₁ < t <;>
          by_cases h2 : score e₂ < t <;> simp [h0, h1, h2, not_lt.mp]
      simp only [starEnergy, starCost] at hmed
      dsimp only [bdiff, ecol]
      rw [hcol, ← add_assoc, hmed]
      by_cases hs2 : G.EdgeStraddles score t v
      · have hrhs : (if v ∉ G.matchedVertices M ∧ G.EdgeStraddles score t v then 1 else 0) = 1 :=
          ite_eq_left ⟨hv, hs2⟩
        rw [hrhs]
        split_ifs with hs1
        · exact (hiff.mp hs2 hs1).elim
        · omega
      · have hrhs : (if v ∉ G.matchedVertices M ∧ G.EdgeStraddles score t v then 1 else 0) = 0 :=
          ite_eq_right fun h => hs2 h.2
        rw [hrhs]
        split_ifs with hs1
        · omega
        · exact (hs2 (hiff.mpr hs1)).elim
    · simp [hv]
  have hpair : ∑ e ∈ Mfin, (bdiff (col (G.src e)) (col (G.tgt e)) +
        (vsum (G.src e) + vsum (G.tgt e))) ≤
      {e | e ∈ M ∧ G.PairStraddlesAny score t e}.ncard +
        {e | e ∈ M ∧ G.PairStraddlesBoth score t e}.ncard := by
    have hcnt (Q : E → Prop) [DecidablePred Q] :
        {e | e ∈ M ∧ Q e}.ncard = ∑ e ∈ Mfin, if Q e then 1 else 0 := by
      have hs : {e | e ∈ M ∧ Q e} = ((Mfin.filter Q) : Set E) := by ext e; simp [Mfin]
      rw [hs, ncard_coe_finset, Finset.card_filter]
    rw [hcnt (G.PairStraddlesAny score t), hcnt (G.PairStraddlesBoth score t),
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun e he => ?_
    have heM : e ∈ M := (Finset.mem_filter.mp he).2
    have hbs := outerLow_outerHigh_spec h3 score (v := G.src e) (Or.inl rfl)
    have hdt := outerLow_outerHigh_spec h3 score (v := G.tgt e) (Or.inr rfl)
    set a := G.outerLow score (G.src e) e
    set b := G.outerHigh score (G.src e) e
    set c := G.outerLow score (G.tgt e) e
    set d := G.outerHigh score (G.tgt e) e
    have eq_match {e' f : E} (he' : e' ∈ M) (hf : f ∈ M) {v : V}
        (he'v : e' ∈ G.incidenceSet v) (hfv : f ∈ G.incidenceSet v) : e' = f := by
      by_contra hne
      exact Set.disjoint_left.mp (hM he' hf hne)
        (he'v.imp Eq.symm Eq.symm) (hfv.imp Eq.symm Eq.symm)
    have hfil_s : Finset.univ.filter (fun f => f ∉ M ∧ f ∈ G.incidenceSet (G.src e)) = {a, b} := by
      ext f
      have hd : f ∈ G.incidenceSet (G.src e) \ {e} ↔ f = a ∨ f = b := by simp [hbs.2.1]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, ← hd, mem_sdiff, mem_singleton_iff]
      exact ⟨fun ⟨hfM, hfi⟩ => ⟨hfi, fun hfe => hfM (hfe ▸ heM)⟩,
        fun ⟨hfi, hfe⟩ => ⟨fun hfM => hfe (eq_match hfM heM hfi (Or.inl rfl)), hfi⟩⟩
    have hfil_t : Finset.univ.filter (fun f => f ∉ M ∧ f ∈ G.incidenceSet (G.tgt e)) = {c, d} := by
      ext f
      have hd : f ∈ G.incidenceSet (G.tgt e) \ {e} ↔ f = c ∨ f = d := by simp [hdt.2.1]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, ← hd, mem_sdiff, mem_singleton_iff]
      exact ⟨fun ⟨hfM, hfi⟩ => ⟨hfi, fun hfe => hfM (hfe ▸ heM)⟩,
        fun ⟨hfi, hfe⟩ => ⟨fun hfM => hfe (eq_match hfM heM hfi (Or.inr rfl)), hfi⟩⟩
    obtain ⟨hks, hkt⟩ := matchingKey_outer hloop h3 hM score heM
    change G.matchingKey M score (G.src e) = pairKey (score a) (score b) (score c) (score d) at hks
    change G.matchingKey M score (G.tgt e) = pairKey (score c) (score d) (score a) (score b) at hkt
    have hsval : vsum (G.src e) = bdiff (col (G.src e)) (ecol a) + bdiff (col (G.src e)) (ecol b) :=
      by dsimp [vsum]; rw [hfil_s, Finset.sum_pair hbs.1]
    have htval : vsum (G.tgt e) = bdiff (col (G.tgt e)) (ecol c) + bdiff (col (G.tgt e)) (ecol d) :=
      by dsimp [vsum]; rw [hfil_t, Finset.sum_pair hdt.1]
    have henergy := twoVertexEnergy_pairKey (score a) (score b) (score c) (score d) t
    have hany : G.PairStraddlesAny score t e ↔
        ¬(decide (score a < t) = decide (score b < t) ∧
          decide (score b < t) = decide (score c < t) ∧
          decide (score c < t) = decide (score d < t)) := by
      simp only [PairStraddlesAny, StraddlesOn, hbs.2.1, hdt.2.1, mem_union, mem_insert_iff,
        mem_singleton_iff]
      have hex (p : E → Prop) : (∃ f, ((f = a ∨ f = b) ∨ f = c ∨ f = d) ∧ p f) ↔
          p a ∨ p b ∨ p c ∨ p d :=
        ⟨fun ⟨f, h, hp⟩ => by rcases h with (rfl | rfl) | (rfl | rfl) <;> simp [hp],
          by rintro (hp | hp | hp | hp); exacts [⟨a, Or.inl (Or.inl rfl), hp⟩,
            ⟨b, Or.inl (Or.inr rfl), hp⟩, ⟨c, Or.inr (Or.inl rfl), hp⟩,
            ⟨d, Or.inr (Or.inr rfl), hp⟩]⟩
      rw [hex (score · < t), hex (t ≤ score ·)]
      by_cases ha : score a < t <;> by_cases hb : score b < t <;>
        by_cases hc : score c < t <;> by_cases hd : score d < t <;>
        simp [ha, hb, hc, hd, not_lt.mp]
    have hboth : G.PairStraddlesBoth score t e ↔
        (decide (score a < t) ≠ decide (score b < t) ∧
          decide (score c < t) ≠ decide (score d < t)) := by
      simp only [PairStraddlesBoth, StraddlesOn, hbs.2.1, hdt.2.1, mem_insert_iff,
        mem_singleton_iff]
      by_cases ha : score a < t <;> by_cases hb : score b < t <;>
        by_cases hc : score c < t <;> by_cases hd : score d < t <;>
        simp [ha, hb, hc, hd, not_lt.mp]
    rw [hsval, htval]
    simp only [twoVertexEnergy, twoVertexCost] at henergy
    have hlhs : bdiff (col (G.src e)) (col (G.tgt e)) +
        (bdiff (col (G.src e)) (ecol a) + bdiff (col (G.src e)) (ecol b) +
          (bdiff (col (G.tgt e)) (ecol c) + bdiff (col (G.tgt e)) (ecol d))) =
        twoVertexCost (ecol a) (ecol b) (ecol c) (ecol d) := by
      simp only [twoVertexCost, bdiff, col, ecol, hks, hkt]
      omega
    rw [hlhs]
    simp only [twoVertexCost, ecol]
    have h1 : (if (decide (score a < t) = decide (score b < t) ∧
        decide (score b < t) = decide (score c < t) ∧
        decide (score c < t) = decide (score d < t)) then 0 else 1) =
        if G.PairStraddlesAny score t e then 1 else 0 := by
      split_ifs with g1 g2 g2
      · exact (hany.mp g2 g1).elim
      · rfl
      · rfl
      · exact (g2 (hany.mpr g1)).elim
    have h2 : (if decide (score a < t) ≠ decide (score b < t) ∧
        decide (score c < t) ≠ decide (score d < t) then 1 else 0) =
        if G.PairStraddlesBoth score t e then 1 else 0 := by
      split_ifs with g1 g2 g2
      · rfl
      · exact (g2 (hboth.mpr g1)).elim
      · exact (g1 (hboth.mp g2)).elim
      · rfl
    omega
  rw [hcut, hslack, matchingCost]
  calc (∑ e : E, bdiff (col (G.src e)) (col (G.tgt e))) + 2 * ∑ e ∈ Mfinᶜ, slack e
      ≤ (∑ e ∈ Mfin, bdiff (col (G.src e)) (col (G.tgt e))) +
          ∑ e ∈ Mfinᶜ, (bdiff (col (G.src e)) (ecol e) + bdiff (col (G.tgt e)) (ecol e)) := hstep1
    _ = (∑ v ∈ Finset.univ.filter (· ∉ G.matchedVertices M), vsum v) +
          ∑ e ∈ Mfin, (bdiff (col (G.src e)) (col (G.tgt e)) +
            (vsum (G.src e) + vsum (G.tgt e))) := by
        rw [hgroup]
        change (∑ e ∈ Mfin, bdiff (col (G.src e)) (col (G.tgt e))) + ∑ v : V, vsum v = _
        rw [hpart_v, add_left_comm, ← Finset.sum_add_distrib]
    _ ≤ _ := by
        have := Nat.add_le_add hsingle hpair
        omega

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
      (1 - lam) * ((G.activeCleanPairs M M_clean score P).ncard : ℝ) :=
    mul_le_mul_of_nonneg_left hS₁_le h1lam
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

private theorem ncard_matchingKey_pred_le_four [Finite V] [Finite E] {G : Multigraph V E}
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M : Set E} (hM : G.IsMatching M) (score : E → ℝ) (p : ℝ → Prop) :
    {v | p (G.matchingKey M score v)}.ncard ≤ 4 * {e | p (score e)}.ncard := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  let Efin : Finset E := Finset.univ.filter fun e => p (score e)
  let mateOrSelf (u : V) : V :=
    if h : ∃ e ∈ M, e ∈ G.incidenceSet u then
      if G.src h.choose = u then G.tgt h.choose else G.src h.choose
    else u
  let hit (e : E) : Finset V :=
    {G.src e, G.tgt e, mateOrSelf (G.src e), mateOrSelf (G.tgt e)}
  have eq_match {e' f : E} (he' : e' ∈ M) (hf : f ∈ M) {v : V}
      (he'v : e' ∈ G.incidenceSet v) (hfv : f ∈ G.incidenceSet v) : e' = f := by
    by_contra hne
    exact Set.disjoint_left.mp (hM he' hf hne)
      (he'v.imp Eq.symm Eq.symm) (hfv.imp Eq.symm Eq.symm)
  have hmate_src {e : E} (heM : e ∈ M) : mateOrSelf (G.src e) = G.tgt e := by
    have hex : ∃ f ∈ M, f ∈ G.incidenceSet (G.src e) := ⟨e, heM, Or.inl rfl⟩
    have hch : hex.choose = e := eq_match hex.choose_spec.1 heM hex.choose_spec.2 (Or.inl rfl)
    dsimp only [mateOrSelf]
    rw [dite_eq_left hex]
    simp only [hch, ↓reduceIte]
  have hmate_tgt {e : E} (heM : e ∈ M) : mateOrSelf (G.tgt e) = G.src e := by
    have hex : ∃ f ∈ M, f ∈ G.incidenceSet (G.tgt e) := ⟨e, heM, Or.inr rfl⟩
    have hch : hex.choose = e := eq_match hex.choose_spec.1 heM hex.choose_spec.2 (Or.inr rfl)
    dsimp only [mateOrSelf]
    rw [dite_eq_left hex]
    simp only [hch, hloop e, ↓reduceIte]
  have hsub : (Finset.univ.filter fun v => p (G.matchingKey M score v)) ⊆ Efin.biUnion hit := by
    intro v hv
    have hpv : p (G.matchingKey M score v) := (Finset.mem_filter.mp hv).2
    by_cases hmat : v ∈ G.matchedVertices M
    · obtain ⟨e, heM, hev⟩ := hmat
      have hbs := outerLow_outerHigh_spec h3 score (v := G.src e) (Or.inl rfl)
      have hdt := outerLow_outerHigh_spec h3 score (v := G.tgt e) (Or.inr rfl)
      obtain ⟨hks, hkt⟩ := matchingKey_outer hloop h3 hM score heM
      set a := G.outerLow score (G.src e) e
      set b := G.outerHigh score (G.src e) e
      set c := G.outerLow score (G.tgt e) e
      set d := G.outerHigh score (G.tgt e) e
      change G.matchingKey M score (G.src e) =
        pairKey (score a) (score b) (score c) (score d) at hks
      change G.matchingKey M score (G.tgt e) =
        pairKey (score c) (score d) (score a) (score b) at hkt
      have ha_inc : a ∈ G.incidenceSet (G.src e) :=
        ((show a ∈ G.incidenceSet (G.src e) \ {e} by rw [hbs.2.1]; simp)).1
      have hb_inc : b ∈ G.incidenceSet (G.src e) :=
        ((show b ∈ G.incidenceSet (G.src e) \ {e} by rw [hbs.2.1]; simp)).1
      have hc_inc : c ∈ G.incidenceSet (G.tgt e) :=
        ((show c ∈ G.incidenceSet (G.tgt e) \ {e} by rw [hdt.2.1]; simp)).1
      have hd_inc : d ∈ G.incidenceSet (G.tgt e) :=
        ((show d ∈ G.incidenceSet (G.tgt e) \ {e} by rw [hdt.2.1]; simp)).1
      have hit_self {u : V} {f : E} (hfu : f ∈ G.incidenceSet u) : u ∈ hit f := by
        rcases hfu with h | h <;> simp [hit, h]
      have hit_src_from_tgt {f : E} (hft : f ∈ G.incidenceSet (G.tgt e)) : G.src e ∈ hit f := by
        rcases hft with h | h <;> simp [hit, h, hmate_tgt heM]
      have hit_tgt_from_src {f : E} (hfs : f ∈ G.incidenceSet (G.src e)) : G.tgt e ∈ hit f := by
        rcases hfs with h | h <;> simp [hit, h, hmate_src heM]
      rcases hev with rfl | rfl
      · rw [hks] at hpv
        rcases pairKey_mem (score a) (score b) (score c) (score d) with h | h | h | h
        · exact Finset.mem_biUnion.mpr
            ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hit_self ha_inc⟩
        · exact Finset.mem_biUnion.mpr
            ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hit_self hb_inc⟩
        · exact Finset.mem_biUnion.mpr
            ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hit_src_from_tgt hc_inc⟩
        · exact Finset.mem_biUnion.mpr
            ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hit_src_from_tgt hd_inc⟩
      · rw [hkt] at hpv
        rcases pairKey_mem (score c) (score d) (score a) (score b) with h | h | h | h
        · exact Finset.mem_biUnion.mpr
            ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hit_self hc_inc⟩
        · exact Finset.mem_biUnion.mpr
            ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hit_self hd_inc⟩
        · exact Finset.mem_biUnion.mpr
            ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hit_tgt_from_src ha_inc⟩
        · exact Finset.mem_biUnion.mpr
            ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hit_tgt_from_src hb_inc⟩
    · have hnc := h3 v
      have hex3 : ∃ e₀ e₁ e₂ : E, G.incidenceSet v = {e₀, e₁, e₂} ∧
          G.matchingKey M score v = median3 (score e₀) (score e₁) (score e₂) := by
        have hnot : ¬∃ e ∈ M, e ∈ G.incidenceSet v := hmat
        simp only [matchingKey, hnot, ↓reduceDIte, hnc]
        exact ⟨_, _, _, (ncard_eq_three.mp hnc).choose_spec.choose_spec.choose_spec.2.2.2, rfl⟩
      obtain ⟨e₀, e₁, e₂, hinc, hkey⟩ := hex3
      rw [hkey] at hpv
      have hmed : median3 (score e₀) (score e₁) (score e₂) = score e₀ ∨
          median3 (score e₀) (score e₁) (score e₂) = score e₁ ∨
          median3 (score e₀) (score e₁) (score e₂) = score e₂ := by
        unfold median3
        rcases max_choice (min (score e₀) (score e₁)) (min (max (score e₀) (score e₁)) (score e₂))
          with h | h
        · rw [h]
          rcases min_choice (score e₀) (score e₁) with h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inl h')
        · rw [h]
          rcases min_choice (max (score e₀) (score e₁)) (score e₂) with h' | h'
          · rw [h']
            rcases max_choice (score e₀) (score e₁) with h'' | h''
            · exact Or.inl h''
            · exact Or.inr (Or.inl h'')
          · exact Or.inr (Or.inr h')
      have hit_v {f : E} (hfv : f ∈ G.incidenceSet v) : v ∈ hit f := by
        rcases hfv with h | h <;> simp [hit, h]
      rcases hmed with h | h | h
      · exact Finset.mem_biUnion.mpr
          ⟨e₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hit_v (by rw [hinc]; simp)⟩
      · exact Finset.mem_biUnion.mpr
          ⟨e₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hit_v (by rw [hinc]; simp)⟩
      · exact Finset.mem_biUnion.mpr
          ⟨e₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hit_v (by rw [hinc]; simp)⟩
  have hcard_hit (e : E) : (hit e).card ≤ 4 := by
    refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
    refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
    simp
  have h1 : {v | p (G.matchingKey M score v)}.ncard =
      (Finset.univ.filter fun v => p (G.matchingKey M score v)).card := by
    have : {v | p (G.matchingKey M score v)} =
        ((Finset.univ.filter fun v => p (G.matchingKey M score v)) : Set V) := by ext v; simp
    rw [this, ncard_coe_finset]
  have h2 : {e | p (score e)}.ncard = Efin.card := by
    have : {e | p (score e)} = (Efin : Set E) := by ext e; simp [Efin]
    rw [this, ncard_coe_finset]
  rw [h1, h2]
  calc (Finset.univ.filter fun v => p (G.matchingKey M score v)).card
      ≤ (Efin.biUnion hit).card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ Efin, (hit e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ Efin, 4 := Finset.sum_le_sum fun e _ => hcard_hit e
    _ = 4 * Efin.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

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
    have hnonneg_act : 0 ≤ (1 - lam) * ((G.activeCleanPairs M M_clean score P).ncard : ℝ) :=
      mul_nonneg h1lam (Nat.cast_nonneg _)
    rcases lt_or_ge m a with hlow | hge
    · have hsub : P ⊆ {v | G.matchingKey M score v < a} := fun v hv => (hP_le v hv).trans_lt hlow
      have hcut : (G.edgeCut P).ncard ≤ 12 * {e | score e < a}.ncard := by
        calc (G.edgeCut P).ncard
            ≤ (G.touching P).ncard := ncard_le_ncard (G.edgeCut_subset_touching P)
          _ ≤ 3 * P.ncard := G.ncard_touching_le (fun v => (h3 v).le) P
          _ ≤ 3 * {v | G.matchingKey M score v < a}.ncard :=
              Nat.mul_le_mul_left 3 (ncard_le_ncard hsub)
          _ ≤ 3 * (4 * {e | score e < a}.ncard) :=
              Nat.mul_le_mul_left 3 (ncard_matchingKey_pred_le_four hloop h3 hM score (· < a))
          _ = 12 * {e | score e < a}.ncard := by ring
      have hcutR : ((G.edgeCut P).ncard : ℝ) ≤ 12 * ({e | score e < a}.ncard : ℝ) := by
        exact_mod_cast hcut
      linarith
    set top := a + K * δ
    rcases le_or_gt top m with htop | hlt
    · have hsub : Pᶜ ⊆ {v | top ≤ G.matchingKey M score v} := fun v hv => htop.trans (hP_ge v hv)
      have hcompl : G.edgeCut P = G.edgeCut Pᶜ := by ext e; simp [mem_edgeCut, not_iff_not]
      have hcut : (G.edgeCut P).ncard ≤ 12 * {e | top ≤ score e}.ncard := by
        rw [hcompl]
        calc (G.edgeCut Pᶜ).ncard
            ≤ (G.touching Pᶜ).ncard := ncard_le_ncard (G.edgeCut_subset_touching Pᶜ)
          _ ≤ 3 * Pᶜ.ncard := G.ncard_touching_le (fun v => (h3 v).le) Pᶜ
          _ ≤ 3 * {v | top ≤ G.matchingKey M score v}.ncard :=
              Nat.mul_le_mul_left 3 (ncard_le_ncard hsub)
          _ ≤ 3 * (4 * {e | top ≤ score e}.ncard) :=
              Nat.mul_le_mul_left 3 (ncard_matchingKey_pred_le_four hloop h3 hM score (top ≤ ·))
          _ = 12 * {e | top ≤ score e}.ncard := by ring
      have hcutR : ((G.edgeCut P).ncard : ℝ) ≤ 12 * ({e | top ≤ score e}.ncard : ℝ) := by
        exact_mod_cast hcut
      linarith
    obtain ⟨i, hiK, ht, ht'⟩ := exists_grid_index hδ hge hlt
    set t := a + i * δ
    set t' := a + (i + 1) * δ
    set P₀ : Set V := {v | G.matchingKey M score v < t}
    have hP₀ : P₀ ⊆ P := fun v hv => by_contra fun hvn => not_lt.mpr (ht.trans (hP_ge v hvn)) hv
    have hdiff : P \ P₀ ⊆ {v | t ≤ G.matchingKey M score v ∧ G.matchingKey M score v < t'} :=
      fun v ⟨hv, hvn⟩ => ⟨not_lt.mp hvn, (hP_le v hv).trans_lt ht'⟩
    have hwin : (P \ P₀).ncard ≤ 4 * {e | t ≤ score e ∧ score e < t'}.ncard :=
      (ncard_le_ncard hdiff).trans
        (ncard_matchingKey_pred_le_four hloop h3 hM score fun x => t ≤ x ∧ x < t')
    have hwinR : 3 * ((P \ P₀).ncard : ℝ) ≤ 12 * ({e | t ≤ score e ∧ score e < t'}.ncard : ℝ) := by
      have : (P \ P₀).ncard * 3 ≤ 12 * {e | t ≤ score e ∧ score e < t'}.ncard := by omega
      have hR : ((P \ P₀).ncard : ℝ) * 3 ≤ 12 * ({e | t ≤ score e ∧ score e < t'}.ncard : ℝ) := by
        exact_mod_cast this
      linarith
    have heff : ((G.edgeCut P).ncard : ℝ) -
        (1 - lam) * ((G.activeCleanPairs M M_clean score P).ncard : ℝ) ≤
        G.weightedMatchingCost M M_clean lam score t + 3 * ((P \ P₀).ncard : ℝ) :=
      ncard_edgeCut_sub_active_le_weightedMatchingCost hloop h3 hM hclean hlam0 hlam1 score t hP₀
    linarith [mid i hiK]
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
