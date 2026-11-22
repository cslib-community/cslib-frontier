/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.DeMorgan
public import CslibFrontier.Computability.Circuit.Frontier.Basis.PairAtlas
public import CslibFrontier.Computability.Circuit.Frontier.Correlation.Circuit
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Cubic
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Matching
public import CslibFrontier.Computability.Circuit.Frontier.Nondeterministic
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.TutteBerge
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Support
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Foundations.Data.Nat.Card
import CslibFrontier.Foundations.Data.Nat.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `U₂` pair-compressed layouts, `7/8` cubic matchings, and `3`-state frontier compilation

On a circuit over the `U₂` basis (fan-in at most two without `XOR`/`XNOR`, covering both
`Cslib.Circuits.Boolean.DeMorgan` and `Cslib.Circuits.Boolean`), every clean `3`-pin block of a
saturated compression realizes either a polarized `COPY` junction or an `AND`-type gate, and every
matched edge joining two clean `3`-pin blocks admits an unambiguous `3`-rectangle cover
(`Cslib.Circuits.Frontier.Basis.hasUnambiguousRectangles_u2`).

Combining this `3`-state frontier compression (`log₂ 3` bits in place of `2` bits whenever both
high-score outer wires of a clean matched pair lie on the frontier) with:

* an exact natural-number prefix slack bound (`ncard_edgeCut_add_inactive_le_matchingCost`) showing
  that any clean `(1, 1)` pair whose high-score outer wires do *not* both stay on the prefix cut
  already saves at least `1` cut edge over `Multigraph.matchingCost`, and
* a `7/8` vertex-coverage matching theorem for arbitrary finite `3`-regular simple graphs proved
  directly from `SimpleGraph.exists_isMatching_ncard_verts_add_ncard_oddComponents_eq`,

reduces worst-case, average-case, nondeterministic, and quadratic-form correlation bounds for `U₂`
circuits to the single-threshold Gaussian expectation of `Multigraph.weightedMatchingCost` at weight
`λ = log₂ 3 - 1`.

## Main definitions

* `Cslib.Circuits.Frontier.Multigraph.weightedMatchingCost`: threshold cost assigning weight
  `λ ∈ [0, 1]` to `PairStraddlesBoth` on clean matched edges and `1` on dirty matched edges.
* `Cslib.Circuits.Frontier.Multigraph.activeCleanPairs`: clean matched pairs whose endpoints both
  lie in a prefix `P` and whose two high-score outer edges both cross `G.edgeCut P`.
* `Cslib.Circuits.Interpretation.IsU2`: Boolean interpretations of fan-in at most two whose binary
  operations are polarized `AND`-type (`Boolean.DeMorgan.isU2`, `Boolean.isU2`).
* `Cslib.Circuits.Frontier.Compiler.U2PairData.branchingProgram`: the `3`-state pair-compressed
  layered `ReadOnceNBP` of a `U₂` circuit network.
* `Cslib.Circuits.Frontier.U2CubicPairBound`: cubic pair-node effective-cut layout hypothesis at
  weight `λ = log₂ 3 - 1`.

## Main results

* `SimpleGraph.exists_isMatching_mul_eight_ge`,
  `Cslib.Circuits.Frontier.Multigraph.exists_isMatching_mul_eight_ge`: every finite `3`-regular
  simple graph (or loopless edge-simple cubic multigraph) has a matching covering at least `7/8` of
  its vertices.
* `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_add_inactive_le_matchingCost`,
  `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_sub_active_le_weightedMatchingCost`,
  `Cslib.Circuits.Frontier.Multigraph.exists_u2_pairNode_layout`: natural-number prefix slack and
  real effective-cut pair-node layout bounds.
* `Cslib.Circuits.Frontier.Compiler.exists_u2_saturated`: saturated `U₂` budget-`3` compression with
  clean `3`-pin blocks and exact read-input and dirty-block counts.
* `Cslib.Circuits.Frontier.eventually_lt_innerSize_u2_nondeterministic`,
  `Cslib.Circuits.Frontier.eventually_lt_innerSize_u2`,
  `Cslib.Circuits.Frontier.eventually_agreement_le_u2`,
  `Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le_u2`: parametric `U₂`
  nondeterministic, worst-case, average-case, and quadratic-form correlation reductions.
-/

public section

/-! ### `7/8` vertex-coverage matchings in `3`-regular simple graphs -/

namespace SimpleGraph

/-- **Every finite `3`-regular simple graph has a matching covering at least `7/8` of its
vertices.** In the Tutte–Berge maximizer `U`, every odd component `C` of `G - U` has an odd number
`b_C`
of edges to `U`; when `b_C = 1`, `3 |C| - 1 ≤ |C| (|C| - 1)` with `|C|` odd forces `|C| ≥ 5`. Thus
`q₁ + 3 q₃ ≤ 3 |U|` and `|U| + 5 q₁ + q₃ ≤ |V|`, giving `8 (q₁ + q₃ - |U|) ≤ |V|`. -/
theorem exists_isMatching_mul_eight_ge {V : Type*} [Finite V] (H : SimpleGraph V)
    (h3 : ∀ v : V, (H.neighborSet v).ncard = 3) :
    ∃ M : H.Subgraph, M.IsMatching ∧ 7 * Nat.card V ≤ 8 * M.verts.ncard := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨M, U, hM, hTB⟩ := H.exists_isMatching_ncard_verts_add_ncard_oddComponents_eq
  refine ⟨M, hM, ?_⟩
  set G' := ((⊤ : H.Subgraph).deleteVerts U).coe
  set OddC := G'.oddComponents
  have := Fintype.ofFinite OddC
  let Ufin : Finset V := U.toFinset
  have hUcard : Ufin.card = U.ncard := (Set.ncard_eq_toFinset_card' U).symm
  let S (c : OddC) : Finset V := (Subtype.val '' c.1.supp).toFinset
  have hScard (c : OddC) : (S c).card = c.1.supp.ncard := by
    rw [← Set.ncard_eq_toFinset_card', Set.ncard_image_of_injective _ Subtype.val_injective]
  have hSodd (c : OddC) : Odd (S c).card := by
    rw [hScard]
    exact c.2
  have hS_notU (c : OddC) {v : V} (hv : v ∈ S c) : v ∉ U := by
    simp only [S, Set.mem_toFinset, Set.mem_image] at hv
    obtain ⟨x, -, rfl⟩ := hv
    exact x.2.2
  have hS_disj_U (c : OddC) : Disjoint (S c) Ufin :=
    Finset.disjoint_left.mpr fun v hv hvU => hS_notU c hv (Set.mem_toFinset.mp hvU)
  have hS_pairwise : Set.Pairwise (Set.univ : Set OddC) fun c₁ c₂ => Disjoint (S c₁) (S c₂) := by
    intro c₁ _ c₂ _ hne
    refine Finset.disjoint_left.mpr fun v hv₁ hv₂ => hne ?_
    simp only [S, Set.mem_toFinset, Set.mem_image] at hv₁ hv₂
    obtain ⟨x₁, hx₁, hxv₁⟩ := hv₁
    obtain ⟨x₂, hx₂, hxv₂⟩ := hv₂
    have hx : x₁ = x₂ := Subtype.ext (hxv₁.trans hxv₂.symm)
    exact Subtype.ext (ConnectedComponent.eq_of_common_vertex hx₁ (hx ▸ hx₂))
  have hS_closed (c : OddC) {v w : V} (hv : v ∈ S c) (hw : w ∉ U) (hadj : H.Adj v w) :
      w ∈ S c := by
    simp only [S, Set.mem_toFinset, Set.mem_image] at hv ⊢
    obtain ⟨x, hx, rfl⟩ := hv
    refine ⟨⟨w, trivial, hw⟩, ?_, rfl⟩
    rw [ConnectedComponent.mem_supp_iff] at hx ⊢
    rw [← hx]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj
      (Subgraph.Adj.coe (Subgraph.deleteVerts_adj.mpr ⟨trivial, x.2.2, trivial, hw, hadj⟩))).symm
  let intPairs (c : OddC) : Finset (V × V) :=
    (S c ×ˢ S c).filter fun p => H.Adj p.1 p.2
  let cutPairs (c : OddC) : Finset (V × V) :=
    (S c ×ˢ Ufin).filter fun p => H.Adj p.1 p.2
  have hdeg_sum (c : OddC) : 3 * (S c).card = (intPairs c).card + (cutPairs c).card := by
    have hpart : intPairs c ∪ cutPairs c =
        (S c).biUnion fun v => (H.neighborFinset v).map
          ⟨fun w => (v, w), fun _ _ h => Prod.mk.inj h |>.2⟩ := by
      ext ⟨v, w⟩
      simp only [intPairs, cutPairs, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
        Finset.mem_biUnion, Finset.mem_map, mem_neighborFinset]
      constructor
      · rintro (⟨⟨hv, _⟩, hadj⟩ | ⟨⟨hv, _⟩, hadj⟩) <;> exact ⟨v, hv, w, hadj, rfl⟩
      · rintro ⟨v', hv', w', hadj, hpair⟩
        change (v', w') = (v, w) at hpair
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
        by_cases hwU : w' ∈ U
        · exact Or.inr ⟨⟨hv', Set.mem_toFinset.mpr hwU⟩, hadj⟩
        · exact Or.inl ⟨⟨hv', hS_closed c hv' hwU hadj⟩, hadj⟩
    have hdisj : Disjoint (intPairs c) (cutPairs c) :=
      Finset.disjoint_left.mpr fun p hp₁ hp₂ =>
        Finset.disjoint_left.mp (hS_disj_U c) (Finset.mem_product.mp (Finset.mem_filter.mp hp₁).1).2
          (Finset.mem_product.mp (Finset.mem_filter.mp hp₂).1).2
    rw [← Finset.card_union_of_disjoint hdisj, hpart, Finset.card_biUnion]
    · have h3fin (v : V) : (H.neighborFinset v).card = 3 := by
        have := h3 v
        rwa [← H.coe_neighborFinset v, Set.ncard_coe_finset] at this
      simp only [Finset.card_map, h3fin, Finset.sum_const, smul_eq_mul, mul_comm]
    · intro v₁ _ v₂ _ hne
      refine Finset.disjoint_left.mpr fun p hp₁ hp₂ => hne ?_
      simp only [Finset.mem_map] at hp₁ hp₂
      obtain ⟨w₁, -, rfl⟩ := hp₁
      obtain ⟨w₂, -, heq⟩ := hp₂
      exact (Prod.mk.inj heq).1.symm
  let idx : V ≃ Fin (Nat.card V) := Finite.equivFin V
  have hint_even (c : OddC) : Even (intPairs c).card := by
    let F_lt := (intPairs c).filter fun p => idx p.1 < idx p.2
    let F_gt := (intPairs c).filter fun p => ¬idx p.1 < idx p.2
    have hsplit : (intPairs c).card = F_lt.card + F_gt.card :=
      (Finset.card_filter_add_card_filter_not _).symm
    have hbij : F_lt.card = F_gt.card := by
      refine Finset.card_bij (fun p _ => p.swap) (fun p hp => ?_)
        (fun p₁ _ p₂ _ h => Prod.swap_injective h) (fun p hp => ?_)
      · simp only [F_lt, F_gt, intPairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, hp.1.2.symm⟩, fun hlt => lt_asymm hp.2 hlt⟩
      · simp only [F_lt, F_gt, intPairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
        have hne : idx p.2 ≠ idx p.1 := fun h => hp.1.2.ne (idx.injective h.symm)
        refine ⟨p.swap, ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, hp.1.2.symm⟩, ?_⟩, Prod.swap_swap p⟩
        exact lt_of_le_of_ne (not_lt.mp hp.2) hne
    rw [hsplit, hbij]
    exact ⟨F_gt.card, rfl⟩
  have hint_le (c : OddC) : (intPairs c).card ≤ (S c).card * (S c).card - (S c).card := by
    have hsub : intPairs c ⊆ (S c).offDiag := fun p hp => by
      simp only [intPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag] at hp ⊢
      exact ⟨hp.1.1, hp.1.2, hp.2.ne⟩
    exact (Finset.card_le_card hsub).trans_eq (Finset.offDiag_card (S c))
  have hcut_odd (c : OddC) : Odd (cutPairs c).card := by
    obtain ⟨k, hk⟩ := hSodd c
    obtain ⟨m, hm⟩ := hint_even c
    have hsum := hdeg_sum c
    refine ⟨3 * k + 1 - m, ?_⟩
    omega
  have hfive_of_one (c : OddC) (h1 : (cutPairs c).card = 1) : 5 ≤ (S c).card := by
    obtain ⟨k, hk⟩ := hSodd c
    have hsum := hdeg_sum c
    have hle := hint_le c
    rw [h1] at hsum
    rw [hk] at hsum hle
    rcases k with _ | _ | k <;> omega
  let Q₁ : Finset OddC := Finset.univ.filter fun c => (cutPairs c).card = 1
  let Q₃ : Finset OddC := Finset.univ.filter fun c => ¬(cutPairs c).card = 1
  have hQ_tot : Q₁.card + Q₃.card = OddC.ncard := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
  have hQ₃_ge (c : OddC) (hc : c ∈ Q₃) : 3 ≤ (cutPairs c).card := by
    have hne : (cutPairs c).card ≠ 1 := (Finset.mem_filter.mp hc).2
    obtain ⟨k, hk⟩ := hcut_odd c
    omega
  have hcut_tot : Q₁.card + 3 * Q₃.card ≤ 3 * U.ncard := by
    have hlow : Q₁.card + 3 * Q₃.card ≤ ∑ c : OddC, (cutPairs c).card := by
      rw [← Finset.sum_add_sum_compl Q₁]
      have hcompl : Q₁ᶜ = Q₃ := by ext c; simp [Q₁, Q₃]
      rw [hcompl]
      refine Nat.add_le_add ?_ ?_
      · calc Q₁.card = ∑ _c ∈ Q₁, 1 := by simp
          _ ≤ ∑ c ∈ Q₁, (cutPairs c).card :=
            Finset.sum_le_sum fun c hc => le_of_eq (Finset.mem_filter.mp hc).2.symm
      · calc 3 * Q₃.card = ∑ _c ∈ Q₃, 3 := by simp [mul_comm]
          _ ≤ ∑ c ∈ Q₃, (cutPairs c).card := Finset.sum_le_sum fun c hc => hQ₃_ge c hc
    have hbi_disj : ((Finset.univ : Finset OddC) : Set OddC).PairwiseDisjoint cutPairs := by
      intro c₁ _ c₂ _ hne
      refine Finset.disjoint_left.mpr fun p hp₁ hp₂ => ?_
      exact Finset.disjoint_left.mp (hS_pairwise trivial trivial hne)
        (Finset.mem_product.mp (Finset.mem_filter.mp hp₁).1).1
        (Finset.mem_product.mp (Finset.mem_filter.mp hp₂).1).1
    let allFromU : Finset (V × V) :=
      Ufin.biUnion fun u => (H.neighborFinset u).map
        ⟨fun v => (v, u), fun _ _ h => Prod.mk.inj h |>.1⟩
    have hsub : Finset.univ.biUnion cutPairs ⊆ allFromU := by
      intro ⟨v, u⟩ hp
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, cutPairs, Finset.mem_filter,
        Finset.mem_product] at hp
      obtain ⟨c, ⟨_, hu⟩, hadj⟩ := hp
      simp only [allFromU, Finset.mem_biUnion, Finset.mem_map, mem_neighborFinset]
      exact ⟨u, hu, v, hadj.symm, rfl⟩
    have hall_card : allFromU.card ≤ 3 * Ufin.card := by
      refine Finset.card_biUnion_le.trans ?_
      have h3fin (u : V) : (H.neighborFinset u).card = 3 := by
        have := h3 u
        rwa [← H.coe_neighborFinset u, Set.ncard_coe_finset] at this
      simp [h3fin, mul_comm]
    calc Q₁.card + 3 * Q₃.card
        ≤ ∑ c : OddC, (cutPairs c).card := hlow
      _ = (Finset.univ.biUnion cutPairs).card := (Finset.card_biUnion hbi_disj).symm
      _ ≤ allFromU.card := Finset.card_le_card hsub
      _ ≤ 3 * U.ncard := by rwa [hUcard] at hall_card
  have hvert_tot : U.ncard + 5 * Q₁.card + Q₃.card ≤ Nat.card V := by
    have hlow : 5 * Q₁.card + Q₃.card ≤ ∑ c : OddC, (S c).card := by
      rw [← Finset.sum_add_sum_compl Q₁]
      have hcompl : Q₁ᶜ = Q₃ := by ext c; simp [Q₁, Q₃]
      rw [hcompl]
      refine Nat.add_le_add ?_ ?_
      · calc 5 * Q₁.card = ∑ _c ∈ Q₁, 5 := by simp [mul_comm]
          _ ≤ ∑ c ∈ Q₁, (S c).card :=
            Finset.sum_le_sum fun c hc => hfive_of_one c (Finset.mem_filter.mp hc).2
      · calc Q₃.card = ∑ _c ∈ Q₃, 1 := by simp
          _ ≤ ∑ c ∈ Q₃, (S c).card := Finset.sum_le_sum fun c _ => by
            obtain ⟨k, hk⟩ := hSodd c; omega
    have hdisj_all : Disjoint Ufin (Finset.univ.biUnion S) := by
      refine Finset.disjoint_left.mpr fun v hvU hvS => ?_
      obtain ⟨c, -, hvc⟩ := Finset.mem_biUnion.mp hvS
      exact Finset.disjoint_left.mp (hS_disj_U c) hvc hvU
    have hcard_bi : (Finset.univ.biUnion S).card = ∑ c : OddC, (S c).card :=
      Finset.card_biUnion fun c₁ _ c₂ _ hne => hS_pairwise trivial trivial hne
    have hunion_le : (Ufin ∪ Finset.univ.biUnion S).card ≤ Fintype.card V :=
      Finset.card_le_univ _
    rw [Finset.card_union_of_disjoint hdisj_all, hUcard, hcard_bi,
      ← Nat.card_eq_fintype_card] at hunion_le
    omega
  omega

end SimpleGraph

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

private theorem outerLow_outerHigh_spec [Finite E] {G : Multigraph V E}
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
        simp only [EdgeStraddles, hinc, mem_insert_iff, mem_singleton_iff]
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

/-! ### `U₂` bases and clean-block saturated compressions -/

namespace Cslib.Circuits

/-- A Boolean circuit interpretation belongs to **`U₂`** (fan-in at most two without `XOR`/`XNOR`)
when every operation has arity at most `2` and every binary operation is an `AND`-type gate up to
input/output polarities (`AND`, `OR`, `NAND`, `NOR`, `IMP`, `NIMP`, etc.). Constants (arity `0`)
and arbitrary unary gates (arity `1`: `id`, `NOT`, or constants) are permitted. -/
structure Interpretation.IsU2 {σ : Signature} (I : Interpretation σ Bool) : Prop where
  /-- Every operation has fan-in at most `2`. -/
  arity_le_two : ∀ op : σ.Op, σ.Arity op ≤ 2
  /-- Every binary operation is an `AND`-type gate `((x₀ ^^ nx) && (x₁ ^^ ny)) ^^ nz`. -/
  binary_andType : ∀ (op : σ.Op) (h : σ.Arity op = 2), ∃ nx ny nz : Bool,
    ∀ x : Fin 2 → Bool, I op (x ∘ Fin.cast h) = (((x 0 ^^ nx) && (x 1 ^^ ny)) ^^ nz)

theorem Interpretation.IsU2.fanInAtMost_two {σ : Signature} {I : Interpretation σ Bool}
    (hI : I.IsU2) {n m : ℕ} (c : Circuit σ n m) : c.FanInAtMost 2 :=
  Program.fanInAtMost_iff.mpr fun _ => hI.arity_le_two _

/-- The constant-free De Morgan basis `Boolean.DeMorgan.interpretation` is a `U₂` basis. -/
theorem Boolean.DeMorgan.isU2 : Boolean.DeMorgan.interpretation.IsU2 where
  arity_le_two := Boolean.DeMorgan.arity_le_two
  binary_andType op h := by
    cases op with
    | not => cases h
    | and => exact ⟨false, false, false, fun x => by simp [Boolean.DeMorgan.interpretation]⟩
    | or =>
      refine ⟨true, true, true, fun x => ?_⟩
      simp only [Boolean.DeMorgan.interpretation, Fin.cast_refl, Function.comp_id]
      cases x 0 <;> cases x 1 <;> rfl

/-- cslib's Boolean basis `Boolean.interpretation` (De Morgan with constants) is a `U₂` basis. -/
theorem Boolean.isU2 : Boolean.interpretation.IsU2 where
  arity_le_two op := by cases op <;> simp
  binary_andType op h := by
    cases op with
    | const _ => cases h
    | not => cases h
    | and => exact ⟨false, false, false, fun x => by simp [Boolean.interpretation]⟩
    | or =>
      refine ⟨true, true, true, fun x => ?_⟩
      simp only [Boolean.interpretation, Fin.cast_refl, Function.comp_id]
      cases x 0 <;> cases x 1 <;> rfl

end Cslib.Circuits

namespace Cslib.Circuits.Frontier.Compiler

open Set Cslib.Circuits.Frontier.Basis

section CleanCompression

variable {σ : Signature} {m_in m_out : ℕ}

/-- Edges of `graph c` with both endpoints inside `S`. -/
def internalEdges (c : Circuit σ m_in m_out) (S : Set (Vertex c)) : Set (Edge c) :=
  {e | src e ∈ S ∧ tgt e ∈ S}

/-- Vertices that carry neither inputs nor circuit outputs: junctions and reachable gates. -/
def IsCleanVertex {c : Circuit σ m_in m_out} (v : Vertex c) : Prop :=
  (∀ (i : Fin m_in) (hi : Reach c (.input i)), v ≠ .signal ⟨.input i, hi⟩) ∧
    ∀ o : Fin m_out, v ≠ .output o

/-- Input- and output-independent local gate/junction satisfaction on `S`. -/
def GateSatisfies {c : Circuit σ m_in m_out} (I : Interpretation σ Bool) (S : Set (Vertex c))
    (α : Edge c → Bool) : Prop :=
  ∀ v ∈ S, Constraint I (fun _ => univ) v (fun _ => false) α

private theorem constraint_iff_of_isCleanVertex {c : Circuit σ m_in m_out}
    (I : Interpretation σ Bool) (Acc : Fin m_out → Set Bool) {v : Vertex c} (hv : IsCleanVertex v)
    (x : Fin m_in → Bool) (α : Edge c → Bool) :
    Constraint I Acc v x α ↔ Constraint I (fun _ => univ) v (fun _ => false) α := by
  cases v with
  | signal w =>
    rcases w with ⟨i | g, hw⟩
    · exact (hv.1 i hw rfl).elim
    · rfl
  | junction _ => rfl
  | output o => exact (hv.2 o rfl).elim

private theorem readAt_eq_empty_of_isCleanVertex {c : Circuit σ m_in m_out}
    (I : Interpretation σ Bool) (Acc : Fin m_out → Set Bool) {v : Vertex c}
    (hv : IsCleanVertex v) : ((network c I Acc).readAt v) = ∅ := by
  ext i
  simp only [Network.readAt, network_site, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  intro hsite
  obtain ⟨hi, rfl⟩ := site_eq_some hsite
  exact hv.1 i hi rfl

private theorem hidden_constraint_iff_of_isCleanVertex {n k : ℕ} {c : Circuit σ (n + k) m_out}
    (I : Interpretation σ Bool) (Acc : Fin m_out → Set Bool) {v : Vertex c}
    (hv : IsCleanVertex v) (x : Fin n → Bool) (α : Edge c → Bool) :
    (hiddenNetwork c I Acc).Constraint v x α ↔
      Constraint I (fun _ => univ) v (fun _ => false) α := by
  change (∃ y : Fin k → Bool, Constraint I Acc v _ α) ↔ _
  simp only [constraint_iff_of_isCleanVertex I Acc hv _ α, exists_const]

private theorem readAt_hidden_eq_empty_of_isCleanVertex {n k : ℕ} {c : Circuit σ (n + k) m_out}
    (I : Interpretation σ Bool) (Acc : Fin m_out → Set Bool) {v : Vertex c}
    (hv : IsCleanVertex v) :
    ((hiddenNetwork c I Acc).readAt v) = ∅ := by
  ext i
  simp only [hiddenNetwork, Network.readAt, Network.hide, Network.reindex, network_site,
    mem_ofPred_eq, mem_empty_iff_false, iff_false]
  intro hsite
  obtain ⟨hi, rfl⟩ := site_eq_some hsite
  exact hv.1 _ hi rfl

private theorem gateSatisfies_congr {c : Circuit σ m_in m_out} {I : Interpretation σ Bool}
    {S : Set (Vertex c)} {α β : Edge c → Bool}
    (h : EqOn α β ((graph c).touching S)) (hα : GateSatisfies I S α) :
    GateSatisfies I S β := by
  intro v hv
  refine (network c I fun _ => univ).constraint_congr v (fun _ => false) (fun _ => false) α β
    (fun _ _ => rfl) (fun e he => ?_) (hα v hv)
  exact h (he.imp (fun hs => by change (graph c).src e = v at hs; rw [hs]; exact hv)
    (fun ht => by change (graph c).tgt e = v at ht; rw [ht]; exact hv))

/-- A clean `2`-pin block acting as an oriented Boolean wire `α e_out = (α e_in ^^ neg)`. -/
private def CleanWire {c : Circuit σ m_in m_out} (I : Interpretation σ Bool)
    (S : Set (Vertex c)) : Prop :=
  ∃ (e_in e_out : Edge c) (neg : Bool),
    (∀ v ∈ S, IsCleanVertex v) ∧
    e_in ≠ e_out ∧
    (graph c).edgeCut S = {e_in, e_out} ∧
    tgt e_in ∈ S ∧ src e_out ∈ S ∧
    (∀ α, GateSatisfies I S α → α e_out = (α e_in ^^ neg)) ∧
    (∀ α, α e_out = (α e_in ^^ neg) →
      ∃ β, EqOn β α (internalEdges c S)ᶜ ∧ GateSatisfies I S β)

/-- A clean `3`-pin block whose every outgoing boundary edge realizes a `U2OutRel` and whose every
incoming boundary edge realizes a `U2InRel`. -/
def CleanBlock3 {c : Circuit σ m_in m_out} (I : Interpretation σ Bool) (S : Set (Vertex c)) :
    Prop :=
  (∀ v ∈ S, IsCleanVertex v) ∧
  ((graph c).edgeCut S).ncard = 3 ∧
  ∀ (p q e : Edge c), p ≠ q → (graph c).edgeCut S \ {e} = {p, q} → e ∈ (graph c).edgeCut S →
    (src e ∈ S → ∃ rel : Bool → Bool → Bool → Bool, U2OutRel rel ∧
      (∀ α, GateSatisfies I S α → rel (α p) (α q) (α e) = true) ∧
      (∀ α, rel (α p) (α q) (α e) = true →
        ∃ β, EqOn β α (internalEdges c S)ᶜ ∧ GateSatisfies I S β)) ∧
    (tgt e ∈ S → ∃ rel : Bool → Bool → Bool → Bool, U2InRel rel ∧
      (∀ α, GateSatisfies I S α → rel (α p) (α q) (α e) = true) ∧
      (∀ α, rel (α p) (α q) (α e) = true →
        ∃ β, EqOn β α (internalEdges c S)ᶜ ∧ GateSatisfies I S β))

private theorem edgeCut_union_of_inter_singleton {V E : Type*} {G : Multigraph V E}
    {S₁ S₂ : Set V} (hd : Disjoint S₁ S₂) {f : E}
    (hint : G.edgeCut S₁ ∩ G.edgeCut S₂ = {f}) :
    G.edgeCut (S₁ ∪ S₂) = (G.edgeCut S₁ \ {f}) ∪ (G.edgeCut S₂ \ {f}) ∧
      {e | G.src e ∈ S₁ ∪ S₂ ∧ G.tgt e ∈ S₁ ∪ S₂} =
        {e | G.src e ∈ S₁ ∧ G.tgt e ∈ S₁} ∪ {e | G.src e ∈ S₂ ∧ G.tgt e ∈ S₂} ∪ {f} := by
  have hmem_f (e : E) : e = f ↔ e ∈ G.edgeCut S₁ ∧ e ∈ G.edgeCut S₂ := by
    rw [← mem_singleton_iff, ← hint, mem_inter_iff]
  constructor
  · ext e
    have hd_src : ¬(G.src e ∈ S₁ ∧ G.src e ∈ S₂) := fun ⟨h1, h2⟩ => disjoint_left.mp hd h1 h2
    have hd_tgt : ¬(G.tgt e ∈ S₁ ∧ G.tgt e ∈ S₂) := fun ⟨h1, h2⟩ => disjoint_left.mp hd h1 h2
    simp only [mem_union, mem_sdiff, mem_singleton_iff, hmem_f, Multigraph.mem_edgeCut]
    tauto
  · ext e
    have hd_src : ¬(G.src e ∈ S₁ ∧ G.src e ∈ S₂) := fun ⟨h1, h2⟩ => disjoint_left.mp hd h1 h2
    have hd_tgt : ¬(G.tgt e ∈ S₁ ∧ G.tgt e ∈ S₂) := fun ⟨h1, h2⟩ => disjoint_left.mp hd h1 h2
    simp only [mem_union, mem_singleton_iff, hmem_f, Multigraph.mem_edgeCut, mem_ofPred_eq]
    tauto

private theorem patch_union {c : Circuit σ m_in m_out} {I : Interpretation σ Bool}
    {S₁ S₂ : Set (Vertex c)} (hd : Disjoint S₁ S₂) {f : Edge c}
    (hint : (graph c).edgeCut S₁ ∩ (graph c).edgeCut S₂ = {f})
    (α α₀ : Edge c → Bool) (hα₀ : ∀ e ≠ f, α₀ e = α e)
    (h₁ : ∃ β₁, EqOn β₁ α₀ (internalEdges c S₁)ᶜ ∧ GateSatisfies I S₁ β₁)
    (h₂ : ∀ β₁, EqOn β₁ α₀ ((graph c).edgeCut S₂) →
      ∃ β₂, EqOn β₂ β₁ (internalEdges c S₂)ᶜ ∧ GateSatisfies I S₂ β₂) :
    ∃ β, EqOn β α (internalEdges c (S₁ ∪ S₂))ᶜ ∧ GateSatisfies I (S₁ ∪ S₂) β := by
  obtain ⟨β₁, hβ₁_eq, hβ₁_sat⟩ := h₁
  have hβ₁_cut₂ : EqOn β₁ α₀ ((graph c).edgeCut S₂) := by
    intro e he
    refine hβ₁_eq fun hin => ?_
    simp only [Multigraph.mem_edgeCut, graph_src, graph_tgt] at he
    exact he (iff_of_false (disjoint_left.mp hd hin.1) (disjoint_left.mp hd hin.2))
  obtain ⟨β₂, hβ₂_eq, hβ₂_sat⟩ := h₂ β₁ hβ₁_cut₂
  have hβ₂_touch₁ : EqOn β₁ β₂ ((graph c).touching S₁) := by
    intro e he
    symm
    refine hβ₂_eq fun hin => ?_
    rcases he with hs | ht
    · exact disjoint_left.mp hd hs hin.1
    · exact disjoint_left.mp hd ht hin.2
  have hint_eq := (edgeCut_union_of_inter_singleton hd hint).2
  dsimp only [graph_src, graph_tgt] at hint_eq
  refine ⟨β₂, fun e he => ?_, fun v hv => ?_⟩
  · change e ∉ {e | src e ∈ S₁ ∪ S₂ ∧ tgt e ∈ S₁ ∪ S₂} at he
    rw [hint_eq] at he
    simp only [mem_union, mem_singleton_iff, not_or] at he
    obtain ⟨⟨hn1, hn2⟩, hnf⟩ := he
    rw [hβ₂_eq hn2, hβ₁_eq hn1, hα₀ e hnf]
  · rcases hv with hv₁ | hv₂
    · exact gateSatisfies_congr hβ₂_touch₁ hβ₁_sat v hv₁
    · exact hβ₂_sat v hv₂

private theorem cleanWire_merge_wire {c : Circuit σ m_in m_out} {I : Interpretation σ Bool}
    {S₁ S₂ : Set (Vertex c)} (hd : Disjoint S₁ S₂)
    (hw₁ : CleanWire I S₁) (hw₂ : CleanWire I S₂)
    (h1 : ((graph c).edgeCut S₁ ∩ (graph c).edgeCut S₂).ncard = 1) :
    CleanWire I (S₁ ∪ S₂) := by
  classical
  obtain ⟨f, hint⟩ := ncard_eq_one.mp h1
  obtain ⟨hc_union, _⟩ := edgeCut_union_of_inter_singleton hd hint
  obtain ⟨a₁, b₁, neg₁, hcl₁, hne₁, hcut₁, htgt₁, hsrc₁, hsd₁, hrl₁⟩ := hw₁
  obtain ⟨a₂, b₂, neg₂, hcl₂, hne₂, hcut₂, htgt₂, hsrc₂, hsd₂, hrl₂⟩ := hw₂
  have hf₁ : f = a₁ ∨ f = b₁ := by
    have : f ∈ (graph c).edgeCut S₁ := (hint.symm ▸ mem_singleton f).1
    simpa [hcut₁] using this
  have hf₂ : f = a₂ ∨ f = b₂ := by
    have : f ∈ (graph c).edgeCut S₂ := (hint.symm ▸ mem_singleton f).2
    simpa [hcut₂] using this
  have hcl_u : ∀ v ∈ S₁ ∪ S₂, IsCleanVertex v := fun v hv => hv.elim (hcl₁ v) (hcl₂ v)
  rcases hf₁ with hfa₁ | hfb₁ <;> rcases hf₂ with hfa₂ | hfb₂
  · exact (disjoint_left.mp hd (hfa₁ ▸ htgt₁) (hfa₂ ▸ htgt₂)).elim
  · -- `f = a₁ = b₂`: `S₂` feeds `S₁` (`a₂ → f → b₁`)
    have ha₂_ne_b₁ : a₂ ≠ b₁ := fun h => by
      have : a₂ ∈ (graph c).edgeCut S₁ ∩ (graph c).edgeCut S₂ :=
        ⟨by rw [hcut₁, h]; simp, by rw [hcut₂]; simp⟩
      rw [hint, mem_singleton_iff, hfb₂] at this
      exact hne₂ this
    have hs₁ : (graph c).edgeCut S₁ \ {f} = {b₁} := by
      rw [hcut₁, hfa₁]; ext e; simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      exact ⟨fun ⟨h, hne⟩ => h.resolve_left hne, fun h => ⟨Or.inr h, h ▸ hne₁.symm⟩⟩
    have hs₂ : (graph c).edgeCut S₂ \ {f} = {a₂} := by
      rw [hcut₂, hfb₂]; ext e; simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      exact ⟨fun ⟨h, hne⟩ => h.resolve_right hne, fun h => ⟨Or.inl h, h ▸ hne₂⟩⟩
    refine ⟨a₂, b₁, neg₂ ^^ neg₁, hcl_u, ha₂_ne_b₁, ?_, Or.inr htgt₂, Or.inl hsrc₁, ?_, ?_⟩
    · rw [hc_union, hs₁, hs₂]; ext e; simp [or_comm]
    · intro α hsat
      have h1' := hsd₁ α fun v hv => hsat v (Or.inl hv)
      have h2' := hsd₂ α fun v hv => hsat v (Or.inr hv)
      rw [h1', ← hfa₁, hfb₂, h2', Bool.xor_assoc]
    · intro α hα
      let α₀ : Edge c → Bool := fun e => if e = f then (α a₂ ^^ neg₂) else α e
      refine patch_union hd hint α α₀ (fun e hne => ite_eq_right hne) ?_ ?_
      · refine hrl₁ α₀ ?_
        have hb₁_eq : α₀ b₁ = α b₁ := ite_eq_right (hfa₁ ▸ hne₁.symm)
        have ha₁_eq : α₀ a₁ = (α a₂ ^^ neg₂) := ite_eq_left hfa₁.symm
        rw [hb₁_eq, ha₁_eq, hα, Bool.xor_assoc]
      · intro β₁ hβ₁
        refine hrl₂ β₁ ?_
        have hb₂ : β₁ b₂ = (α a₂ ^^ neg₂) :=
          (hβ₁ (by rw [hcut₂]; simp)).trans (ite_eq_left hfb₂.symm)
        have ha₂ : β₁ a₂ = α a₂ :=
          (hβ₁ (by rw [hcut₂]; simp)).trans (ite_eq_right (hfb₂ ▸ hne₂))
        rw [hb₂, ha₂]
  · -- `f = b₁ = a₂`: `S₁` feeds `S₂` (`a₁ → f → b₂`)
    have ha₁_ne_b₂ : a₁ ≠ b₂ := fun h => by
      have : a₁ ∈ (graph c).edgeCut S₁ ∩ (graph c).edgeCut S₂ :=
        ⟨by rw [hcut₁]; simp, by rw [hcut₂, h]; simp⟩
      rw [hint, mem_singleton_iff, hfb₁] at this
      exact hne₁ this
    have hs₁ : (graph c).edgeCut S₁ \ {f} = {a₁} := by
      rw [hcut₁, hfb₁]; ext e; simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      exact ⟨fun ⟨h, hne⟩ => h.resolve_right hne, fun h => ⟨Or.inl h, h ▸ hne₁⟩⟩
    have hs₂ : (graph c).edgeCut S₂ \ {f} = {b₂} := by
      rw [hcut₂, hfa₂]; ext e; simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      exact ⟨fun ⟨h, hne⟩ => h.resolve_left hne, fun h => ⟨Or.inr h, h ▸ hne₂.symm⟩⟩
    refine ⟨a₁, b₂, neg₁ ^^ neg₂, hcl_u, ha₁_ne_b₂, ?_, Or.inl htgt₁, Or.inr hsrc₂, ?_, ?_⟩
    · rw [hc_union, hs₁, hs₂]; ext e; simp [or_comm]
    · intro α hsat
      have h1' := hsd₁ α fun v hv => hsat v (Or.inl hv)
      have h2' := hsd₂ α fun v hv => hsat v (Or.inr hv)
      rw [h2', ← hfa₂, hfb₁, h1', Bool.xor_assoc]
    · intro α hα
      let α₀ : Edge c → Bool := fun e => if e = f then (α a₁ ^^ neg₁) else α e
      refine patch_union hd hint α α₀ (fun e hne => ite_eq_right hne) ?_ ?_
      · refine hrl₁ α₀ ?_
        have hb₁_eq : α₀ b₁ = (α a₁ ^^ neg₁) := ite_eq_left hfb₁.symm
        have ha₁_eq : α₀ a₁ = α a₁ := ite_eq_right (hfb₁ ▸ hne₁)
        rw [hb₁_eq, ha₁_eq]
      · intro β₁ hβ₁
        refine hrl₂ β₁ ?_
        have ha₂ : β₁ a₂ = (α a₁ ^^ neg₁) :=
          (hβ₁ (by rw [hcut₂]; simp)).trans (ite_eq_left hfa₂.symm)
        have hb₂ : β₁ b₂ = α b₂ :=
          (hβ₁ (by rw [hcut₂]; simp)).trans (ite_eq_right (hfa₂ ▸ hne₂.symm))
        rw [hb₂, ha₂, hα, Bool.xor_assoc]
  · exact (disjoint_left.mp hd (hfb₁ ▸ hsrc₁) (hfb₂ ▸ hsrc₂)).elim

private theorem cleanWire_merge_block3 {c : Circuit σ m_in m_out} {I : Interpretation σ Bool}
    {S₁ S₂ : Set (Vertex c)} (hd : Disjoint S₁ S₂)
    (hw₁ : CleanWire I S₁) (hb₂ : CleanBlock3 I S₂)
    (h1 : ((graph c).edgeCut S₁ ∩ (graph c).edgeCut S₂).ncard = 1) :
    CleanBlock3 I (S₁ ∪ S₂) := by
  classical
  have := Fintype.ofFinite (Edge c)
  obtain ⟨f, hint⟩ := ncard_eq_one.mp h1
  obtain ⟨hc_union, _⟩ := edgeCut_union_of_inter_singleton hd hint
  obtain ⟨w_in, w_out, neg, hcl₁, hne₁, hcut₁, htgt₁, hsrc₁, hsd₁, hrl₁⟩ := hw₁
  obtain ⟨hcl₂, hnc₂, hpin₂⟩ := hb₂
  have hf₁ : f = w_in ∨ f = w_out := by
    have : f ∈ (graph c).edgeCut S₁ := (hint.symm ▸ mem_singleton f).1
    simpa [hcut₁] using this
  have hf_cut₂ : f ∈ (graph c).edgeCut S₂ := (hint.symm ▸ mem_singleton f).2
  -- Identify the external surviving wire `w'` of `S₁`.
  let w' : Edge c := if f = w_in then w_out else w_in
  have hw'_ne_f : w' ≠ f := by
    dsimp only [w']
    rcases hf₁ with hfw | hfw
    · rw [ite_eq_left hfw, hfw]; exact hne₁.symm
    · rw [ite_eq_right (hfw ▸ hne₁.symm), hfw]; exact hne₁
  have hs₁ : (graph c).edgeCut S₁ \ {f} = {w'} := by
    dsimp only [w']
    rcases hf₁ with hfw | hfw
    · rw [ite_eq_left hfw, hcut₁, hfw]
      ext e; simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      exact ⟨fun ⟨h, hne⟩ => h.resolve_left hne, fun h => ⟨Or.inr h, h ▸ hne₁.symm⟩⟩
    · rw [ite_eq_right (hfw ▸ hne₁.symm), hcut₁, hfw]
      ext e; simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      exact ⟨fun ⟨h, hne⟩ => h.resolve_right hne, fun h => ⟨Or.inl h, h ▸ hne₁⟩⟩
  have hw'_not_cut₂ : w' ∉ (graph c).edgeCut S₂ := fun hm => by
    have : w' ∈ (graph c).edgeCut S₁ ∩ (graph c).edgeCut S₂ :=
      ⟨((hs₁.symm ▸ mem_singleton w') : w' ∈ (graph c).edgeCut S₁ \ {f}).1, hm⟩
    rw [hint, mem_singleton_iff] at this
    exact hw'_ne_f this
  have hw'_not_s₂f : w' ∉ (graph c).edgeCut S₂ \ {f} := fun hm => hw'_not_cut₂ hm.1
  have hcut_u : (graph c).edgeCut (S₁ ∪ S₂) = insert w' ((graph c).edgeCut S₂ \ {f}) := by
    rw [hc_union, hs₁, singleton_union]
  have hnc_s₂ : ((graph c).edgeCut S₂ \ {f}).ncard = 2 := by
    have := ncard_sdiff_singleton_add_one hf_cut₂ (s := (graph c).edgeCut S₂)
    omega
  have hnc_u : ((graph c).edgeCut (S₁ ∪ S₂)).ncard = 3 := by
    rw [hcut_u, ncard_insert_of_notMem hw'_not_s₂f, hnc_s₂]
  -- Orientation & wire relation between `f` and `w'`.
  have horient : (src w' ∈ S₁ ∪ S₂ → src f ∈ S₂) ∧ (tgt w' ∈ S₁ ∪ S₂ → tgt f ∈ S₂) := by
    have hf_cut₂' : ¬(src f ∈ S₂ ↔ tgt f ∈ S₂) := hf_cut₂
    have hw'_cut_u' : ¬(src w' ∈ S₁ ∪ S₂ ↔ tgt w' ∈ S₁ ∪ S₂) := by
      have hm : w' ∈ (graph c).edgeCut (S₁ ∪ S₂) := by rw [hcut_u]; exact mem_insert _ _
      exact hm
    rcases hf₁ with hfw | hfw
    · have hw' : w' = w_out := ite_eq_left hfw
      refine ⟨fun _ => by_contra fun hn =>
        hf_cut₂' (iff_of_false hn (disjoint_left.mp hd (hfw ▸ htgt₁))),
        fun h => (hw'_cut_u' (iff_of_true (Or.inl (hw' ▸ hsrc₁)) h)).elim⟩
    · have hw' : w' = w_in := ite_eq_right (hfw ▸ hne₁.symm)
      refine ⟨fun h => (hw'_cut_u' (iff_of_true h (Or.inl (hw' ▸ htgt₁)))).elim,
        fun _ => by_contra fun hn =>
          hf_cut₂' (iff_of_false (disjoint_left.mp hd (hfw ▸ hsrc₁)) hn)⟩
  have hwire_sd : ∀ α, GateSatisfies I S₁ α → α f = (α w' ^^ neg) := by
    intro α hsat
    have h := hsd₁ α hsat
    dsimp only [w']
    rcases hf₁ with hfw | hfw
    · rw [ite_eq_left hfw, hfw, h]; cases α w_in <;> cases neg <;> rfl
    · rw [ite_eq_right (hfw ▸ hne₁.symm), hfw, h]
  let α₀_fn (α : Edge c → Bool) : Edge c → Bool := fun g => if g = f then (α w' ^^ neg) else α g
  have hwire_rl : ∀ α, ∃ β₁, EqOn β₁ (α₀_fn α) (internalEdges c S₁)ᶜ ∧ GateSatisfies I S₁ β₁ := by
    intro α
    refine hrl₁ (α₀_fn α) ?_
    dsimp only [α₀_fn, w']
    rcases hf₁ with hfw | hfw
    · have hne_of : w_out ≠ f := fun h => hne₁ (hfw.symm.trans h.symm)
      rw [ite_eq_right hne_of, ite_eq_left hfw.symm, ite_eq_left hfw]
      cases α w_out <;> cases neg <;> rfl
    · have hne_fi : f ≠ w_in := fun h => hne₁ (h.symm.trans hfw)
      rw [ite_eq_left hfw.symm, ite_eq_right hne_fi, ite_eq_right hne_fi.symm]
  refine ⟨fun v hv => hv.elim (hcl₁ v) (hcl₂ v), hnc_u, ?_⟩
  intro p q e hpq hrem he_u
  -- For any edge `g ∈ edgeCut (S₁ ∪ S₂)` with `g ≠ w'`, its orientation in `S₁ ∪ S₂` matches `S₂`.
  have horient_other {g : Edge c} (hg_u : g ∈ (graph c).edgeCut (S₁ ∪ S₂)) (hg_ne : g ≠ w') :
      g ∈ (graph c).edgeCut S₂ \ {f} ∧
        (src g ∈ S₁ ∪ S₂ → src g ∈ S₂) ∧ (tgt g ∈ S₁ ∪ S₂ → tgt g ∈ S₂) := by
    rw [hcut_u, mem_insert_iff] at hg_u
    have hg₂ : g ∈ (graph c).edgeCut S₂ \ {f} := hg_u.resolve_left hg_ne
    have hg_not_s₁ : src g ∉ S₁ ∧ tgt g ∉ S₁ := by
      have hg_not_cut₁ : g ∉ (graph c).edgeCut S₁ := fun hm => by
        have : g ∈ (graph c).edgeCut S₁ \ {f} := ⟨hm, hg₂.2⟩
        rw [hs₁, mem_singleton_iff] at this
        exact hg_ne this
      have hiff : src g ∈ S₁ ↔ tgt g ∈ S₁ := by
        simpa [Multigraph.mem_edgeCut] using hg_not_cut₁
      by_cases hs_in : src g ∈ S₁
      · have ht_in : tgt g ∈ S₁ := hiff.mp hs_in
        exact (hg₂.1 (iff_of_false (disjoint_left.mp hd hs_in) (disjoint_left.mp hd ht_in))).elim
      · exact ⟨hs_in, fun ht_in => hs_in (hiff.mpr ht_in)⟩
    exact ⟨hg₂, fun h => h.resolve_left hg_not_s₁.1, fun h => h.resolve_left hg_not_s₁.2⟩
  -- Split on which of `e, p, q` equals `w'`.
  have hw'_mem : w' = e ∨ w' = p ∨ w' = q := by
    by_cases hwe : w' = e
    · exact Or.inl hwe
    · have : w' ∈ (graph c).edgeCut (S₁ ∪ S₂) \ {e} := ⟨by rw [hcut_u]; simp, hwe⟩
      rw [hrem] at this
      exact Or.inr (by simpa using this)
  rcases hw'_mem with hwe | hwp | hwq
  · -- Case 1: `w' = e`.
    have hrem₂ : (graph c).edgeCut S₂ \ {f} = {p, q} := by
      have h1 := insert_sdiff_self_of_notMem hw'_not_s₂f
      rw [← hcut_u, hwe, hrem] at h1
      exact h1.symm
    have hp_s₂f : p ∈ (graph c).edgeCut S₂ \ {f} := by rw [hrem₂]; simp
    have hq_s₂f : q ∈ (graph c).edgeCut S₂ \ {f} := by rw [hrem₂]; simp
    obtain ⟨h₂_out, h₂_in⟩ := hpin₂ p q f hpq hrem₂ hf_cut₂
    constructor
    · intro hsrc_e
      obtain ⟨rel₀, hU₀, hsd₀, hrl₀⟩ := h₂_out (horient.1 (hwe ▸ hsrc_e))
      have hU : U2OutRel fun a b x => rel₀ a b (x ^^ neg) := by
        simpa only [Bool.xor_false] using hU₀.flip false false neg
      refine ⟨fun a b x => rel₀ a b (x ^^ neg), hU, ?_, ?_⟩
      · intro α hsat
        dsimp only
        rw [← hwe, ← hwire_sd α (fun v hv => hsat v (Or.inl hv))]
        exact hsd₀ α fun v hv => hsat v (Or.inr hv)
      · intro α hrel
        refine patch_union hd hint α (α₀_fn α) (fun g hne => ite_eq_right hne) (hwire_rl α)
          fun β₁ hβ₁ => hrl₀ β₁ ?_
        have hp_eq : β₁ p = α p := (hβ₁ hp_s₂f.1).trans (ite_eq_right hp_s₂f.2)
        have hq_eq : β₁ q = α q := (hβ₁ hq_s₂f.1).trans (ite_eq_right hq_s₂f.2)
        have hf_eq : β₁ f = (α e ^^ neg) := by
          rw [hβ₁ hf_cut₂, ← hwe]; exact ite_eq_left rfl
        rwa [hp_eq, hq_eq, hf_eq]
    · intro htgt_e
      obtain ⟨rel₀, hI₀, hsd₀, hrl₀⟩ := h₂_in (horient.2 (hwe ▸ htgt_e))
      have hI : U2InRel fun a b x => rel₀ a b (x ^^ neg) := by
        simpa only [Bool.xor_false] using hI₀.flip false false neg
      refine ⟨fun a b x => rel₀ a b (x ^^ neg), hI, ?_, ?_⟩
      · intro α hsat
        dsimp only
        rw [← hwe, ← hwire_sd α (fun v hv => hsat v (Or.inl hv))]
        exact hsd₀ α fun v hv => hsat v (Or.inr hv)
      · intro α hrel
        refine patch_union hd hint α (α₀_fn α) (fun g hne => ite_eq_right hne) (hwire_rl α)
          fun β₁ hβ₁ => hrl₀ β₁ ?_
        have hp_eq : β₁ p = α p := (hβ₁ hp_s₂f.1).trans (ite_eq_right hp_s₂f.2)
        have hq_eq : β₁ q = α q := (hβ₁ hq_s₂f.1).trans (ite_eq_right hq_s₂f.2)
        have hf_eq : β₁ f = (α e ^^ neg) := by
          rw [hβ₁ hf_cut₂, ← hwe]; exact ite_eq_left rfl
        rwa [hp_eq, hq_eq, hf_eq]
  · -- Case 2: `w' = p`.
    have he_ne_w : e ≠ w' := fun h => by
      have hm : p ∈ (graph c).edgeCut (S₁ ∪ S₂) \ {e} := by rw [hrem]; simp
      exact hm.2 (hwp.symm.trans h.symm)
    obtain ⟨he₂, he_src, he_tgt⟩ := horient_other he_u he_ne_w
    have hq_rem : q ∈ (graph c).edgeCut (S₁ ∪ S₂) \ {e} := by rw [hrem]; simp
    obtain ⟨hq₂, _, _⟩ := horient_other hq_rem.1 (hwp ▸ hpq.symm)
    have hfq : f ≠ q := Ne.symm hq₂.2
    have hrem₂ : (graph c).edgeCut S₂ \ {e} = {f, q} := by
      ext g
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hg₂, hge⟩
        by_cases hgf : g = f
        · exact Or.inl hgf
        · have hgu : g ∈ (graph c).edgeCut (S₁ ∪ S₂) \ {e} :=
            ⟨by rw [hcut_u]; exact Or.inr ⟨hg₂, hgf⟩, hge⟩
          rw [hrem] at hgu
          rcases hgu with hgp | hgq
          · exact (hw'_not_cut₂ (hwp.trans hgp.symm ▸ hg₂)).elim
          · exact Or.inr hgq
      · rintro (rfl | rfl)
        · exact ⟨hf_cut₂, Ne.symm he₂.2⟩
        · exact ⟨hq₂.1, hq_rem.2⟩
    obtain ⟨h₂_out, h₂_in⟩ := hpin₂ f q e hfq hrem₂ he₂.1
    constructor
    · intro hsrc_e
      obtain ⟨rel₀, hU₀, hsd₀, hrl₀⟩ := h₂_out (he_src hsrc_e)
      have hU : U2OutRel fun a b x => rel₀ (a ^^ neg) b x := by
        simpa only [Bool.xor_false] using hU₀.flip neg false false
      refine ⟨fun a b x => rel₀ (a ^^ neg) b x, hU, ?_, ?_⟩
      · intro α hsat
        dsimp only
        rw [← hwp, ← hwire_sd α (fun v hv => hsat v (Or.inl hv))]
        exact hsd₀ α fun v hv => hsat v (Or.inr hv)
      · intro α hrel
        refine patch_union hd hint α (α₀_fn α) (fun g hne => ite_eq_right hne) (hwire_rl α)
          fun β₁ hβ₁ => hrl₀ β₁ ?_
        have hf_eq : β₁ f = (α p ^^ neg) := by
          rw [hβ₁ hf_cut₂, ← hwp]; exact ite_eq_left rfl
        have hq_eq : β₁ q = α q := (hβ₁ hq₂.1).trans (ite_eq_right hq₂.2)
        have he_eq : β₁ e = α e := (hβ₁ he₂.1).trans (ite_eq_right he₂.2)
        rwa [hf_eq, hq_eq, he_eq]
    · intro htgt_e
      obtain ⟨rel₀, hI₀, hsd₀, hrl₀⟩ := h₂_in (he_tgt htgt_e)
      have hI : U2InRel fun a b x => rel₀ (a ^^ neg) b x := by
        simpa only [Bool.xor_false] using hI₀.flip neg false false
      refine ⟨fun a b x => rel₀ (a ^^ neg) b x, hI, ?_, ?_⟩
      · intro α hsat
        dsimp only
        rw [← hwp, ← hwire_sd α (fun v hv => hsat v (Or.inl hv))]
        exact hsd₀ α fun v hv => hsat v (Or.inr hv)
      · intro α hrel
        refine patch_union hd hint α (α₀_fn α) (fun g hne => ite_eq_right hne) (hwire_rl α)
          fun β₁ hβ₁ => hrl₀ β₁ ?_
        have hf_eq : β₁ f = (α p ^^ neg) := by
          rw [hβ₁ hf_cut₂, ← hwp]; exact ite_eq_left rfl
        have hq_eq : β₁ q = α q := (hβ₁ hq₂.1).trans (ite_eq_right hq₂.2)
        have he_eq : β₁ e = α e := (hβ₁ he₂.1).trans (ite_eq_right he₂.2)
        rwa [hf_eq, hq_eq, he_eq]
  · -- Case 3: `w' = q`.
    have he_ne_w : e ≠ w' := fun h => by
      have hm : q ∈ (graph c).edgeCut (S₁ ∪ S₂) \ {e} := by rw [hrem]; simp
      exact hm.2 (hwq.symm.trans h.symm)
    obtain ⟨he₂, he_src, he_tgt⟩ := horient_other he_u he_ne_w
    have hp_rem : p ∈ (graph c).edgeCut (S₁ ∪ S₂) \ {e} := by rw [hrem]; simp
    obtain ⟨hp₂, _, _⟩ := horient_other hp_rem.1 (hwq ▸ hpq)
    have hpf : p ≠ f := hp₂.2
    have hrem₂ : (graph c).edgeCut S₂ \ {e} = {p, f} := by
      ext g
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hg₂, hge⟩
        by_cases hgf : g = f
        · exact Or.inr hgf
        · have hgu : g ∈ (graph c).edgeCut (S₁ ∪ S₂) \ {e} :=
            ⟨by rw [hcut_u]; exact Or.inr ⟨hg₂, hgf⟩, hge⟩
          rw [hrem] at hgu
          rcases hgu with hgp | hgq
          · exact Or.inl hgp
          · exact (hw'_not_cut₂ (hwq.trans hgq.symm ▸ hg₂)).elim
      · rintro (rfl | rfl)
        · exact ⟨hp₂.1, hp_rem.2⟩
        · exact ⟨hf_cut₂, Ne.symm he₂.2⟩
    obtain ⟨h₂_out, h₂_in⟩ := hpin₂ p f e hpf hrem₂ he₂.1
    constructor
    · intro hsrc_e
      obtain ⟨rel₀, hU₀, hsd₀, hrl₀⟩ := h₂_out (he_src hsrc_e)
      have hU : U2OutRel fun a b x => rel₀ a (b ^^ neg) x := by
        simpa only [Bool.xor_false] using hU₀.flip false neg false
      refine ⟨fun a b x => rel₀ a (b ^^ neg) x, hU, ?_, ?_⟩
      · intro α hsat
        dsimp only
        rw [← hwq, ← hwire_sd α (fun v hv => hsat v (Or.inl hv))]
        exact hsd₀ α fun v hv => hsat v (Or.inr hv)
      · intro α hrel
        refine patch_union hd hint α (α₀_fn α) (fun g hne => ite_eq_right hne) (hwire_rl α)
          fun β₁ hβ₁ => hrl₀ β₁ ?_
        have hp_eq : β₁ p = α p := (hβ₁ hp₂.1).trans (ite_eq_right hp₂.2)
        have hf_eq : β₁ f = (α q ^^ neg) := by
          rw [hβ₁ hf_cut₂, ← hwq]; exact ite_eq_left rfl
        have he_eq : β₁ e = α e := (hβ₁ he₂.1).trans (ite_eq_right he₂.2)
        rwa [hp_eq, hf_eq, he_eq]
    · intro htgt_e
      obtain ⟨rel₀, hI₀, hsd₀, hrl₀⟩ := h₂_in (he_tgt htgt_e)
      have hI : U2InRel fun a b x => rel₀ a (b ^^ neg) x := by
        simpa only [Bool.xor_false] using hI₀.flip false neg false
      refine ⟨fun a b x => rel₀ a (b ^^ neg) x, hI, ?_, ?_⟩
      · intro α hsat
        dsimp only
        rw [← hwq, ← hwire_sd α (fun v hv => hsat v (Or.inl hv))]
        exact hsd₀ α fun v hv => hsat v (Or.inr hv)
      · intro α hrel
        refine patch_union hd hint α (α₀_fn α) (fun g hne => ite_eq_right hne) (hwire_rl α)
          fun β₁ hβ₁ => hrl₀ β₁ ?_
        have hp_eq : β₁ p = α p := (hβ₁ hp₂.1).trans (ite_eq_right hp₂.2)
        have hf_eq : β₁ f = (α q ^^ neg) := by
          rw [hβ₁ hf_cut₂, ← hwq]; exact ite_eq_left rfl
        have he_eq : β₁ e = α e := (hβ₁ he₂.1).trans (ite_eq_right he₂.2)
        rwa [hp_eq, hf_eq, he_eq]

private theorem internalEdges_singleton_empty (c : Circuit σ m_in m_out) (v : Vertex c) :
    internalEdges c {v} = ∅ := by
  ext e
  simp only [internalEdges, mem_ofPred_eq, mem_singleton_iff, mem_empty_iff_false, iff_false]
  rintro ⟨hs, ht⟩
  exact loopless e (hs.trans ht.symm)

private theorem clean_junction_singleton {c : Circuit σ m_in m_out} (I : Interpretation σ Bool)
    (j : Junction c) :
    CleanWire I {.junction j} ∨ CleanBlock3 I {.junction j} := by
  rcases j with ⟨w, ⟨idx, hidx⟩⟩
  set j : Junction c := ⟨w, ⟨idx, hidx⟩⟩
  have hcl : ∀ v ∈ ({Vertex.junction j} : Set (Vertex c)), IsCleanVertex v := by
    intro v hv; rw [mem_singleton_iff] at hv; subst hv
    exact ⟨fun _ _ h => (nomatch h), fun _ h => (nomatch h)⟩
  have hint0 : (internalEdges c {.junction j})ᶜ = univ := by
    rw [internalEdges_singleton_empty, compl_empty]
  by_cases hnext : idx + 1 < fanout c w
  · -- Non-last junction: `CleanBlock3` (`copyRel`)
    right
    set e_in : Edge c := .feed j
    set e_d : Edge c := .deliver j
    set e_f : Edge c := .feed ⟨w, ⟨idx + 1, hnext⟩⟩
    have h01 : e_in ≠ e_d := fun h => nomatch h
    have h02 : e_in ≠ e_f := fun h => by
      have := congrArg (fun x : Junction c => (x.2 : ℕ)) (Edge.feed.inj h)
      dsimp [j] at this; omega
    have h12 : e_d ≠ e_f := fun h => nomatch h
    have hcut : (graph c).edgeCut {.junction j} = {e_in, e_d, e_f} := by
      ext e
      rw [Multigraph.edgeCut_singleton _ loopless]
      simp only [Multigraph.mem_incidenceSet, graph_src, graph_tgt, mem_insert_iff,
        mem_singleton_iff]
      constructor
      · rintro (hs | ht)
        · rcases e with ⟨w', ⟨k, hk⟩⟩ | j'
          · cases k with
            | zero => cases hs
            | succ k =>
              have hj := Vertex.junction.inj hs
              obtain ⟨rfl, hfin⟩ := Sigma.mk.inj_iff.mp hj
              have hk_eq : k = idx := Fin.mk.inj_iff.mp (eq_of_heq hfin)
              subst hk_eq
              exact Or.inr (Or.inr rfl)
          · cases hs; exact Or.inr (Or.inl rfl)
        · rcases e with j' | j'
          · cases ht; exact Or.inl rfl
          · change owner (junctionEquiv c j') = _ at ht
            generalize junctionEquiv c j' = t at ht
            rcases t with a | o <;> cases ht
      · rintro (rfl | rfl | rfl)
        · exact Or.inr rfl
        · exact Or.inl rfl
        · exact Or.inl rfl
    have hnc : ((graph c).edgeCut {.junction j}).ncard = 3 := by
      rw [hcut, ncard_insert_of_notMem (by simp [h01, h02]), ncard_pair h12]
    have hsat_iff (α : Edge c → Bool) :
        GateSatisfies I {.junction j} α ↔ α e_d = α e_in ∧ α e_f = α e_in := by
      simp only [GateSatisfies, mem_singleton_iff, forall_eq, Constraint]
      constructor
      · intro h; exact ⟨h e_d rfl, h e_f rfl⟩
      · rintro ⟨hd, hf⟩ e hs
        have hmem : e ∈ (graph c).edgeCut {.junction j} := by
          rw [Multigraph.edgeCut_singleton _ loopless]; exact Or.inl hs
        rw [hcut] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact (feeder_ne_junction j hs).elim
        · exact hd
        · exact hf
    refine ⟨hcl, hnc, fun p q e hpq hrem he => ?_⟩
    have hall_eq (α : Edge c → Bool) :
        (α e_d = α e_in ∧ α e_f = α e_in) ↔ copyPolarRel false false (α p) (α q) (α e) = true := by
      have hp_rem : p ∈ (graph c).edgeCut {.junction j} \ {e} := by rw [hrem]; simp
      have hq_rem : q ∈ (graph c).edgeCut {.junction j} \ {e} := by rw [hrem]; simp
      have hp_mem : p ∈ ({e_in, e_d, e_f} : Set (Edge c)) := hcut ▸ hp_rem.1
      have hq_mem : q ∈ ({e_in, e_d, e_f} : Set (Edge c)) := hcut ▸ hq_rem.1
      have he_mem : e ∈ ({e_in, e_d, e_f} : Set (Edge c)) := by rwa [← hcut]
      have hp_ne_e : p ≠ e := hp_rem.2
      have hq_ne_e : q ≠ e := hq_rem.2
      rcases hp_mem with rfl | rfl | rfl <;> rcases hq_mem with rfl | rfl | rfl <;>
        rcases he_mem with rfl | rfl | rfl
      all_goals first
        | exact (hpq rfl).elim
        | exact (hp_ne_e rfl).elim
        | exact (hq_ne_e rfl).elim
        | (cases α e_in <;> cases α e_d <;> cases α e_f <;> decide)
    exact ⟨fun _ => ⟨copyPolarRel false false, .copy false false,
        fun α h => (hall_eq α).mp ((hsat_iff α).mp h),
        fun α h => ⟨α, by rw [hint0]; exact eqOn_refl _ _, (hsat_iff α).mpr ((hall_eq α).mpr h)⟩⟩,
      fun _ => ⟨copyPolarRel false false, .copy false false,
        fun α h => (hall_eq α).mp ((hsat_iff α).mp h),
        fun α h => ⟨α, by rw [hint0]; exact eqOn_refl _ _, (hsat_iff α).mpr ((hall_eq α).mpr h)⟩⟩⟩
  · -- Last junction: `CleanWire` (`neg = false`)
    left
    set e_in : Edge c := .feed j
    set e_d : Edge c := .deliver j
    have h01 : e_in ≠ e_d := fun h => nomatch h
    have hcut : (graph c).edgeCut {.junction j} = {e_in, e_d} := by
      ext e
      rw [Multigraph.edgeCut_singleton _ loopless]
      simp only [Multigraph.mem_incidenceSet, graph_src, graph_tgt, mem_insert_iff,
        mem_singleton_iff]
      constructor
      · rintro (hs | ht)
        · rcases e with ⟨w', ⟨k, hk⟩⟩ | j'
          · cases k with
            | zero => cases hs
            | succ k =>
              have hj := Vertex.junction.inj hs
              obtain ⟨rfl, hfin⟩ := Sigma.mk.inj_iff.mp hj
              have hk_eq : k = idx := Fin.mk.inj_iff.mp (eq_of_heq hfin)
              omega
          · cases hs; exact Or.inr rfl
        · rcases e with j' | j'
          · cases ht; exact Or.inl rfl
          · change owner (junctionEquiv c j') = _ at ht
            generalize junctionEquiv c j' = t at ht
            rcases t with a | o <;> cases ht
      · rintro (rfl | rfl) <;> [exact Or.inr rfl; exact Or.inl rfl]
    refine ⟨e_in, e_d, false, hcl, h01, hcut, rfl, rfl, ?_, ?_⟩
    · intro α hsat
      simp only [Bool.xor_false]
      exact hsat (.junction j) rfl e_d rfl
    · intro α hα
      simp only [Bool.xor_false] at hα
      refine ⟨α, by rw [hint0]; exact eqOn_refl _ _, ?_⟩
      simp only [GateSatisfies, mem_singleton_iff, forall_eq, Constraint]
      intro e hs
      have hmem : e ∈ (graph c).edgeCut {.junction j} := by
        rw [Multigraph.edgeCut_singleton _ loopless]; exact Or.inl hs
      rw [hcut] at hmem
      rcases hmem with rfl | rfl
      · exact (feeder_ne_junction j hs).elim
      · exact hα

private theorem clean_unary_gate_singleton {c : Circuit σ m_in m_out} {I : Interpretation σ Bool}
    {g : Fin c.size} (hg : Reach c (.gate g)) (h1 : σ.Arity (c.program.lines g).op = 1)
    (hnonconst : ¬∃ b : Bool, ∀ x, I (c.program.lines g).op x = b) :
    CleanWire I {.signal ⟨.gate g, hg⟩} := by
  set v : Vertex c := .signal ⟨.gate g, hg⟩
  set a0 : Fin (σ.Arity (c.program.lines g).op) := ⟨0, by omega⟩
  set e_in : Edge c := argEdge hg a0
  set e_out : Edge c := head ⟨.gate g, hg⟩
  let neg : Bool := I (c.program.lines g).op (fun _ => false)
  have hcl : ∀ u ∈ ({v} : Set (Vertex c)), IsCleanVertex u := by
    intro u hu; rw [mem_singleton_iff] at hu; rw [hu]
    exact ⟨fun _ _ h => (by dsimp [v] at h; cases h), fun _ h => (by dsimp [v] at h; cases h)⟩
  have hne : e_in ≠ e_out := fun h => nomatch h
  have hcut : (graph c).edgeCut {v} = {e_in, e_out} := by
    ext e
    rw [Multigraph.edgeCut_singleton _ loopless]
    simp only [Multigraph.mem_incidenceSet, graph_src, graph_tgt, mem_insert_iff,
      mem_singleton_iff]
    constructor
    · rintro (hs | ht)
      · exact Or.inr (eq_head_of_src_eq_signal hs)
      · obtain ⟨⟨⟨g', a⟩, hg'⟩, hwg, rfl⟩ := exists_slot_of_tgt_eq_signal ht
        dsimp at hwg
        obtain rfl : g' = g := Wire.gate.inj hwg
        have ha : a = a0 := Fin.ext (by have := a.isLt; dsimp [a0]; omega)
        subst ha
        exact Or.inl rfl
    · rintro (rfl | rfl)
      · exact Or.inr (tgt_deliverEdge _)
      · exact Or.inl rfl
  have hf_eq (b : Bool) : I (c.program.lines g).op (fun _ => b) = (b ^^ neg) := by
    have hdiff : I (c.program.lines g).op (fun _ => true) ≠ neg := by
      intro heq
      refine hnonconst ⟨neg, fun x => ?_⟩
      have hx : x = (fun _ => x a0) :=
        funext fun idx => congrArg x (Fin.ext (by have := idx.isLt; dsimp [a0]; omega))
      rw [hx]
      cases x a0
      · rfl
      · exact heq
    cases b
    · simp [neg]
    · dsimp only [neg] at hdiff ⊢
      cases hval : I (c.program.lines g).op (fun _ => false) <;>
        cases hval1 : I (c.program.lines g).op (fun _ => true) <;> simp_all
  have harg_eq (α : Edge c → Bool) :
      (fun a => α (argEdge hg a)) = fun _ => α e_in := by
    funext a
    have ha : a = a0 := Fin.ext (by have := a.isLt; dsimp [a0]; omega)
    rw [ha]
  have hint0 : (internalEdges c {v})ᶜ = univ := by
    rw [internalEdges_singleton_empty, compl_empty]
  refine ⟨e_in, e_out, neg, hcl, hne, hcut, tgt_deliverEdge _, rfl, ?_, ?_⟩
  · intro α hsat
    have h := hsat v rfl
    change α e_out = I (c.program.lines g).op (fun a => α (argEdge hg a)) at h
    rw [h, harg_eq, hf_eq]
  · intro α hα
    refine ⟨α, by rw [hint0]; exact eqOn_refl _ _, ?_⟩
    simp only [GateSatisfies, mem_singleton_iff, forall_eq]
    change α e_out = I (c.program.lines g).op (fun a => α (argEdge hg a))
    rw [harg_eq, hf_eq]
    exact hα

private theorem clean_binary_gate_singleton {c : Circuit σ m_in m_out} {I : Interpretation σ Bool}
    (hU2 : I.IsU2) {g : Fin c.size} (hg : Reach c (.gate g))
    (h2 : σ.Arity (c.program.lines g).op = 2) :
    CleanBlock3 I {.signal ⟨.gate g, hg⟩} := by
  obtain ⟨nx, ny, nz, hand⟩ := hU2.binary_andType (c.program.lines g).op h2
  set v : Vertex c := .signal ⟨.gate g, hg⟩
  set a0 : Fin (σ.Arity (c.program.lines g).op) := ⟨0, by omega⟩
  set a1 : Fin (σ.Arity (c.program.lines g).op) := ⟨1, by omega⟩
  set e0 : Edge c := argEdge hg a0
  set e1 : Edge c := argEdge hg a1
  set e_out : Edge c := head ⟨.gate g, hg⟩
  have hcl : ∀ u ∈ ({v} : Set (Vertex c)), IsCleanVertex u := by
    intro u hu; rw [mem_singleton_iff] at hu; rw [hu]
    exact ⟨fun _ _ h => (by dsimp [v] at h; cases h), fun _ h => (by dsimp [v] at h; cases h)⟩
  have h01 : e0 ≠ e1 := fun h => by
    have hdel := Edge.deliver.inj h
    have hcon := (junctionEquiv c).symm.injective hdel
    have hsl := Sum.inl.inj hcon
    have hfin : (a0 : ℕ) = (a1 : ℕ) := congrArg (fun s : Slot c => (s.1.2 : ℕ)) hsl
    dsimp [a0, a1] at hfin; omega
  have h02 : e0 ≠ e_out := fun h => nomatch h
  have h12 : e1 ≠ e_out := fun h => nomatch h
  have hcut : (graph c).edgeCut {v} = {e0, e1, e_out} := by
    ext e
    rw [Multigraph.edgeCut_singleton _ loopless]
    simp only [Multigraph.mem_incidenceSet, graph_src, graph_tgt, mem_insert_iff,
      mem_singleton_iff]
    constructor
    · rintro (hs | ht)
      · exact Or.inr (Or.inr (eq_head_of_src_eq_signal hs))
      · obtain ⟨⟨⟨g', a⟩, hg'⟩, hwg, rfl⟩ := exists_slot_of_tgt_eq_signal ht
        dsimp at hwg
        obtain rfl : g' = g := Wire.gate.inj hwg
        have hlt : (a : ℕ) < 2 := h2 ▸ a.isLt
        rcases (show (a : ℕ) = 0 ∨ (a : ℕ) = 1 by omega) with hz | ho
        · have ha : a = a0 := Fin.ext hz
          subst ha; exact Or.inl rfl
        · have ha : a = a1 := Fin.ext ho
          subst ha; exact Or.inr (Or.inl rfl)
    · rintro (rfl | rfl | rfl)
      · exact Or.inr (tgt_deliverEdge _)
      · exact Or.inr (tgt_deliverEdge _)
      · exact Or.inl rfl
  have hnc : ((graph c).edgeCut {v}).ncard = 3 := by
    rw [hcut, ncard_insert_of_notMem (by simp [h01, h02]), ncard_pair h12]
  have hint0 : (internalEdges c {v})ᶜ = univ := by
    rw [internalEdges_singleton_empty, compl_empty]
  have hsat_iff (α : Edge c → Bool) :
      GateSatisfies I {v} α ↔ andTypeRel nx ny nz 2 (α e0) (α e1) (α e_out) = true := by
    simp only [GateSatisfies, mem_singleton_iff, forall_eq]
    change (α e_out = I (c.program.lines g).op (fun a => α (argEdge hg a))) ↔ _
    let x2 : Fin 2 → Bool := ![α e0, α e1]
    have hx2 : (fun a => α (argEdge hg a)) = x2 ∘ Fin.cast h2 := by
      funext a
      have hlt : (a : ℕ) < 2 := h2 ▸ a.isLt
      rcases (show (a : ℕ) = 0 ∨ (a : ℕ) = 1 by omega) with hz | ho
      · have ha : a = a0 := Fin.ext hz
        subst ha; rfl
      · have ha : a = a1 := Fin.ext ho
        subst ha; rfl
    rw [hx2, hand x2]
    change (α e_out = (((α e0 ^^ nx) && (α e1 ^^ ny)) ^^ nz)) ↔
      ((((α e0 ^^ nx) && (α e1 ^^ ny)) ^^ nz) == α e_out) = true
    cases α e0 <;> cases α e1 <;> cases α e_out <;> cases nx <;> cases ny <;> cases nz <;> decide
  refine ⟨hcl, hnc, fun p q e hpq hrem he => ?_⟩
  have hp_rem : p ∈ (graph c).edgeCut {v} \ {e} := by rw [hrem]; simp
  have hq_rem : q ∈ (graph c).edgeCut {v} \ {e} := by rw [hrem]; simp
  have hp_mem : p ∈ ({e0, e1, e_out} : Set (Edge c)) := hcut ▸ hp_rem.1
  have hq_mem : q ∈ ({e0, e1, e_out} : Set (Edge c)) := hcut ▸ hq_rem.1
  have he_mem : e ∈ ({e0, e1, e_out} : Set (Edge c)) := by rwa [← hcut]
  have hp_ne_e : p ≠ e := hp_rem.2
  have hq_ne_e : q ≠ e := hq_rem.2
  have ht0 : tgt e0 = v := tgt_deliverEdge (.inl ⟨⟨g, a0⟩, hg⟩)
  have ht1 : tgt e1 = v := tgt_deliverEdge (.inl ⟨⟨g, a1⟩, hg⟩)
  have hsrc_e0 : src e0 ≠ v := fun h => loopless e0 (h.trans ht0.symm)
  have hsrc_e1 : src e1 ≠ v := fun h => loopless e1 (h.trans ht1.symm)
  have htgt_out : tgt e_out ≠ v := fun h => loopless e_out h.symm
  constructor
  · intro hsrc_e
    rw [mem_singleton_iff] at hsrc_e
    rcases he_mem with rfl | rfl | rfl
    · exact (hsrc_e0 hsrc_e).elim
    · exact (hsrc_e1 hsrc_e).elim
    · rcases hp_mem with rfl | rfl | rfl <;> rcases hq_mem with rfl | rfl | rfl
      all_goals first
        | exact (hpq rfl).elim | exact (hp_ne_e rfl).elim | exact (hq_ne_e rfl).elim
        | exact ⟨andTypeRel nx ny nz 2, .gate nx ny nz,
            fun α h => (hsat_iff α).mp h,
            fun α h => ⟨α, by rw [hint0]; exact eqOn_refl _ _, (hsat_iff α).mpr h⟩⟩
        | (refine ⟨andTypeRel ny nx nz 2, .gate ny nx nz, fun α h => ?_, fun α h => ?_⟩
           · have := (hsat_iff α).mp h
             revert this
             cases α e0 <;> cases α e1 <;> cases α e_out <;>
               cases nx <;> cases ny <;> cases nz <;> decide
           · refine ⟨α, by rw [hint0]; exact eqOn_refl _ _, (hsat_iff α).mpr ?_⟩
             revert h
             cases α e0 <;> cases α e1 <;> cases α e_out <;>
               cases nx <;> cases ny <;> cases nz <;> decide)
  · intro htgt_e
    rw [mem_singleton_iff] at htgt_e
    rcases he_mem with rfl | rfl | rfl
    · -- `e = e0`: remaining pins are `{e1, e_out}`
      rcases hp_mem with rfl | rfl | rfl <;> rcases hq_mem with rfl | rfl | rfl
      all_goals first
        | exact (hpq rfl).elim | exact (hp_ne_e rfl).elim | exact (hq_ne_e rfl).elim
        | (refine ⟨fun c' d' e' => andTypeRel nx ny nz 0 d' c' e',
              (U2InRel.gate nx ny nz 0).swap, fun α h => ?_, fun α h => ?_⟩
           · have := (hsat_iff α).mp h
             revert this
             cases α e0 <;> cases α e1 <;> cases α e_out <;>
               cases nx <;> cases ny <;> cases nz <;> decide
           · refine ⟨α, by rw [hint0]; exact eqOn_refl _ _, (hsat_iff α).mpr ?_⟩
             revert h
             cases α e0 <;> cases α e1 <;> cases α e_out <;>
               cases nx <;> cases ny <;> cases nz <;> decide)
        | (refine ⟨andTypeRel nx ny nz 0, U2InRel.gate nx ny nz 0, fun α h => ?_, fun α h => ?_⟩
           · have := (hsat_iff α).mp h
             revert this
             cases α e0 <;> cases α e1 <;> cases α e_out <;>
               cases nx <;> cases ny <;> cases nz <;> decide
           · refine ⟨α, by rw [hint0]; exact eqOn_refl _ _, (hsat_iff α).mpr ?_⟩
             revert h
             cases α e0 <;> cases α e1 <;> cases α e_out <;>
               cases nx <;> cases ny <;> cases nz <;> decide)
    · -- `e = e1`: remaining pins are `{e0, e_out}`
      rcases hp_mem with rfl | rfl | rfl <;> rcases hq_mem with rfl | rfl | rfl
      all_goals first
        | exact (hpq rfl).elim | exact (hp_ne_e rfl).elim | exact (hq_ne_e rfl).elim
        | (refine ⟨andTypeRel nx ny nz 1, U2InRel.gate nx ny nz 1, fun α h => ?_, fun α h => ?_⟩
           · have := (hsat_iff α).mp h
             revert this
             cases α e0 <;> cases α e1 <;> cases α e_out <;>
               cases nx <;> cases ny <;> cases nz <;> decide
           · refine ⟨α, by rw [hint0]; exact eqOn_refl _ _, (hsat_iff α).mpr ?_⟩
             revert h
             cases α e0 <;> cases α e1 <;> cases α e_out <;>
               cases nx <;> cases ny <;> cases nz <;> decide)
        | (refine ⟨fun c' d' e' => andTypeRel nx ny nz 1 d' c' e',
              (U2InRel.gate nx ny nz 1).swap, fun α h => ?_, fun α h => ?_⟩
           · have := (hsat_iff α).mp h
             revert this
             cases α e0 <;> cases α e1 <;> cases α e_out <;>
               cases nx <;> cases ny <;> cases nz <;> decide
           · refine ⟨α, by rw [hint0]; exact eqOn_refl _ _, (hsat_iff α).mpr ?_⟩
             revert h
             cases α e0 <;> cases α e1 <;> cases α e_out <;>
               cases nx <;> cases ny <;> cases nz <;> decide)
    · exact (htgt_out htgt_e).elim

private def IsDirtySingleton (c : Circuit σ m_in m_out) (I : Interpretation σ Bool) :
    Vertex c → Prop
  | .signal ⟨.input _, _⟩ => True
  | .signal ⟨.gate g, _⟩ => σ.Arity (c.program.lines g).op = 0 ∨
      (σ.Arity (c.program.lines g).op = 1 ∧ ∃ b : Bool, ∀ x, I (c.program.lines g).op x = b)
  | .junction _ => False
  | .output _ => True

private structure U2CompressState {n k : ℕ} (c : Circuit σ (n + k) 1) (I : Interpretation σ Bool)
    (d₀ : ℕ) where
  cmp : (graph c).Compression 3
  dirty : Finset (List (Vertex c))
  dirty_sub : dirty ⊆ cmp.blocks
  clean : ∀ B ∈ cmp.blocks, B ∉ dirty → CleanWire I {v | v ∈ B} ∨ CleanBlock3 I {v | v ∈ B}
  count : dirty.card + Nat.card (Vertex c) ≤ d₀ + cmp.blocks.card +
    {e | ∃ B ∈ cmp.blocks, src e ∈ B ∧ tgt e ∈ B}.ncard

/-- **Saturated `U₂` compression.** Every circuit `c : Circuit σ (n + k) 1` over a `U₂` basis `I`
has a saturated budget-`3` compression `Q` of `Compiler.graph c` together with a dirty block set
`dirty ⊆ Q.blocks` such that, whenever `1 < Nat.card Q.blocks`:
* every block `B ∉ dirty` is a `CleanBlock3 I {v | v ∈ B}`;
* `Nat.card Q.blocks + 2 * (hiddenNetwork c I Acc).read.ncard ≤ 2 * c.innerSize`; and
* `Nat.card Q.blocks + 2 * dirty.card ≤ 2 * c.innerSize + 2`. -/
theorem exists_u2_saturated {n k : ℕ} (c : Circuit σ (n + k) 1) {I : Interpretation σ Bool}
    (hU2 : I.IsU2) (Acc : Fin 1 → Set Bool) :
    ∃ (Q : (graph c).Compression 3) (dirty : Finset (List (Vertex c))),
      Q.Saturated ∧ dirty ⊆ Q.blocks ∧
      (1 < Nat.card Q.blocks →
        (∀ B ∈ Q.blocks, B ∉ dirty → CleanBlock3 I {v | v ∈ B}) ∧
        Nat.card Q.blocks + 2 * (hiddenNetwork c I Acc).read.ncard ≤ 2 * c.innerSize ∧
        Nat.card Q.blocks + 2 * dirty.card ≤ 2 * c.innerSize + 2) := by
  classical
  have := Fintype.ofFinite (Vertex c)
  have := Fintype.ofFinite (Edge c)
  have hfan : c.FanInAtMost 2 := hU2.fanInAtMost_two c
  have hdeg : (graph c).MaxDegreeLE 3 := maxDegreeLE le_rfl hfan
  let Dfin : Finset (Vertex c) := Finset.univ.filter (IsDirtySingleton c I)
  set d₀ : ℕ := Dfin.card
  -- Initial singleton state.
  let initCmp : (graph c).Compression 3 :=
    { blocks := Finset.univ.image fun v => [v]
      exists_mem := fun v => ⟨[v], Finset.mem_image_of_mem _ (Finset.mem_univ v),
        List.mem_singleton_self v⟩
      eq_of_mem := by simp
      nodup := by simp
      ne_nil := by simp
      ncard_edgeCut_le := by
        simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
          forall_apply_eq_imp_iff, List.mem_singleton]
        intro v
        refine (ncard_le_ncard fun e he => ?_).trans (hdeg v)
        simp only [Multigraph.mem_edgeCut, mem_ofPred_eq] at he
        rw [Multigraph.mem_incidenceSet]; tauto
      ncard_edgeCut_take_le := by simp
      card_le := by
        rw [Finset.card_image_of_injective _ List.singleton_injective, Finset.card_univ,
          Nat.card_eq_fintype_card]
        exact Nat.le_add_right _ _ }
  let initDirty : Finset (List (Vertex c)) := Dfin.image fun v => [v]
  have hinit : U2CompressState c I d₀ :=
    { cmp := initCmp
      dirty := initDirty
      dirty_sub := Finset.image_subset_image (Finset.filter_subset _ _)
      clean := by
        intro B hB hnot
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hB
        have hnotD : ¬IsDirtySingleton c I v := fun hd =>
          hnot (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hd⟩))
        have hset : {u : Vertex c | u ∈ [v]} = {v} := by ext u; simp
        rw [hset]
        cases v with
        | signal w =>
          rcases w with ⟨i | g, hw⟩
          · exact (hnotD trivial).elim
          · have har := hU2.arity_le_two (c.program.lines g).op
            rcases (show σ.Arity (c.program.lines g).op = 0 ∨
                σ.Arity (c.program.lines g).op = 1 ∨
                σ.Arity (c.program.lines g).op = 2 by omega) with h0 | h1 | h2
            · exact (hnotD (Or.inl h0)).elim
            · have hnc : ¬∃ b : Bool, ∀ x, I (c.program.lines g).op x = b :=
                fun hc => hnotD (Or.inr ⟨h1, hc⟩)
              exact Or.inl (clean_unary_gate_singleton hw h1 hnc)
            · exact Or.inr (clean_binary_gate_singleton hU2 hw h2)
        | junction j => exact clean_junction_singleton I j
        | output o => exact (hnotD trivial).elim
      count := by
        have hc1 : initDirty.card = d₀ :=
          Finset.card_image_of_injective _ List.singleton_injective
        have hc2 : initCmp.blocks.card = Nat.card (Vertex c) := by
          rw [Finset.card_image_of_injective _ List.singleton_injective, Finset.card_univ,
            Nat.card_eq_fintype_card]
        rw [hc1, hc2]
        exact Nat.le_add_right _ _ }
  -- Take a minimal-block state.
  obtain ⟨st, -, hmin⟩ :=
    (measure fun s : U2CompressState c I d₀ => s.cmp.blocks.card).wf.has_min univ ⟨hinit, trivial⟩
  -- Prove saturation by constructing the merged `U2CompressState`.
  have hsat : st.cmp.Saturated := by
    intro B₀ hB₀ B₀' hB₀' hne₀ hjoin₀
    by_contra! hcut₀
    suffices ∃ st' : U2CompressState c I d₀, st'.cmp.blocks.card < st.cmp.blocks.card by
      obtain ⟨st', hlt⟩ := this
      exact hmin st' trivial hlt
    -- Order `(B, B')` so `B'.length ≤ B.length`.
    have hex_pair : ∃ B B' : List (Vertex c), B ∈ st.cmp.blocks ∧ B' ∈ st.cmp.blocks ∧
        B ≠ B' ∧ B'.length ≤ B.length ∧
        ((graph c).edgeCut {v | v ∈ B} ∩ (graph c).edgeCut {v | v ∈ B'}).Nonempty ∧
        ((graph c).edgeCut ({v | v ∈ B} ∪ {v | v ∈ B'})).ncard ≤ 3 := by
      rcases le_total B₀'.length B₀.length with hle | hle
      · exact ⟨B₀, B₀', hB₀, hB₀', hne₀, hle, hjoin₀, hcut₀⟩
      · refine ⟨B₀', B₀, hB₀', hB₀, hne₀.symm, hle, ?_, ?_⟩
        · rwa [inter_comm]
        · rwa [union_comm]
    obtain ⟨B, B', hB, hB', hne, hlen, hjoin, hcut⟩ := hex_pair
    have hd_mem (v : Vertex c) (hv : v ∈ B) : v ∉ B' :=
      fun hv' => hne (st.cmp.eq_of_mem B hB B' hB' v hv hv')
    have hd_set : Disjoint {v : Vertex c | v ∈ B} {v : Vertex c | v ∈ B'} :=
      disjoint_left.mpr hd_mem
    have hrest (C : List (Vertex c)) (hC : C ∈ st.cmp.blocks) (hCB : C ≠ B) (hCB' : C ≠ B')
        (v : Vertex c) (hv : v ∈ C) : v ∉ B ∧ v ∉ B' :=
      ⟨fun h => hCB (st.cmp.eq_of_mem C hC B hB v hv h),
        fun h => hCB' (st.cmp.eq_of_mem C hC B' hB' v hv h)⟩
    let blocks' := insert (B ++ B') ((st.cmp.blocks.erase B).erase B')
    have hmem {C : List (Vertex c)} : C ∈ blocks' ↔
        C = B ++ B' ∨ (C ≠ B' ∧ C ≠ B ∧ C ∈ st.cmp.blocks) := by
      simp only [blocks', Finset.mem_insert, Finset.mem_erase]
    have hsup (C : List (Vertex c)) (hC : C ∈ st.cmp.blocks) :
        ∃ D ∈ blocks', ∀ v ∈ C, v ∈ D := by
      by_cases h : C = B ∨ C = B'
      · refine ⟨B ++ B', Finset.mem_insert_self _ _, ?_⟩
        rcases h with rfl | rfl <;> intro v hv <;> simp [hv]
      · rw [not_or] at h
        exact ⟨C, hmem.mpr (Or.inr ⟨h.2, h.1, hC⟩), fun v hv => hv⟩
    have hnot_app : B ++ B' ∉ st.cmp.blocks := by
      intro hm
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil B (st.cmp.ne_nil B hB)
      have heq := st.cmp.eq_of_mem (B ++ B') hm B hB v (List.mem_append_left _ hv) hv
      have hlen_eq := congrArg List.length heq
      rw [List.length_append] at hlen_eq
      have := List.length_pos_of_ne_nil (st.cmp.ne_nil B' hB')
      omega
    have hnot_er : B ++ B' ∉ (st.cmp.blocks.erase B).erase B' := by
      intro hm; simp only [Finset.mem_erase] at hm; exact hnot_app hm.2.2
    have hcard : blocks'.card + 1 = st.cmp.blocks.card := by
      dsimp only [blocks']
      rw [Finset.card_insert_of_notMem hnot_er, Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨hne.symm, hB'⟩), Finset.card_erase_of_mem hB]
      have := Finset.one_lt_card.mpr ⟨B, hB, B', hB', hne⟩
      omega
    have happ (L L' : List (Vertex c)) : {v | v ∈ L ++ L'} = {v | v ∈ L} ∪ {v | v ∈ L'} :=
      Set.ext fun _ => List.mem_append
    -- Internal edges increase by at least `m := |(edgeCut B ∩ edgeCut B')|`.
    set E_old : Set (Edge c) := {e | ∃ D ∈ st.cmp.blocks, src e ∈ D ∧ tgt e ∈ D}
    set E_join : Set (Edge c) := (graph c).edgeCut {v | v ∈ B} ∩ (graph c).edgeCut {v | v ∈ B'}
    set E_new : Set (Edge c) := {e | ∃ D ∈ blocks', src e ∈ D ∧ tgt e ∈ D}
    have hsub_E : E_old ∪ E_join ⊆ E_new := by
      rintro e (⟨C, hC, hs, ht⟩ | ⟨h1, h2⟩)
      · obtain ⟨D, hD, hCD⟩ := hsup C hC
        exact ⟨D, hD, hCD _ hs, hCD _ ht⟩
      · refine ⟨B ++ B', Finset.mem_insert_self _ _, ?_⟩
        have := hd_mem (src e)
        have := hd_mem (tgt e)
        simp only [Multigraph.mem_edgeCut, mem_ofPred_eq, graph_src, graph_tgt] at h1 h2
        simp only [List.mem_append]
        tauto
    have hdisj_E : Disjoint E_old E_join := by
      refine disjoint_left.mpr ?_
      rintro e ⟨D, hD, hs, ht⟩ ⟨h1, h2⟩
      have key (C : List (Vertex c)) (hC : C ∈ st.cmp.blocks)
          (h : e ∈ (graph c).edgeCut {v | v ∈ C}) : D = C := by
        simp only [Multigraph.mem_edgeCut, mem_ofPred_eq, graph_src, graph_tgt] at h
        by_cases hs' : src e ∈ C
        · exact st.cmp.eq_of_mem D hD C hC _ hs hs'
        · exact st.cmp.eq_of_mem D hD C hC _ ht (by tauto)
      exact hne ((key B hB h1).symm.trans (key B' hB' h2))
    have hE_inc : E_old.ncard + E_join.ncard ≤ E_new.ncard := by
      have := ncard_le_ncard hsub_E
      rwa [ncard_union_eq hdisj_E] at this
    have hm_pos : 1 ≤ E_join.ncard := hjoin.ncard_pos
    let cmp' : (graph c).Compression 3 :=
      { blocks := blocks'
        exists_mem := fun v => by
          obtain ⟨C, hC, hv⟩ := st.cmp.exists_mem v
          obtain ⟨D, hD, hCD⟩ := hsup C hC
          exact ⟨D, hD, hCD v hv⟩
        eq_of_mem := by
          simp only [hmem]
          rintro C (rfl | ⟨hC1, hC2, hC⟩) C' (rfl | ⟨hC1', hC2', hC'⟩) v hv hv'
          · rfl
          · rw [List.mem_append] at hv; have := hrest C' hC' hC2' hC1' v hv'; tauto
          · rw [List.mem_append] at hv'; have := hrest C hC hC2 hC1 v hv; tauto
          · exact st.cmp.eq_of_mem C hC C' hC' v hv hv'
        nodup := by
          simp only [hmem]
          rintro C (rfl | ⟨-, -, hC⟩)
          · exact List.nodup_append.mpr ⟨st.cmp.nodup B hB, st.cmp.nodup B' hB',
              fun a ha b hb hab => hd_mem a ha (hab ▸ hb)⟩
          · exact st.cmp.nodup C hC
        ne_nil := by
          simp only [hmem]
          rintro C (rfl | ⟨-, -, hC⟩)
          · exact List.append_ne_nil_of_left_ne_nil (st.cmp.ne_nil B hB) _
          · exact st.cmp.ne_nil C hC
        ncard_edgeCut_le := by
          simp only [hmem]
          rintro C (rfl | ⟨-, -, hC⟩)
          · rwa [happ]
          · exact st.cmp.ncard_edgeCut_le C hC
        ncard_edgeCut_take_le := by
          simp only [hmem]
          rintro C (rfl | ⟨-, -, hC⟩) idx hidx
          · rw [List.length_append] at hidx ⊢
            rw [List.take_append]
            rcases lt_or_ge idx B.length with hk' | hk'
            · rw [Nat.sub_eq_zero_of_le hk'.le, List.take_zero, List.append_nil]
              exact (st.cmp.ncard_edgeCut_take_le B hB idx hk').trans
                (Nat.mul_le_mul_left 3 (Nat.log_mono_right (by omega)))
            · rw [List.take_of_length_le hk']
              have hb : B'.length ≠ 0 := by omega
              have h1' := (graph c).ncard_edgeCut_union_le {v | v ∈ B}
                {v | v ∈ B'.take (idx - B.length)}
              have h3' := st.cmp.ncard_edgeCut_le B hB
              have h4' := st.cmp.ncard_edgeCut_take_le B' hB' (idx - B.length) (by omega)
              have h5' : Nat.log 2 B'.length + 1 ≤ Nat.log 2 (B.length + B'.length) := by
                rw [← Nat.log_mul_base one_lt_two hb]
                exact Nat.log_mono_right (by omega)
              have h6' := Nat.mul_le_mul_left 3 h5'
              simp only [Nat.mul_add, Nat.mul_one] at h6'
              rw [happ]
              omega
          · exact st.cmp.ncard_edgeCut_take_le C hC idx hidx
        card_le := by
          have := st.cmp.card_le
          change Nat.card (Vertex c) ≤ st.cmp.blocks.card + E_old.ncard at this
          change Nat.card (Vertex c) ≤ blocks'.card + E_new.ncard
          omega }
    -- Update `dirty'` according to the three merge cases.
    by_cases hdirty_or : B ∈ st.dirty ∨ B' ∈ st.dirty
    · let dirty' := insert (B ++ B') ((st.dirty.erase B).erase B')
      have hd_sub' : dirty' ⊆ blocks' := by
        intro C hC
        simp only [dirty', Finset.mem_insert, Finset.mem_erase] at hC
        rcases hC with rfl | ⟨h1, h2, h3⟩
        · exact Finset.mem_insert_self _ _
        · exact hmem.mpr (Or.inr ⟨h1, h2, st.dirty_sub h3⟩)
      have hd_card' : dirty'.card ≤ st.dirty.card := by
        have hnot_d : B ++ B' ∉ (st.dirty.erase B).erase B' := fun hm =>
          hnot_app (st.dirty_sub (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).2)
        dsimp only [dirty']
        rw [Finset.card_insert_of_notMem hnot_d]
        rcases hdirty_or with hBd | hB'd
        · have hle1 : ((st.dirty.erase B).erase B').card ≤ (st.dirty.erase B).card :=
            Finset.card_erase_le
          have hle2 := Finset.card_erase_of_mem hBd
          have := Finset.card_pos.mpr ⟨B, hBd⟩
          omega
        · by_cases hBd : B ∈ st.dirty
          · rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne.symm, hB'd⟩),
              Finset.card_erase_of_mem hBd]
            have := Finset.one_lt_card.mpr ⟨B, hBd, B', hB'd, hne⟩
            omega
          · have her : st.dirty.erase B = st.dirty := Finset.erase_eq_of_notMem hBd
            rw [her, Finset.card_erase_of_mem hB'd]
            have := Finset.card_pos.mpr ⟨B', hB'd⟩
            omega
      refine ⟨{ cmp := cmp', dirty := dirty', dirty_sub := hd_sub', clean := ?_, count := ?_ },
        by dsimp [cmp']; omega⟩
      · intro C hC hnotC
        rcases hmem.mp hC with rfl | ⟨h1, h2, hCo⟩
        · exact (hnotC (Finset.mem_insert_self _ _)).elim
        · refine st.clean C hCo fun hCd => hnotC ?_
          exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h1, Finset.mem_erase.mpr ⟨h2, hCd⟩⟩)
      · have hc := st.count
        change st.dirty.card + Nat.card (Vertex c) ≤ d₀ + st.cmp.blocks.card + E_old.ncard at hc
        change dirty'.card + Nat.card (Vertex c) ≤ d₀ + blocks'.card + E_new.ncard
        omega
    · rw [not_or] at hdirty_or
      by_cases hm2 : 2 ≤ E_join.ncard
      · let dirty' := insert (B ++ B') st.dirty
        have hd_sub' : dirty' ⊆ blocks' := by
          intro C hC
          rcases Finset.mem_insert.mp hC with rfl | hCd
          · exact Finset.mem_insert_self _ _
          · exact hmem.mpr (Or.inr ⟨fun h => hdirty_or.2 (h ▸ hCd),
              fun h => hdirty_or.1 (h ▸ hCd), st.dirty_sub hCd⟩)
        have hd_card' : dirty'.card ≤ st.dirty.card + 1 := Finset.card_insert_le _ _
        refine ⟨{ cmp := cmp', dirty := dirty', dirty_sub := hd_sub', clean := ?_, count := ?_ },
          by dsimp [cmp']; omega⟩
        · intro C hC hnotC
          rcases hmem.mp hC with rfl | ⟨_, _, hCo⟩
          · exact (hnotC (Finset.mem_insert_self _ _)).elim
          · exact st.clean C hCo fun hCd => hnotC (Finset.mem_insert_of_mem hCd)
        · have hc := st.count
          change st.dirty.card + Nat.card (Vertex c) ≤ d₀ + st.cmp.blocks.card + E_old.ncard at hc
          change dirty'.card + Nat.card (Vertex c) ≤ d₀ + blocks'.card + E_new.ncard
          omega
      · have hm1 : E_join.ncard = 1 := by omega
        have hd_sub' : st.dirty ⊆ blocks' := fun C hCd =>
          hmem.mpr (Or.inr ⟨fun h => hdirty_or.2 (h ▸ hCd),
            fun h => hdirty_or.1 (h ▸ hCd), st.dirty_sub hCd⟩)
        have hmerged_clean : CleanWire I {v | v ∈ B ++ B'} ∨ CleanBlock3 I {v | v ∈ B ++ B'} := by
          rw [happ]
          rcases st.clean B hB hdirty_or.1 with hwB | hbB <;>
            rcases st.clean B' hB' hdirty_or.2 with hwB' | hbB'
          · exact Or.inl (cleanWire_merge_wire hd_set hwB hwB' hm1)
          · exact Or.inr (cleanWire_merge_block3 hd_set hwB hbB' hm1)
          · rw [union_comm]
            exact Or.inr (cleanWire_merge_block3 hd_set.symm hwB' hbB
              (by rwa [inter_comm]))
          · -- Two `3`-pin blocks sharing `1` edge have cut size `3 + 3 - 2 = 4 > 3`, impossible!
            have hadd := (graph c).ncard_edgeCut_union_add hd_set
            have h3B := hbB.2.1
            have h3B' := hbB'.2.1
            change ((graph c).edgeCut ({v | v ∈ B} ∪ {v | v ∈ B'})).ncard + 2 * E_join.ncard =
              ((graph c).edgeCut {v | v ∈ B}).ncard + ((graph c).edgeCut {v | v ∈ B'}).ncard at hadd
            omega
        refine ⟨{ cmp := cmp', dirty := st.dirty, dirty_sub := hd_sub', clean := ?_, count := ?_ },
          by dsimp [cmp']; omega⟩
        · intro C hC hnotC
          rcases hmem.mp hC with rfl | ⟨_, _, hCo⟩
          · exact hmerged_clean
          · exact st.clean C hCo hnotC
        · have hc := st.count
          change st.dirty.card + Nat.card (Vertex c) ≤ d₀ + st.cmp.blocks.card + E_old.ncard at hc
          change st.dirty.card + Nat.card (Vertex c) ≤ d₀ + blocks'.card + E_new.ncard
          omega
  -- Now establish the three saturation consequences when `1 < Nat.card st.cmp.blocks`.
  refine ⟨st.cmp, st.dirty, hsat, st.dirty_sub, fun htwo => ?_⟩
  have hconn : (graph c).toSimpleGraph.Connected := connected c
  -- 1. Every non-dirty block has cut size `3`, so it cannot be `CleanWire` (`ncard = 2`).
  have hclean3 : ∀ B ∈ st.cmp.blocks, B ∉ st.dirty → CleanBlock3 I {v | v ∈ B} := by
    intro B hB hnot
    rcases st.clean B hB hnot with hw | hb
    · obtain ⟨e₁, e₂, _, _, hne12, hcut2, _⟩ := hw
      have hnc2 : ((graph c).edgeCut {v | v ∈ B}).ncard = 2 := by rw [hcut2, ncard_pair hne12]
      have hnc3 : ((graph c).edgeCut {v | v ∈ B}).ncard = 3 := by
        rw [← st.cmp.ncard_incidenceSet_quotient ⟨B, hB⟩]
        exact hsat.ncard_incidenceSet_quotient hconn htwo ⟨B, hB⟩
      omega
    · exact hb
  -- 2 & 3. Exact vertex/edge/dirty accounting on `Compiler.graph c`.
  have hsum_ext : 3 * Nat.card st.cmp.blocks = 2 * Nat.card st.cmp.external := by
    have hsum := st.cmp.sum_ncard_edgeCut
    have h3_each (B : st.cmp.blocks) : ((graph c).edgeCut {v | v ∈ B.1}).ncard = 3 := by
      rw [← st.cmp.ncard_incidenceSet_quotient B]
      exact hsat.ncard_incidenceSet_quotient hconn htwo B
    simp only [h3_each, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Nat.card_eq_fintype_card, mul_comm _ 3] at hsum
    exact hsum
  set E_int : Set (Edge c) := {e | ∃ B ∈ st.cmp.blocks, src e ∈ B ∧ tgt e ∈ B}
  have hcompl_ext : st.cmp.externalᶜ = E_int := by
    ext e
    simp only [Multigraph.Compression.external, mem_compl_iff, mem_ofPred_eq, not_not,
      graph_src, graph_tgt, E_int]
    exact ⟨fun h => ⟨_, (st.cmp.blockOf (src e)).2, st.cmp.mem_blockOf _,
        h ▸ st.cmp.mem_blockOf _⟩,
      fun ⟨B, hB, hs, ht⟩ => by
        rw [(st.cmp.mem_iff_blockOf_eq (B := ⟨B, hB⟩)).mp hs,
          (st.cmp.mem_iff_blockOf_eq (B := ⟨B, hB⟩)).mp ht]⟩
  have hE_part : Nat.card st.cmp.external + E_int.ncard = Nat.card (Edge c) := by
    rw [Nat.card_coe_set_eq, ← hcompl_ext, ncard_add_ncard_compl]
  have hblk_card : st.cmp.blocks.card = Nat.card st.cmp.blocks :=
    (Nat.card_eq_finsetCard st.cmp.blocks).symm
  -- Partition `Signal c` into inputs and arity `0`, `1` (const/wire), and `2` gates.
  let isConst1 (g : Fin c.size) : Prop :=
    ∃ b : Bool, ∀ x, I (c.program.lines g).op x = b
  let InpFin : Finset (Signal c) := Finset.univ.filter fun w =>
    match w.1 with | .input _ => true | .gate _ => false
  let G0Fin : Finset (Signal c) := Finset.univ.filter fun w =>
    match w.1 with | .input _ => false | .gate g => decide (σ.Arity (c.program.lines g).op = 0)
  let G1cFin : Finset (Signal c) := Finset.univ.filter fun w =>
    match w.1 with
    | .input _ => false
    | .gate g => decide (σ.Arity (c.program.lines g).op = 1 ∧ isConst1 g)
  let G1wFin : Finset (Signal c) := Finset.univ.filter fun w =>
    match w.1 with
    | .input _ => false
    | .gate g => decide (σ.Arity (c.program.lines g).op = 1 ∧ ¬isConst1 g)
  let G2Fin : Finset (Signal c) := Finset.univ.filter fun w =>
    match w.1 with | .input _ => false | .gate g => decide (σ.Arity (c.program.lines g).op = 2)
  have hsig_sum : Nat.card (Signal c) =
      InpFin.card + G0Fin.card + G1cFin.card + G1wFin.card + G2Fin.card := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    have hpart (w : Signal c) :
        (if w ∈ InpFin then 1 else 0) + (if w ∈ G0Fin then 1 else 0) +
          (if w ∈ G1cFin then 1 else 0) + (if w ∈ G1wFin then 1 else 0) +
          (if w ∈ G2Fin then 1 else 0) = 1 := by
      rcases w with ⟨i | g, hw⟩
      · simp [InpFin, G0Fin, G1cFin, G1wFin, G2Fin]
      · have har := hU2.arity_le_two (c.program.lines g).op
        rcases (show σ.Arity (c.program.lines g).op = 0 ∨
            σ.Arity (c.program.lines g).op = 1 ∨
            σ.Arity (c.program.lines g).op = 2 by omega) with h0 | h1 | h2
        · simp [InpFin, G0Fin, G1cFin, G1wFin, G2Fin, h0]
        · by_cases hc : isConst1 g
          · simp only [InpFin, G0Fin, G1cFin, G1wFin, G2Fin, Finset.mem_filter, Finset.mem_univ,
              true_and, decide_eq_true_eq, h1, hc, not_true_eq_false, and_false, and_true]
            decide
          · simp only [InpFin, G0Fin, G1cFin, G1wFin, G2Fin, Finset.mem_filter, Finset.mem_univ,
              true_and, decide_eq_true_eq, h1, hc, not_false_eq_true, and_false, and_true]
            decide
        · simp [InpFin, G0Fin, G1cFin, G1wFin, G2Fin, h2]
    have h1 (S : Finset (Signal c)) : S.card = ∑ w : Signal c, if w ∈ S then 1 else 0 := by
      rw [← Finset.card_filter, Finset.filter_univ_mem]
    rw [h1 InpFin, h1 G0Fin, h1 G1cFin, h1 G1wFin, h1 G2Fin,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    simp only [hpart, Finset.sum_const, smul_eq_mul, mul_one]
  -- Count `Slot c` by grouping over `Signal c`.
  have hslot_sum : Nat.card (Slot c) = G1cFin.card + G1wFin.card + 2 * G2Fin.card := by
    let slotOwner (s : Slot c) : Signal c := ⟨.gate s.1.1, s.2⟩
    have := Fintype.ofFinite (Slot c)
    have hu : (Finset.univ : Finset (Slot c)) = Finset.univ.biUnion fun w : Signal c =>
        Finset.univ.filter fun s : Slot c => slotOwner s = w := by
      ext s; simp
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, hu,
      Finset.card_biUnion (fun w₁ _ w₂ _ hne => Finset.disjoint_left.mpr fun s hs1 hs2 =>
        hne ((Finset.mem_filter.mp hs1).2.symm.trans (Finset.mem_filter.mp hs2).2))]
    have hfib (w : Signal c) :
        (Finset.univ.filter fun s : Slot c => slotOwner s = w).card =
          (if w ∈ G1cFin then 1 else 0) + (if w ∈ G1wFin then 1 else 0) +
            2 * (if w ∈ G2Fin then 1 else 0) := by
      rcases w with ⟨i | g, hw⟩
      · have hem : (Finset.univ.filter fun s : Slot c => slotOwner s = ⟨.input i, hw⟩) = ∅ := by
          ext s; simp [slotOwner]
        rw [hem]; simp [G1cFin, G1wFin, G2Fin]
      · have hbij : (Finset.univ.filter fun s : Slot c => slotOwner s = ⟨.gate g, hw⟩).card =
            σ.Arity (c.program.lines g).op := by
          rw [← Fintype.card_fin (σ.Arity (c.program.lines g).op)]
          refine Finset.card_bij (fun a _ => ⟨⟨g, a⟩, hw⟩)
            (fun a _ => by simp [slotOwner])
            (fun a₁ _ a₂ _ h => by
              have hval : (a₁ : ℕ) = (a₂ : ℕ) :=
                congrArg (fun s : Slot c => (s.1.2 : ℕ)) h
              exact Fin.ext hval)
            (fun s hs => by
              have hsw : slotOwner s = ⟨.gate g, hw⟩ := (Finset.mem_filter.mp hs).2
              have hg_eq : s.1.1 = g := Wire.gate.inj (congrArg Subtype.val hsw)
              rcases s with ⟨⟨g', a⟩, hg'⟩
              dsimp at hg_eq
              subst hg_eq
              exact ⟨a, Finset.mem_univ a, rfl⟩)
            |>.symm
        rw [hbij]
        have har := hU2.arity_le_two (c.program.lines g).op
        rcases (show σ.Arity (c.program.lines g).op = 0 ∨
            σ.Arity (c.program.lines g).op = 1 ∨
            σ.Arity (c.program.lines g).op = 2 by omega) with h0 | h1 | h2
        · simp [G1cFin, G1wFin, G2Fin, h0]
        · by_cases hc : isConst1 g
          · simp only [G1cFin, G1wFin, G2Fin, Finset.mem_filter, Finset.mem_univ, true_and,
              decide_eq_true_eq, h1, hc, not_true_eq_false, and_false, and_true]
            decide
          · simp only [G1cFin, G1wFin, G2Fin, Finset.mem_filter, Finset.mem_univ, true_and,
              decide_eq_true_eq, h1, hc, not_false_eq_true, and_false, and_true]
            decide
        · simp [G1cFin, G1wFin, G2Fin, h2]
    have h1 (S : Finset (Signal c)) : S.card = ∑ w : Signal c, if w ∈ S then 1 else 0 := by
      rw [← Finset.card_filter, Finset.filter_univ_mem]
    simp_rw [hfib]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← h1 G1cFin, ← h1 G1wFin, ← h1 G2Fin]
  -- Bound `G1cFin.card + G1wFin.card + G2Fin.card ≤ c.innerSize`.
  have hinner_le : G1cFin.card + G1wFin.card + G2Fin.card ≤ c.innerSize := by
    have hdisj12 : Disjoint G1cFin G1wFin := Finset.disjoint_left.mpr fun w hw1 hw2 => by
      rcases w with ⟨i | g, hw⟩
      · simp [G1cFin] at hw1
      · simp only [G1cFin, G1wFin, Finset.mem_filter, Finset.mem_univ, true_and,
          decide_eq_true_eq] at hw1 hw2
        exact hw2.2 hw1.2
    have hdisj_2 : Disjoint (G1cFin ∪ G1wFin) G2Fin := Finset.disjoint_left.mpr fun w hw12 hw2 => by
      rcases w with ⟨i | g, hw⟩
      · simp [G2Fin] at hw2
      · simp only [Finset.mem_union, G1cFin, G1wFin, G2Fin, Finset.mem_filter, Finset.mem_univ,
          true_and, decide_eq_true_eq] at hw12 hw2
        rcases hw12 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    rw [← Finset.card_union_of_disjoint hdisj12, ← Finset.card_union_of_disjoint hdisj_2,
      Circuit.innerSize]
    by_cases hcs : 0 < c.size
    · refine Finset.card_le_card_of_injOn
        (fun w => match w.1 with | .input _ => ⟨0, hcs⟩ | .gate g => g)
        (fun w hw => ?_) (fun w₁ hw₁ w₂ hw₂ heq => ?_)
      · rcases w with ⟨i | g, hreach⟩
        · simp [G1cFin, G1wFin, G2Fin] at hw
        · simp only [Finset.mem_coe, Program.mem_innerGates]
          simp only [Finset.mem_coe, Finset.mem_union, G1cFin, G1wFin, G2Fin, Finset.mem_filter,
            Finset.mem_univ, true_and, decide_eq_true_eq] at hw
          rcases hw with (⟨h1, _⟩ | ⟨h1, _⟩) | h2 <;> omega
      · rcases w₁ with ⟨i₁ | g₁, hr₁⟩
        · simp [G1cFin, G1wFin, G2Fin] at hw₁
        · rcases w₂ with ⟨i₂ | g₂, hr₂⟩
          · simp [G1cFin, G1wFin, G2Fin] at hw₂
          · dsimp at heq; subst heq; rfl
    · have hem : G1cFin ∪ G1wFin ∪ G2Fin = ∅ := by
        ext ⟨i | g, hr⟩
        · simp [G1cFin, G1wFin, G2Fin]
        · exact (hcs (Nat.zero_lt_of_lt g.isLt)).elim
      rw [hem]; exact Nat.zero_le _
  -- Relate `d₀` and `(hiddenNetwork c I Acc).read.ncard` to `InpFin, G0Fin, G1cFin`.
  have hd₀_eq : d₀ = InpFin.card + G0Fin.card + G1cFin.card + 1 := by
    have hpart_v (v : Vertex c) :
        (if v ∈ Dfin then 1 else 0) =
          (match v with
          | .signal w => (if w ∈ InpFin then 1 else 0) + (if w ∈ G0Fin then 1 else 0) +
              (if w ∈ G1cFin then 1 else 0)
          | .junction _ => 0
          | .output _ => 1) := by
      cases v with
      | signal w =>
        rcases w with ⟨i | g, hw⟩
        · simp [Dfin, IsDirtySingleton, InpFin, G0Fin, G1cFin]
        · have har := hU2.arity_le_two (c.program.lines g).op
          rcases (show σ.Arity (c.program.lines g).op = 0 ∨
              σ.Arity (c.program.lines g).op = 1 ∨
              σ.Arity (c.program.lines g).op = 2 by omega) with h0 | h1 | h2
          · simp [Dfin, IsDirtySingleton, InpFin, G0Fin, G1cFin, h0]
          · by_cases hc : isConst1 g
            · have hc' : ∃ b : Bool, ∀ x, I (c.program.lines g).op x = b := hc
              simp [Dfin, IsDirtySingleton, InpFin, G0Fin, G1cFin, h1, hc, hc']
            · have hc' : ¬∃ b : Bool, ∀ x, I (c.program.lines g).op x = b := hc
              simp [Dfin, IsDirtySingleton, InpFin, G0Fin, G1cFin, h1, hc, hc']
          · simp [Dfin, IsDirtySingleton, InpFin, G0Fin, G1cFin, h2]
      | junction _ => simp [Dfin, IsDirtySingleton]
      | output _ => simp [Dfin, IsDirtySingleton]
    have hD : d₀ = ∑ v : Vertex c, if v ∈ Dfin then 1 else 0 := by
      dsimp only [d₀]; rw [← Finset.card_filter, Finset.filter_univ_mem]
    rw [hD]
    simp_rw [hpart_v]
    rw [← Vertex.equiv.symm.sum_comp]
    simp only [Fintype.sum_sum_type, Vertex.equiv, Equiv.coe_fn_symm_mk, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have h1 (S : Finset (Signal c)) : (∑ w : Signal c, if w ∈ S then 1 else 0) = S.card := by
      rw [← Finset.card_filter, Finset.filter_univ_mem]
    rw [h1 InpFin, h1 G0Fin, h1 G1cFin]
    omega
  have hread_le : (hiddenNetwork c I Acc).read.ncard ≤ InpFin.card := by
    rw [← Nat.card_coe_set_eq]
    have hinj : Function.Injective
        (fun i : (hiddenNetwork c I Acc).read =>
          (⟨⟨Wire.input (finSumFinEquiv (.inl i.1)), by
            obtain ⟨v, _, hsite⟩ := i.2
            change site c (finSumFinEquiv (.inl i.1)) = some v at hsite
            exact (site_eq_some hsite).1⟩, by simp [InpFin]⟩ :
            {w : Signal c // w ∈ InpFin})) := by
      intro i₁ i₂ h
      have hw := Wire.input.inj (congrArg (fun x => x.1.1) h)
      exact Subtype.ext (Sum.inl.inj (finSumFinEquiv.injective hw))
    have hle := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card (α := {w : Signal c // w ∈ InpFin}), Fintype.card_coe] at hle
  -- Vertex and edge counts of `Compiler.graph c`.
  have hcard_cons : Nat.card (Consumer c) = Nat.card (Slot c) + 1 := by
    rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin 1), Fintype.card_fin]
  have hcard_V : Nat.card (Vertex c) = Nat.card (Signal c) + Nat.card (Consumer c) + 1 := by
    rw [Nat.card_congr Vertex.equiv, Nat.card_sum, Nat.card_sum,
      Nat.card_congr (junctionEquiv c), Nat.card_eq_fintype_card (α := Fin 1), Fintype.card_fin,
      add_assoc]
  have hcard_E : Nat.card (Edge c) = 2 * Nat.card (Consumer c) := card_edge
  have hcmp_le : Nat.card (Vertex c) ≤ st.cmp.blocks.card + E_int.ncard := st.cmp.card_le
  have hcnt : st.dirty.card + Nat.card (Vertex c) ≤ d₀ + st.cmp.blocks.card + E_int.ncard :=
    st.count
  refine ⟨hclean3, ?_, ?_⟩ <;> omega

end CleanCompression

end Cslib.Circuits.Frontier.Compiler

/-! ### `3`-state pair-compressed branching programs -/

namespace Cslib.Circuits.Frontier.Compiler

open Set Matrix Cslib.Circuits.Frontier.Basis

section U2BranchingProgram

variable {σ : Signature} {m_in m_out : ℕ}

/-- Clean matched-pair layout data on a budget-`3` saturated compression of `Compiler.graph c`. -/
structure U2PairData (c : Circuit σ m_in m_out) (I : Interpretation σ Bool) where
  /-- Underlying budget-`3` edge-contraction compression of `Compiler.graph c`. -/
  Q : (graph c).Compression 3
  /-- Proof that `Q` cannot contract any remaining low-degree block. -/
  hsat : Q.Saturated
  /-- Clean edge matching in the quotient multigraph `Q.quotient`. -/
  M : Set Q.external
  /-- Cubic regularity of `Q.quotient` whenever `M` is nonempty. -/
  h3 : M.Nonempty → ∀ B : Q.blocks, (Q.quotient.incidenceSet B).ncard = 3
  /-- Vertex disjointness of the matched edges `M`. -/
  hM : Q.quotient.IsMatching M
  /-- Cleanliness (`COPY` or `U₂` gate) of both endpoint blocks of every edge in `M`. -/
  hclean : ∀ e ∈ M, CleanBlock3 I {v | v ∈ (Q.quotient.src e).1} ∧
    CleanBlock3 I {v | v ∈ (Q.quotient.tgt e).1}
  /-- Real score function on external quotient wires orienting each clean pair's outer wires. -/
  score : Q.external → ℝ
  /-- Linear layout of singletons and equal-key clean pairs of `Q.quotient`. -/
  pairLay : Layout (Q.quotient.PairNode M M score)

namespace U2PairData

variable {c : Circuit σ m_in m_out} {I : Interpretation σ Bool} (D : U2PairData c I)

/-- Equal-key clean matched pairs of `D`. -/
noncomputable def eqPairs : Set D.Q.external :=
  D.Q.quotient.equalKeyPairs D.M D.M D.score

private theorem isMatching_eqPairs : D.Q.quotient.IsMatching D.eqPairs :=
  fun _ h₁ _ h₂ hne => D.hM h₁.1 h₂.1 hne

private def pairVerts (e : D.eqPairs) : Set (Vertex c) :=
  {v | v ∈ (D.Q.quotient.src e.1).1} ∪ {v | v ∈ (D.Q.quotient.tgt e.1).1}

private theorem mem_pairVerts_iff (e : D.eqPairs) (v : Vertex c) :
    v ∈ D.pairVerts e ↔
      D.Q.blockOf v = D.Q.quotient.src e.1 ∨ D.Q.blockOf v = D.Q.quotient.tgt e.1 := by
  simp only [pairVerts, mem_union, mem_ofPred_eq, D.Q.mem_iff_blockOf_eq]

private theorem isCleanVertex_of_mem_pairVerts (e : D.eqPairs) {v : Vertex c}
    (hv : v ∈ D.pairVerts e) : IsCleanVertex v := by
  rcases hv with hv₁ | hv₂
  · exact (D.hclean e.1 e.2.1).1.1 v hv₁
  · exact (D.hclean e.1 e.2.1).2.1 v hv₂

private theorem disjoint_pairVerts {e₁ e₂ : D.eqPairs} (hne : e₁ ≠ e₂) :
    Disjoint (D.pairVerts e₁) (D.pairVerts e₂) := by
  refine disjoint_left.mpr fun v hv₁ hv₂ => ?_
  have hne_val : e₁.1 ≠ e₂.1 := fun h => hne (Subtype.ext h)
  exact disjoint_left.mp (D.isMatching_eqPairs e₁.2 e₂.2 hne_val)
    ((D.mem_pairVerts_iff e₁ v).mp hv₁) ((D.mem_pairVerts_iff e₂ v).mp hv₂)

private noncomputable def pinA (e : D.eqPairs) : D.Q.external :=
  D.Q.quotient.outerLow D.score (D.Q.quotient.src e.1) e.1

private noncomputable def pinB (e : D.eqPairs) : D.Q.external :=
  D.Q.quotient.outerHigh D.score (D.Q.quotient.src e.1) e.1

private noncomputable def pinC (e : D.eqPairs) : D.Q.external :=
  D.Q.quotient.outerLow D.score (D.Q.quotient.tgt e.1) e.1

private noncomputable def pinD (e : D.eqPairs) : D.Q.external :=
  D.Q.quotient.outerHigh D.score (D.Q.quotient.tgt e.1) e.1

private theorem block_edgeCut_sdiff (hM_ne : D.M.Nonempty) (B : D.Q.blocks) (f : D.Q.external)
    (hf : f ∈ D.Q.quotient.incidenceSet B) :
    (D.Q.quotient.outerLow D.score B f).1 ≠ (D.Q.quotient.outerHigh D.score B f).1 ∧
      (graph c).edgeCut {v | v ∈ B.1} \ {f.1} =
        {(D.Q.quotient.outerLow D.score B f).1, (D.Q.quotient.outerHigh D.score B f).1} := by
  have := Fintype.ofFinite (Edge c)
  have hspec := Multigraph.outerLow_outerHigh_spec (D.h3 hM_ne) D.score hf
  refine ⟨fun h => hspec.1 (Subtype.ext h), ?_⟩
  have hpre : D.Q.blockOf ⁻¹' ({B} : Set D.Q.blocks) = {v | v ∈ B.1} := by
    ext v; simp [D.Q.mem_iff_blockOf_eq]
  have hcut : (graph c).edgeCut {v | v ∈ B.1} =
      Subtype.val '' D.Q.quotient.incidenceSet B := by
    rw [← hpre, ← Multigraph.edgeCut_singleton _ D.Q.quotient_loopless]
    ext g
    simp only [Multigraph.mem_edgeCut, mem_preimage, mem_singleton_iff, mem_image,
      Subtype.exists, exists_and_right, exists_eq_right, Multigraph.Compression.quotient_src,
      Multigraph.Compression.quotient_tgt]
    exact ⟨fun h => ⟨fun heq => h (by rw [heq]), h⟩, fun ⟨_, h⟩ => h⟩
  rw [hcut]
  ext g
  simp only [mem_sdiff, mem_image, mem_singleton_iff, mem_insert_iff]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hne⟩
    have hx' : x ∈ D.Q.quotient.incidenceSet B \ {f} := ⟨hx, fun h => hne (congrArg Subtype.val h)⟩
    rw [hspec.2.1] at hx'
    rcases hx' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · have hm : D.Q.quotient.outerLow D.score B f ∈ D.Q.quotient.incidenceSet B \ {f} := by
        rw [hspec.2.1]; simp
      exact ⟨⟨_, hm.1, rfl⟩, fun h => hm.2 (Subtype.ext h)⟩
    · have hm : D.Q.quotient.outerHigh D.score B f ∈ D.Q.quotient.incidenceSet B \ {f} := by
        rw [hspec.2.1]; simp
      exact ⟨⟨_, hm.1, rfl⟩, fun h => hm.2 (Subtype.ext h)⟩

private theorem edgeCut_src_inter_tgt (e : D.eqPairs) :
    (graph c).edgeCut {v | v ∈ (D.Q.quotient.src e.1).1} ∩
      (graph c).edgeCut {v | v ∈ (D.Q.quotient.tgt e.1).1} = {e.1.1} := by
  have := Fintype.ofFinite (Edge c)
  have hinj := D.hsat.injective_ends_quotient
  set B₁ := D.Q.quotient.src e.1
  set B₂ := D.Q.quotient.tgt e.1
  have hneB : B₁ ≠ B₂ := D.Q.quotient_loopless e.1
  ext g
  simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hg₁, hg₂⟩
    rw [D.Q.mem_edgeCut_block] at hg₁ hg₂
    have hext : g ∈ D.Q.external := fun heq => hg₁ (by rw [heq])
    let gx : D.Q.external := ⟨g, hext⟩
    suffices gx = e.1 from congrArg Subtype.val this
    apply hinj
    simp only [Multigraph.ends, Multigraph.Compression.quotient_src,
      Multigraph.Compression.quotient_tgt, Sym2.eq_iff]
    change (D.Q.blockOf (src g) = B₁ ∧ D.Q.blockOf (tgt g) = B₂) ∨
      (D.Q.blockOf (src g) = B₂ ∧ D.Q.blockOf (tgt g) = B₁)
    by_cases hs₁ : D.Q.blockOf (src g) = B₁
    · have ht_ne₁ : D.Q.blockOf (tgt g) ≠ B₁ := fun h => hg₁ (iff_of_true hs₁ h)
      by_cases hs₂ : D.Q.blockOf (src g) = B₂
      · exact (hneB (hs₁.symm.trans hs₂)).elim
      · have ht₂ : D.Q.blockOf (tgt g) = B₂ := by_contra fun hn => hg₂ (iff_of_false hs₂ hn)
        exact Or.inl ⟨hs₁, ht₂⟩
    · have ht₁ : D.Q.blockOf (tgt g) = B₁ := by_contra fun hn => hg₁ (iff_of_false hs₁ hn)
      have ht_ne₂ : D.Q.blockOf (tgt g) ≠ B₂ := fun h => hneB (ht₁.symm.trans h)
      have hs₂ : D.Q.blockOf (src g) = B₂ := by_contra fun hn => hg₂ (iff_of_false hn ht_ne₂)
      exact Or.inr ⟨hs₂, ht₁⟩
  · rintro rfl
    rw [D.Q.mem_edgeCut_block, D.Q.mem_edgeCut_block]
    exact ⟨fun h => hneB (h.mp rfl).symm, fun h => hneB (h.mpr rfl)⟩

private theorem edgeCut_pairVerts (e : D.eqPairs) :
    (graph c).edgeCut (D.pairVerts e) =
      {(D.pinA e).1, (D.pinB e).1, (D.pinC e).1, (D.pinD e).1} := by
  have hd : Disjoint {v | v ∈ (D.Q.quotient.src e.1).1} {v | v ∈ (D.Q.quotient.tgt e.1).1} :=
    D.Q.disjoint_of_ne (D.Q.quotient_loopless e.1)
  obtain ⟨hc_u, _⟩ := edgeCut_union_of_inter_singleton hd (D.edgeCut_src_inter_tgt e)
  have hs₁ := (D.block_edgeCut_sdiff ⟨e.1, e.2.1⟩ (D.Q.quotient.src e.1) e.1 (Or.inl rfl)).2
  have hs₂ := (D.block_edgeCut_sdiff ⟨e.1, e.2.1⟩ (D.Q.quotient.tgt e.1) e.1 (Or.inr rfl)).2
  dsimp only [pairVerts, pinA, pinB, pinC, pinD]
  rw [hc_u, hs₁, hs₂]
  ext g
  simp only [mem_union, mem_insert_iff, mem_singleton_iff]
  tauto

private theorem exists_rect_cover (e : D.eqPairs) :
    ∃ (row col : Fin 3 → Bool × Bool → Bool),
      (∀ α, GateSatisfies I (D.pairVerts e) α →
        ∃! r : Fin 3, (row r (α (D.pinB e).1, α (D.pinD e).1) &&
          col r (α (D.pinA e).1, α (D.pinC e).1)) = true) ∧
      (∀ (r : Fin 3) (α : Edge c → Bool),
        (row r (α (D.pinB e).1, α (D.pinD e).1) &&
          col r (α (D.pinA e).1, α (D.pinC e).1)) = true →
        ∃ β, EqOn β α (internalEdges c (D.pairVerts e))ᶜ ∧ GateSatisfies I (D.pairVerts e) β) := by
  set B₁ := D.Q.quotient.src e.1
  set B₂ := D.Q.quotient.tgt e.1
  have hd : Disjoint {v | v ∈ B₁.1} {v | v ∈ B₂.1} :=
    D.Q.disjoint_of_ne (D.Q.quotient_loopless e.1)
  have hint := D.edgeCut_src_inter_tgt e
  have he_cut₁ : e.1.1 ∈ (graph c).edgeCut {v | v ∈ B₁.1} := (hint.symm ▸ mem_singleton _).1
  have he_cut₂ : e.1.1 ∈ (graph c).edgeCut {v | v ∈ B₂.1} := (hint.symm ▸ mem_singleton _).2
  obtain ⟨hne₁, hs₁⟩ := D.block_edgeCut_sdiff ⟨e.1, e.2.1⟩ B₁ e.1 (Or.inl rfl)
  obtain ⟨hne₂, hs₂⟩ := D.block_edgeCut_sdiff ⟨e.1, e.2.1⟩ B₂ e.1 (Or.inr rfl)
  obtain ⟨hb₁, hb₂⟩ := D.hclean e.1 e.2.1
  obtain ⟨rel₁, hU₁, hsd₁, hrl₁⟩ :=
    (hb₁.2.2 _ _ e.1.1 hne₁ hs₁ he_cut₁).1 (D.Q.mem_blockOf (src e.1.1))
  obtain ⟨rel₂, hI₂, hsd₂, hrl₂⟩ :=
    (hb₂.2.2 _ _ e.1.1 hne₂ hs₂ he_cut₂).2 (D.Q.mem_blockOf (tgt e.1.1))
  obtain ⟨row, col, hcov⟩ := hasUnambiguousRectangles_u2 hU₁ hI₂
  refine ⟨row, col, fun α hsat => ?_, fun r α hr => ?_⟩
  · have h1 := hsd₁ α fun v hv => hsat v (Or.inl hv)
    have h2 := hsd₂ α fun v hv => hsat v (Or.inr hv)
    have hpm : pairMatrix rel₁ rel₂ (α (D.pinB e).1, α (D.pinD e).1)
        (α (D.pinA e).1, α (D.pinC e).1) = true := by
      dsimp only [pinA, pinB, pinC, pinD, B₁, B₂] at h1 h2 ⊢
      rcases Bool.dichotomy (α e.1.1) with hα | hα <;> rw [hα] at h1 h2
      · simp only [pairMatrix, h1, h2, Bool.and_self, Bool.true_or]
      · simp only [pairMatrix, h1, h2, Bool.and_self, Bool.or_true]
    have hcard := hcov (α (D.pinB e).1, α (D.pinD e).1) (α (D.pinA e).1, α (D.pinC e).1)
    simp only [hpm, ↓reduceIte] at hcard
    obtain ⟨r₀, hr₀⟩ := Finset.card_eq_one.mp hcard
    refine ⟨r₀, ?_, fun r' hr' => ?_⟩
    · have hm : r₀ ∈ Finset.univ.filter _ := hr₀ ▸ Finset.mem_singleton_self r₀
      exact (Finset.mem_filter.mp hm).2
    · have hm : r' ∈ ({r₀} : Finset (Fin 3)) := hr₀ ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr'⟩
      exact Finset.mem_singleton.mp hm
  · classical
    have hcard := hcov (α (D.pinB e).1, α (D.pinD e).1) (α (D.pinA e).1, α (D.pinC e).1)
    have hpos : 0 < (Finset.univ.filter fun r' : Fin 3 =>
        row r' (α (D.pinB e).1, α (D.pinD e).1) &&
          col r' (α (D.pinA e).1, α (D.pinC e).1)).card :=
      Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
    have hpm : pairMatrix rel₁ rel₂ (α (D.pinB e).1, α (D.pinD e).1)
        (α (D.pinA e).1, α (D.pinC e).1) = true := by
      by_contra hfalse
      simp only [Bool.not_eq_true] at hfalse
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte] at hcard
      omega
    simp only [pairMatrix, Bool.or_eq_true, Bool.and_eq_true] at hpm
    have hex_val : ∃ val_e : Bool, rel₁ (α (D.pinA e).1) (α (D.pinB e).1) val_e = true ∧
        rel₂ (α (D.pinC e).1) (α (D.pinD e).1) val_e = true :=
      hpm.elim (fun h => ⟨false, h⟩) (fun h => ⟨true, h⟩)
    obtain ⟨val_e, hv₁, hv₂⟩ := hex_val
    let α₀ : Edge c → Bool := fun g => if g = e.1.1 then val_e else α g
    have ha_mem : (D.pinA e).1 ∈ (graph c).edgeCut {v | v ∈ B₁.1} \ {e.1.1} := by
      rw [hs₁]; exact Or.inl rfl
    have hb_mem : (D.pinB e).1 ∈ (graph c).edgeCut {v | v ∈ B₁.1} \ {e.1.1} := by
      rw [hs₁]; exact Or.inr rfl
    have hc_mem : (D.pinC e).1 ∈ (graph c).edgeCut {v | v ∈ B₂.1} \ {e.1.1} := by
      rw [hs₂]; exact Or.inl rfl
    have hd_mem : (D.pinD e).1 ∈ (graph c).edgeCut {v | v ∈ B₂.1} \ {e.1.1} := by
      rw [hs₂]; exact Or.inr rfl
    refine patch_union hd hint α α₀ (fun g hne => ite_eq_right hne) ?_ ?_
    · refine hrl₁ α₀ ?_
      have hA : α₀ (D.pinA e).1 = α (D.pinA e).1 := ite_eq_right ha_mem.2
      have hB : α₀ (D.pinB e).1 = α (D.pinB e).1 := ite_eq_right hb_mem.2
      have hE : α₀ e.1.1 = val_e := ite_eq_left rfl
      dsimp only [pinA, pinB] at hA hB hv₁
      rwa [hA, hB, hE]
    · intro β₁ hβ₁
      refine hrl₂ β₁ ?_
      have hC : β₁ (D.pinC e).1 = α (D.pinC e).1 := (hβ₁ hc_mem.1).trans (ite_eq_right hc_mem.2)
      have hD : β₁ (D.pinD e).1 = α (D.pinD e).1 := (hβ₁ hd_mem.1).trans (ite_eq_right hd_mem.2)
      have hE : β₁ e.1.1 = val_e := (hβ₁ he_cut₂).trans (ite_eq_left rfl)
      dsimp only [pinC, pinD] at hC hD hv₂
      rwa [hC, hD, hE]

private noncomputable def rowPred (e : D.eqPairs) : Fin 3 → Bool × Bool → Bool :=
  (D.exists_rect_cover e).choose

private noncomputable def colPred (e : D.eqPairs) : Fin 3 → Bool × Bool → Bool :=
  (D.exists_rect_cover e).choose_spec.choose

private noncomputable def rectIdxAux (e : D.eqPairs) (b d a c_val : Bool) : Fin 3 :=
  letI := Classical.dec
  if h : ∃ r : Fin 3, (D.rowPred e r (b, d) && D.colPred e r (a, c_val)) = true then
    h.choose
  else 0

private noncomputable def rectIdx (e : D.eqPairs) (α : Edge c → Bool) : Fin 3 :=
  D.rectIdxAux e (α (D.pinB e).1) (α (D.pinD e).1) (α (D.pinA e).1) (α (D.pinC e).1)

private theorem rectIdx_congr (e : D.eqPairs) {α β : Edge c → Bool}
    (hA : α (D.pinA e).1 = β (D.pinA e).1) (hB : α (D.pinB e).1 = β (D.pinB e).1)
    (hC : α (D.pinC e).1 = β (D.pinC e).1) (hD : α (D.pinD e).1 = β (D.pinD e).1) :
    D.rectIdx e α = D.rectIdx e β := by
  unfold rectIdx
  rw [hB, hD, hA, hC]

private theorem rectIdx_spec_of_sat (e : D.eqPairs) {α : Edge c → Bool}
    (hsat : GateSatisfies I (D.pairVerts e) α) :
    D.rowPred e (D.rectIdx e α) (α (D.pinB e).1, α (D.pinD e).1) = true ∧
      D.colPred e (D.rectIdx e α) (α (D.pinA e).1, α (D.pinC e).1) = true := by
  obtain ⟨r, hr, _⟩ := (D.exists_rect_cover e).choose_spec.choose_spec.1 α hsat
  have hex : ∃ r' : Fin 3, (D.rowPred e r' (α (D.pinB e).1, α (D.pinD e).1) &&
      D.colPred e r' (α (D.pinA e).1, α (D.pinC e).1)) = true := ⟨r, hr⟩
  dsimp only [rectIdx, rectIdxAux]
  rw [dite_eq_left hex]
  exact Bool.and_eq_true_iff.mp hex.choose_spec

private theorem rectIdx_eq_and_realize (e : D.eqPairs) {r : Fin 3} {α : Edge c → Bool}
    (hrc : D.rowPred e r (α (D.pinB e).1, α (D.pinD e).1) = true ∧
      D.colPred e r (α (D.pinA e).1, α (D.pinC e).1) = true) :
    D.rectIdx e α = r ∧
      ∃ β, EqOn β α (internalEdges c (D.pairVerts e))ᶜ ∧ GateSatisfies I (D.pairVerts e) β := by
  have hand : (D.rowPred e r (α (D.pinB e).1, α (D.pinD e).1) &&
      D.colPred e r (α (D.pinA e).1, α (D.pinC e).1)) = true :=
    Bool.and_eq_true_iff.mpr hrc
  obtain ⟨β, hβ_eq, hβ_sat⟩ := (D.exists_rect_cover e).choose_spec.choose_spec.2 r α hand
  refine ⟨?_, β, hβ_eq, hβ_sat⟩
  -- `β` agrees with `α` on all four external pins of `pairVerts e`.
  have hnot_int {g : Edge c} (hg : g ∈ (graph c).edgeCut (D.pairVerts e)) :
      g ∉ internalEdges c (D.pairVerts e) := fun hin => hg (iff_of_true hin.1 hin.2)
  have hA : β (D.pinA e).1 = α (D.pinA e).1 :=
    hβ_eq (hnot_int (by rw [D.edgeCut_pairVerts]; simp))
  have hB : β (D.pinB e).1 = α (D.pinB e).1 :=
    hβ_eq (hnot_int (by rw [D.edgeCut_pairVerts]; simp))
  have hC : β (D.pinC e).1 = α (D.pinC e).1 :=
    hβ_eq (hnot_int (by rw [D.edgeCut_pairVerts]; simp))
  have hD : β (D.pinD e).1 = α (D.pinD e).1 :=
    hβ_eq (hnot_int (by rw [D.edgeCut_pairVerts]; simp))
  obtain ⟨r₀, _, huniq⟩ := (D.exists_rect_cover e).choose_spec.choose_spec.1 β hβ_sat
  have hex : ∃ r' : Fin 3, (D.rowPred e r' (α (D.pinB e).1, α (D.pinD e).1) &&
      D.colPred e r' (α (D.pinA e).1, α (D.pinC e).1)) = true := ⟨r, hand⟩
  dsimp only [rectIdx, rectIdxAux]
  rw [dite_eq_left hex]
  have h1 : hex.choose = r₀ := huniq hex.choose (by rw [hB, hD, hA, hC]; exact hex.choose_spec)
  have h2 : r = r₀ := huniq r (by rw [hB, hD, hA, hC]; exact hand)
  exact h1.trans h2.symm

/-- Individual vertices outside equal-key clean pairs, plus one super-node per `e : D.eqPairs`. -/
private abbrev SingleVert :=
  {v : Vertex c // D.Q.blockOf v ∉ D.Q.quotient.matchedVertices D.eqPairs}

private abbrev StepNode := D.SingleVert ⊕ D.eqPairs

private instance : Finite D.StepNode := by
  have := Finite.of_injective (fun u : D.SingleVert => u.1) Subtype.val_injective
  have := Fintype.ofFinite (Edge c)
  infer_instance

private theorem card_stepNode_le : Nat.card D.StepNode ≤ Nat.card (Vertex c) := by
  let rep : D.StepNode → Vertex c
    | .inl u => u.1
    | .inr e => (D.Q.quotient.src e.1).1.head (D.Q.ne_nil _ (D.Q.quotient.src e.1).2)
  refine Nat.card_le_card_of_injective rep ?_
  rintro (u₁ | e₁) (u₂ | e₂) h <;> dsimp only [rep] at h
  · exact congrArg Sum.inl (Subtype.ext h)
  · have hm : rep (.inr e₂) ∈ (D.Q.quotient.src e₂.1).1 := List.head_mem _
    dsimp only [rep] at hm
    rw [← h] at hm
    exact (u₁.2 ⟨e₂.1, e₂.2, Or.inl (D.Q.mem_iff_blockOf_eq.mp hm).symm⟩).elim
  · have hm : rep (.inr e₁) ∈ (D.Q.quotient.src e₁.1).1 := List.head_mem _
    dsimp only [rep] at hm
    rw [h] at hm
    exact (u₂.2 ⟨e₁.1, e₁.2, Or.inl (D.Q.mem_iff_blockOf_eq.mp hm).symm⟩).elim
  · have hm₁ : rep (.inr e₁) ∈ D.pairVerts e₁ := Or.inl (List.head_mem _)
    have hm₂ : rep (.inr e₂) ∈ D.pairVerts e₂ := Or.inl (List.head_mem _)
    dsimp only [rep] at hm₁ hm₂
    rw [h] at hm₁
    by_contra hne
    exact disjoint_left.mp (D.disjoint_pairVerts fun heq => hne (congrArg Sum.inr heq)) hm₁ hm₂

private noncomputable def stepPairNode : D.StepNode → D.Q.quotient.PairNode D.M D.M D.score
  | .inl u => .inl ⟨D.Q.blockOf u.1, u.2⟩
  | .inr e => .inr e

open Classical in
private noncomputable def stepSubIdx : D.StepNode → ℕ
  | .inl u => (D.Q.blockOf u.1).1.idxOf u.1
  | .inr _ => 0

private noncomputable def stepKey (x : D.StepNode) : ℕ ×ₗ ℕ :=
  toLex ((D.pairLay (D.stepPairNode x) : ℕ), D.stepSubIdx x)

private theorem stepKey_injective : Function.Injective D.stepKey := by
  classical
  rintro (u₁ | e₁) (u₂ | e₂) h
  · obtain ⟨hp, hi⟩ := Prod.mk.inj (toLex.injective h)
    have hb : D.Q.blockOf u₁.1 = D.Q.blockOf u₂.1 :=
      Subtype.mk.inj (Sum.inl.inj (D.pairLay.injective (Fin.ext hp)))
    dsimp only [stepSubIdx] at hi
    rw [hb] at hi
    exact congrArg Sum.inl
      (Subtype.ext ((List.idxOf_inj (D.Q.mem_iff_blockOf_eq.mpr hb)).mp hi))
  · exact absurd (D.pairLay.injective (Fin.ext (Prod.mk.inj (toLex.injective h)).1))
      (by simp [stepPairNode])
  · exact absurd (D.pairLay.injective (Fin.ext (Prod.mk.inj (toLex.injective h)).1))
      (by simp [stepPairNode])
  · exact congrArg Sum.inr
      (Sum.inr.inj (D.pairLay.injective (Fin.ext (Prod.mk.inj (toLex.injective h)).1)))

private noncomputable def stepLayout : Layout D.StepNode :=
  (Layout.exists_lt_iff D.stepKey_injective).choose

private theorem stepLayout_lt_iff (x y : D.StepNode) :
    D.stepLayout x < D.stepLayout y ↔ D.stepKey x < D.stepKey y :=
  (Layout.exists_lt_iff D.stepKey_injective).choose_spec x y

private def nodeVerts : D.StepNode → Set (Vertex c)
  | .inl u => {u.1}
  | .inr e => D.pairVerts e

private theorem pairwiseDisjoint_nodeVerts :
    (univ : Set D.StepNode).PairwiseDisjoint D.nodeVerts := by
  rintro (u₁ | e₁) - (u₂ | e₂) - hne
  · refine disjoint_singleton.mpr fun h => hne (congrArg Sum.inl (Subtype.ext h))
  · refine disjoint_singleton_left.mpr fun hm => u₁.2 ?_
    exact ⟨e₂.1, e₂.2, (D.mem_pairVerts_iff e₂ u₁.1).mp hm |>.imp Eq.symm Eq.symm⟩
  · refine disjoint_singleton_right.mpr fun hm => u₂.2 ?_
    exact ⟨e₁.1, e₁.2, (D.mem_pairVerts_iff e₁ u₂.1).mp hm |>.imp Eq.symm Eq.symm⟩
  · exact D.disjoint_pairVerts fun h => hne (congrArg Sum.inr h)

private theorem exists_mem_nodeVerts (v : Vertex c) : ∃ x : D.StepNode, v ∈ D.nodeVerts x := by
  by_cases hv : D.Q.blockOf v ∈ D.Q.quotient.matchedVertices D.eqPairs
  · obtain ⟨e, he, hev⟩ := hv
    exact ⟨.inr ⟨e, he⟩, (D.mem_pairVerts_iff ⟨e, he⟩ v).mpr (hev.imp Eq.symm Eq.symm)⟩
  · exact ⟨.inl ⟨v, hv⟩, rfl⟩

private noncomputable def pastVerts (t : ℕ) : Set (Vertex c) :=
  ⋃ x ∈ D.stepLayout.initial t, D.nodeVerts x

private theorem pastVerts_zero : D.pastVerts 0 = ∅ := by
  simp [pastVerts]

private theorem pastVerts_of_card_le {t : ℕ} (ht : Nat.card D.StepNode ≤ t) :
    D.pastVerts t = univ := by
  ext v
  simp only [pastVerts, D.stepLayout.initial_of_card_le ht, mem_iUnion, mem_univ, exists_prop,
    true_and, iff_true]
  exact D.exists_mem_nodeVerts v

private theorem pastVerts_mono : Monotone D.pastVerts :=
  fun _ _ hst => biUnion_mono (fun _ hx => lt_of_lt_of_le hx hst) fun _ _ => subset_rfl

private theorem pastVerts_succ_sdiff {t : ℕ} (ht : t < Nat.card D.StepNode) :
    D.pastVerts (t + 1) \ D.pastVerts t = D.nodeVerts (D.stepLayout.symm ⟨t, ht⟩) ∧
      D.pastVerts (t + 1) = D.nodeVerts (D.stepLayout.symm ⟨t, ht⟩) ∪ D.pastVerts t ∧
      Disjoint (D.nodeVerts (D.stepLayout.symm ⟨t, ht⟩)) (D.pastVerts t) := by
  set x := D.stepLayout.symm ⟨t, ht⟩
  have hx_not : x ∉ D.stepLayout.initial t := by simp [x, Layout.mem_initial]
  have hun : D.pastVerts (t + 1) = D.nodeVerts x ∪ D.pastVerts t := by
    simp only [pastVerts, D.stepLayout.initial_succ ht, biUnion_insert]
    rfl
  have hdisj : Disjoint (D.nodeVerts x) (D.pastVerts t) := by
    refine disjoint_iUnion₂_right.mpr fun y hy => ?_
    exact D.pairwiseDisjoint_nodeVerts trivial trivial fun (heq : x = y) => hx_not (by rwa [heq])
  refine ⟨?_, hun, hdisj⟩
  rw [hun]
  ext v
  simp only [mem_sdiff, mem_union]
  have hd : v ∈ D.nodeVerts x → v ∉ D.pastVerts t := fun hv => disjoint_left.mp hdisj hv
  tauto

private theorem pairVerts_subset_pastVerts_iff (e : D.eqPairs) (t : ℕ) :
    D.pairVerts e ⊆ D.pastVerts t ↔ .inr e ∈ D.stepLayout.initial t := by
  refine ⟨fun hsub => ?_, fun hm v hv => mem_biUnion hm hv⟩
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ (D.Q.ne_nil _ (D.Q.quotient.src e.1).2)
  have hv_pair : v ∈ D.pairVerts e := Or.inl hv
  obtain ⟨y, hy_in, hvy⟩ := mem_iUnion₂.mp (hsub hv_pair)
  have hy_eq : y = .inr e := by
    by_contra hne
    exact disjoint_left.mp (D.pairwiseDisjoint_nodeVerts trivial trivial hne) hvy hv_pair
  rwa [← hy_eq]

private noncomputable def actPairs (t : ℕ) : Set D.eqPairs :=
  {e | .inr e ∈ D.stepLayout.initial t ∧
    (D.pinB e).1 ∈ (graph c).edgeCut (D.pastVerts t) ∧
    (D.pinD e).1 ∈ (graph c).edgeCut (D.pastVerts t)}

private noncomputable def singleCut (t : ℕ) : Set (Edge c) :=
  (graph c).edgeCut (D.pastVerts t) \ ⋃ e ∈ D.actPairs t, {(D.pinB e).1, (D.pinD e).1}

private theorem pinB_ne_pinD (e : D.eqPairs) : (D.pinB e).1 ≠ (D.pinD e).1 := by
  have := Fintype.ofFinite (Edge c)
  intro h
  exact Multigraph.outerHigh_src_ne_tgt D.Q.quotient_loopless
    D.hsat.injective_ends_quotient (D.h3 ⟨e.1, e.2.1⟩) D.score e.1 (Subtype.ext h)

private theorem pin_end_in_pairVerts (e : D.eqPairs) (g : Edge c)
    (hg : g ∈ ({(D.pinA e).1, (D.pinB e).1, (D.pinC e).1, (D.pinD e).1} : Set (Edge c))) :
    src g ∈ D.pairVerts e ∨ tgt g ∈ D.pairVerts e := by
  have hcut : g ∈ (graph c).edgeCut (D.pairVerts e) := D.edgeCut_pairVerts e ▸ hg
  by_contra hnone
  rw [not_or] at hnone
  exact hcut (iff_of_false hnone.1 hnone.2)

private theorem pinA_end (e : D.eqPairs) :
    src (D.pinA e).1 ∈ D.pairVerts e ∨ tgt (D.pinA e).1 ∈ D.pairVerts e :=
  D.pin_end_in_pairVerts e (D.pinA e).1 (by simp)

private theorem pinB_end (e : D.eqPairs) :
    src (D.pinB e).1 ∈ D.pairVerts e ∨ tgt (D.pinB e).1 ∈ D.pairVerts e :=
  D.pin_end_in_pairVerts e (D.pinB e).1 (by simp)

private theorem pinC_end (e : D.eqPairs) :
    src (D.pinC e).1 ∈ D.pairVerts e ∨ tgt (D.pinC e).1 ∈ D.pairVerts e :=
  D.pin_end_in_pairVerts e (D.pinC e).1 (by simp)

private theorem pinD_end (e : D.eqPairs) :
    src (D.pinD e).1 ∈ D.pairVerts e ∨ tgt (D.pinD e).1 ∈ D.pairVerts e :=
  D.pin_end_in_pairVerts e (D.pinD e).1 (by simp)

private theorem pinBD_end (e : D.eqPairs) {g : Edge c}
    (hg : g ∈ ({(D.pinB e).1, (D.pinD e).1} : Set (Edge c))) :
    src g ∈ D.pairVerts e ∨ tgt g ∈ D.pairVerts e := by
  rcases hg with rfl | rfl
  · exact D.pinB_end e
  · exact D.pinD_end e

private theorem pairwiseDisjoint_actPairs (t : ℕ) :
    (D.actPairs t).PairwiseDisjoint fun e => ({(D.pinB e).1, (D.pinD e).1} : Set (Edge c)) := by
  intro e₁ he₁ e₂ he₂ hne
  refine disjoint_left.mpr fun g hg₁ hg₂ => ?_
  have hg_cut : g ∈ (graph c).edgeCut (D.pastVerts t) := by
    rcases hg₁ with rfl | rfl
    · exact he₁.2.1
    · exact he₁.2.2
  have hsub₁ := (D.pairVerts_subset_pastVerts_iff e₁ t).mpr he₁.1
  have hsub₂ := (D.pairVerts_subset_pastVerts_iff e₂ t).mpr he₂.1
  have hend₁ := D.pinBD_end e₁ hg₁
  have hend₂ := D.pinBD_end e₂ hg₂
  have hboth : src g ∈ D.pastVerts t ∧ tgt g ∈ D.pastVerts t := by
    rcases hend₁ with hs₁ | ht₁ <;> rcases hend₂ with hs₂ | ht₂
    · exact (disjoint_left.mp (D.disjoint_pairVerts hne) hs₁ hs₂).elim
    · exact ⟨hsub₁ hs₁, hsub₂ ht₂⟩
    · exact ⟨hsub₂ hs₂, hsub₁ ht₁⟩
    · exact (disjoint_left.mp (D.disjoint_pairVerts hne) ht₁ ht₂).elim
  exact hg_cut (iff_of_true hboth.1 hboth.2)

private theorem ncard_singleCut_add_actPairs (t : ℕ) :
    (D.singleCut t).ncard + 2 * (D.actPairs t).ncard =
      ((graph c).edgeCut (D.pastVerts t)).ncard := by
  classical
  have := Fintype.ofFinite (Edge c)
  set U := ⋃ e ∈ D.actPairs t, ({(D.pinB e).1, (D.pinD e).1} : Set (Edge c))
  have hU_sub : U ⊆ (graph c).edgeCut (D.pastVerts t) := by
    rintro g ⟨_, ⟨e, rfl⟩, _, ⟨he, rfl⟩, rfl | rfl⟩
    · exact he.2.1
    · exact he.2.2
  have hU_card : U.ncard = 2 * (D.actPairs t).ncard := by
    have := Fintype.ofFinite D.eqPairs
    let Afin : Finset D.eqPairs := (D.actPairs t).toFinset
    have hU_eq : U = ((Afin.biUnion fun e => {(D.pinB e).1, (D.pinD e).1}) : Set (Edge c)) := by
      ext g
      simp only [U, Afin, Finset.coe_biUnion, Finset.mem_coe, mem_toFinset, mem_iUnion,
        Finset.coe_insert, Finset.coe_singleton]
    rw [hU_eq, ncard_coe_finset, Finset.card_biUnion]
    · have h2 (e : D.eqPairs) : ({(D.pinB e).1, (D.pinD e).1} : Finset (Edge c)).card = 2 :=
        Finset.card_pair (D.pinB_ne_pinD e)
      simp only [h2, Finset.sum_const, smul_eq_mul, mul_comm _ 2, Afin, ncard_eq_toFinset_card']
    · intro e₁ he₁ e₂ he₂ hne
      dsimp only [Function.onFun]
      rw [← Finset.disjoint_coe, Finset.coe_insert, Finset.coe_singleton, Finset.coe_insert,
        Finset.coe_singleton]
      exact D.pairwiseDisjoint_actPairs t (mem_toFinset.mp he₁) (mem_toFinset.mp he₂) hne
  have hsdiff := ncard_sdiff_add_ncard_of_subset hU_sub
  change (D.singleCut t).ncard + U.ncard = _ at hsdiff
  rw [hU_card] at hsdiff
  exact hsdiff

private theorem pinAC_notMem_masked (t : ℕ) {e : D.eqPairs} (he : e ∈ D.actPairs t) :
    (D.pinA e).1 ∉ (⋃ e' ∈ D.actPairs t, ({(D.pinB e').1, (D.pinD e').1} : Set (Edge c))) ∧
      (D.pinC e).1 ∉ (⋃ e' ∈ D.actPairs t, ({(D.pinB e').1, (D.pinD e').1} : Set (Edge c))) := by
  have check (g : D.Q.external) (hg_end : g ∈ D.Q.quotient.incidenceSet (D.Q.quotient.src e.1) \
      {e.1} ∪ D.Q.quotient.incidenceSet (D.Q.quotient.tgt e.1) \ {e.1})
      (hg_ne_B : g.1 ≠ (D.pinB e).1) (hg_ne_D : g.1 ≠ (D.pinD e).1) :
      g.1 ∉ ⋃ e' ∈ D.actPairs t, ({(D.pinB e').1, (D.pinD e').1} : Set (Edge c)) := by
    rintro ⟨_, ⟨e', rfl⟩, _, ⟨he', rfl⟩, hmem⟩
    by_cases hee' : e = e'
    · subst hee'
      rcases hmem with h | h
      · exact hg_ne_B h
      · exact hg_ne_D h
    · have hg_cut : g.1 ∈ (graph c).edgeCut (D.pastVerts t) := by
        rcases hmem with h | h <;> rw [h]
        · exact he'.2.1
        · exact he'.2.2
      have hsub₁ := (D.pairVerts_subset_pastVerts_iff e t).mpr he.1
      have hsub₂ := (D.pairVerts_subset_pastVerts_iff e' t).mpr he'.1
      have hend₁ : src g.1 ∈ D.pairVerts e ∨ tgt g.1 ∈ D.pairVerts e := by
        rcases hg_end with hg₁ | hg₂
        · have hs₁ :=
            (D.block_edgeCut_sdiff ⟨e.1, e.2.1⟩ (D.Q.quotient.src e.1) e.1 (Or.inl rfl)).2
          have hm : g.1 ∈ (graph c).edgeCut {v | v ∈ (D.Q.quotient.src e.1).1} \ {e.1.1} := by
            have := Fintype.ofFinite (Edge c)
            have hspec := (Multigraph.outerLow_outerHigh_spec (D.h3 ⟨e.1, e.2.1⟩) D.score
              (v := D.Q.quotient.src e.1) (Or.inl rfl)).2.1
            rw [hspec] at hg₁
            rw [hs₁]
            rcases hg₁ with rfl | rfl <;> simp
          rw [hs₁] at hm
          rcases hm with h | h <;> rw [h]
          · exact D.pinA_end e
          · exact D.pinB_end e
        · have hs₂ :=
            (D.block_edgeCut_sdiff ⟨e.1, e.2.1⟩ (D.Q.quotient.tgt e.1) e.1 (Or.inr rfl)).2
          have hm : g.1 ∈ (graph c).edgeCut {v | v ∈ (D.Q.quotient.tgt e.1).1} \ {e.1.1} := by
            have := Fintype.ofFinite (Edge c)
            have hspec := (Multigraph.outerLow_outerHigh_spec (D.h3 ⟨e.1, e.2.1⟩) D.score
              (v := D.Q.quotient.tgt e.1) (Or.inr rfl)).2.1
            rw [hspec] at hg₂
            rw [hs₂]
            rcases hg₂ with rfl | rfl <;> simp
          rw [hs₂] at hm
          rcases hm with h | h <;> rw [h]
          · exact D.pinC_end e
          · exact D.pinD_end e
      have hend₂ := D.pinBD_end e' hmem
      have hboth : src g.1 ∈ D.pastVerts t ∧ tgt g.1 ∈ D.pastVerts t := by
        rcases hend₁ with hs₁ | ht₁ <;> rcases hend₂ with hs₂ | ht₂
        · exact (disjoint_left.mp (D.disjoint_pairVerts hee') hs₁ hs₂).elim
        · exact ⟨hsub₁ hs₁, hsub₂ ht₂⟩
        · exact ⟨hsub₂ hs₂, hsub₁ ht₁⟩
        · exact (disjoint_left.mp (D.disjoint_pairVerts hee') ht₁ ht₂).elim
      exact hg_cut (iff_of_true hboth.1 hboth.2)
  have := Fintype.ofFinite (Edge c)
  have hinj := D.hsat.injective_ends_quotient
  have hbs := Multigraph.outerLow_outerHigh_spec (D.h3 ⟨e.1, e.2.1⟩) D.score
    (v := D.Q.quotient.src e.1) (Or.inl rfl)
  have hdt := Multigraph.outerLow_outerHigh_spec (D.h3 ⟨e.1, e.2.1⟩) D.score
    (v := D.Q.quotient.tgt e.1) (Or.inr rfl)
  have ha_mem : D.pinA e ∈ D.Q.quotient.incidenceSet (D.Q.quotient.src e.1) \ {e.1} := by
    dsimp only [pinA]; rw [hbs.2.1]; simp
  have hc_mem : D.pinC e ∈ D.Q.quotient.incidenceSet (D.Q.quotient.tgt e.1) \ {e.1} := by
    dsimp only [pinC]; rw [hdt.2.1]; simp
  have hd_mem : D.pinD e ∈ D.Q.quotient.incidenceSet (D.Q.quotient.tgt e.1) \ {e.1} := by
    dsimp only [pinD]; rw [hdt.2.1]; simp
  have hb_mem : D.pinB e ∈ D.Q.quotient.incidenceSet (D.Q.quotient.src e.1) \ {e.1} := by
    dsimp only [pinB]; rw [hbs.2.1]; simp
  have no_cross {x y : D.Q.external}
      (hx : x ∈ D.Q.quotient.incidenceSet (D.Q.quotient.src e.1) \ {e.1})
      (hy : y ∈ D.Q.quotient.incidenceSet (D.Q.quotient.tgt e.1) \ {e.1}) : x.1 ≠ y.1 := by
    intro hxy
    have hxy' : x = y := Subtype.ext hxy
    subst hxy'
    rcases hx.1 with hs | ht <;> rcases hy.1 with hs' | ht'
    · exact D.Q.quotient_loopless e.1 (hs.symm.trans hs')
    · exact hx.2 (hinj (by simp only [Multigraph.ends, hs, ht']))
    · exact hx.2 (hinj (by simp only [Multigraph.ends, ht, hs', Sym2.eq_swap]))
    · exact D.Q.quotient_loopless e.1 (ht.symm.trans ht')
  exact ⟨check (D.pinA e) (Or.inl ha_mem) (fun h => hbs.1 (Subtype.ext h)) (no_cross ha_mem hd_mem),
    check (D.pinC e) (Or.inr hc_mem) (fun h => no_cross hb_mem hc_mem h.symm)
      (fun h => hdt.1 (Subtype.ext h))⟩

private theorem notMem_internalEdges_pairVerts {e : D.eqPairs} {g : D.Q.external}
    (hg_not : g ∉ D.eqPairs) : g.1 ∉ internalEdges c (D.pairVerts e) := by
  rintro ⟨hs, ht⟩
  have hinj := D.hsat.injective_ends_quotient
  rw [D.mem_pairVerts_iff] at hs ht
  rcases hs with hs₁ | hs₂ <;> rcases ht with ht₁ | ht₂
  · exact g.2 (hs₁.trans ht₁.symm)
  · change D.Q.quotient.src g = _ at hs₁
    change D.Q.quotient.tgt g = _ at ht₂
    have hge : g = e.1 := hinj (by simp only [Multigraph.ends, hs₁, ht₂])
    exact hg_not (hge ▸ e.2)
  · change D.Q.quotient.src g = _ at hs₂
    change D.Q.quotient.tgt g = _ at ht₁
    have hge : g = e.1 := hinj (by simp only [Multigraph.ends, hs₂, ht₁, Sym2.eq_swap])
    exact hg_not (hge ▸ e.2)
  · exact g.2 (hs₂.trans ht₂.symm)

private theorem pin_notMem_eqPairs {B : D.Q.blocks} {e : D.eqPairs}
    (hB : B = D.Q.quotient.src e.1 ∨ B = D.Q.quotient.tgt e.1) (g : D.Q.external)
    (hg : g ∈ D.Q.quotient.incidenceSet B \ {e.1}) : g ∉ D.eqPairs := by
  intro hg_eq
  refine hg.2 ?_
  by_contra hne
  exact disjoint_left.mp (D.isMatching_eqPairs hg_eq e.2 hne) (hg.1.imp Eq.symm Eq.symm) hB

private theorem pinA_notMem_eqPairs (e : D.eqPairs) : D.pinA e ∉ D.eqPairs := by
  have := Fintype.ofFinite (Edge c)
  refine D.pin_notMem_eqPairs (e := e) (Or.inl rfl) (D.pinA e) ?_
  dsimp only [pinA]
  rw [(Multigraph.outerLow_outerHigh_spec (D.h3 ⟨e.1, e.2.1⟩) D.score (Or.inl rfl)).2.1]
  exact Or.inl rfl

private theorem pinB_notMem_eqPairs (e : D.eqPairs) : D.pinB e ∉ D.eqPairs := by
  have := Fintype.ofFinite (Edge c)
  refine D.pin_notMem_eqPairs (e := e) (Or.inl rfl) (D.pinB e) ?_
  dsimp only [pinB]
  rw [(Multigraph.outerLow_outerHigh_spec (D.h3 ⟨e.1, e.2.1⟩) D.score (Or.inl rfl)).2.1]
  exact Or.inr rfl

private theorem pinC_notMem_eqPairs (e : D.eqPairs) : D.pinC e ∉ D.eqPairs := by
  have := Fintype.ofFinite (Edge c)
  refine D.pin_notMem_eqPairs (e := e) (Or.inr rfl) (D.pinC e) ?_
  dsimp only [pinC]
  rw [(Multigraph.outerLow_outerHigh_spec (D.h3 ⟨e.1, e.2.1⟩) D.score (Or.inr rfl)).2.1]
  exact Or.inl rfl

private theorem pinD_notMem_eqPairs (e : D.eqPairs) : D.pinD e ∉ D.eqPairs := by
  have := Fintype.ofFinite (Edge c)
  refine D.pin_notMem_eqPairs (e := e) (Or.inr rfl) (D.pinD e) ?_
  dsimp only [pinD]
  rw [(Multigraph.outerLow_outerHigh_spec (D.h3 ⟨e.1, e.2.1⟩) D.score (Or.inr rfl)).2.1]
  exact Or.inr rfl

open Classical in
private noncomputable def intraPrefix : D.StepNode → Set (Vertex c)
  | .inl u => {v | v ∈ (D.Q.blockOf u.1).1.take ((D.Q.blockOf u.1).1.idxOf u.1)}
  | .inr _ => ∅

private theorem disjoint_preimage_intraPrefix (x : D.StepNode) :
    Disjoint (D.Q.blockOf ⁻¹' D.Q.quotient.pairNodeVerts D.M D.M D.score
      (D.pairLay.initial (D.pairLay (D.stepPairNode x) : ℕ))) (D.intraPrefix x) := by
  classical
  rcases x with u | e
  · refine disjoint_left.mpr fun v hvP hvT => ?_
    have hB : D.Q.blockOf v = D.Q.blockOf u.1 :=
      D.Q.mem_iff_blockOf_eq.mp (List.mem_of_mem_take hvT)
    rw [mem_preimage, hB, Multigraph.mem_pairNodeVerts_of_notMem u.2,
      Layout.mem_initial] at hvP
    exact lt_irrefl _ hvP
  · exact disjoint_empty _

private theorem ncard_edgeCut_intraPrefix_le (x : D.StepNode) :
    ((graph c).edgeCut (D.intraPrefix x)).ncard ≤ 3 * Nat.log 2 (Nat.card (Vertex c)) := by
  classical
  have := Fintype.ofFinite (Vertex c)
  rcases x with u | e
  · dsimp only [intraPrefix]
    refine (D.Q.ncard_edgeCut_take_le _ (D.Q.blockOf u.1).2 _
      (List.idxOf_lt_length_of_mem (D.Q.mem_blockOf u.1))).trans
      (Nat.mul_le_mul_left 3 (Nat.log_mono_right ?_))
    rw [Nat.card_eq_fintype_card]
    exact (D.Q.nodup _ (D.Q.blockOf u.1).2).length_le_card
  · dsimp only [intraPrefix]; simp

private theorem pastVerts_eq_preimage_union {t : ℕ} (ht : t < Nat.card D.StepNode) :
    let x := D.stepLayout.symm ⟨t, ht⟩
    let s := (D.pairLay (D.stepPairNode x) : ℕ)
    D.pastVerts t =
      D.Q.blockOf ⁻¹' D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s) ∪
        D.intraPrefix x := by
  classical
  dsimp only
  set x := D.stepLayout.symm ⟨t, ht⟩ with hx_def
  ext v
  simp only [pastVerts, Layout.initial_eq_of_lt_iff D.stepLayout_lt_iff ht, ← hx_def,
    mem_iUnion, mem_ofPred_eq, stepKey, Prod.Lex.toLex_lt_toLex, mem_union, mem_preimage]
  constructor
  · rintro ⟨y, hlt | ⟨hp_eq, hsub_lt⟩, hvy⟩
    · left
      rcases y with u' | e'
      · rcases hvy with rfl
        exact (Multigraph.mem_pairNodeVerts_of_notMem u'.2).mpr hlt
      · obtain hblk := (D.mem_pairVerts_iff e' v).mp hvy
        exact (Multigraph.mem_pairNodeVerts_of_mem D.hM (Subset.refl _) e'
          (hblk.imp Eq.symm Eq.symm)).mpr hlt
    · right
      have hp_node : D.stepPairNode y = D.stepPairNode x :=
        D.pairLay.injective (Fin.ext hp_eq)
      rcases x with u | e
      · rcases y with u' | e'
        · have hb : D.Q.blockOf u'.1 = D.Q.blockOf u.1 :=
            Subtype.mk.inj (Sum.inl.inj hp_node)
          rcases hvy with rfl
          dsimp only [stepSubIdx, intraPrefix] at hsub_lt ⊢
          rw [hb] at hsub_lt
          exact (List.mem_take_iff_idxOf_lt (D.Q.mem_iff_blockOf_eq.mpr hb)).mpr hsub_lt
        · cases hp_node
      · dsimp only [stepSubIdx] at hsub_lt
        omega
  · rintro (hvP | hvT)
    · by_cases hv_mat : D.Q.blockOf v ∈ D.Q.quotient.matchedVertices D.eqPairs
      · obtain ⟨e₀, he₀, hev⟩ := hv_mat
        have hinr :=
          (Multigraph.mem_pairNodeVerts_of_mem D.hM (Subset.refl _) ⟨e₀, he₀⟩ hev).mp hvP
        exact ⟨.inr ⟨e₀, he₀⟩, Or.inl hinr,
          (D.mem_pairVerts_iff ⟨e₀, he₀⟩ v).mpr (hev.imp Eq.symm Eq.symm)⟩
      · have hinl := (Multigraph.mem_pairNodeVerts_of_notMem hv_mat).mp hvP
        exact ⟨.inl ⟨v, hv_mat⟩, Or.inl hinl, rfl⟩
    · rcases x with u | e
      · dsimp only [intraPrefix] at hvT
        have hv_mem : v ∈ (D.Q.blockOf u.1).1 := List.mem_of_mem_take hvT
        have hblk : D.Q.blockOf v = D.Q.blockOf u.1 := D.Q.mem_iff_blockOf_eq.mp hv_mem
        have hp_eq : D.stepPairNode (.inl ⟨v, hblk ▸ u.2⟩) = D.stepPairNode (.inl u) := by
          dsimp only [stepPairNode]
          exact congrArg Sum.inl (Subtype.ext hblk)
        refine ⟨.inl ⟨v, hblk ▸ u.2⟩, Or.inr ⟨?_, ?_⟩, rfl⟩
        · exact congrArg (fun p => (D.pairLay p : ℕ)) hp_eq
        · dsimp only [stepSubIdx]
          rw [hblk]
          exact (List.mem_take_iff_idxOf_lt hv_mem).mp hvT
      · exact hvT.elim

/-- Effective real cut of `D` at step `t`, bounded by `D.pairLay`'s whole-block bound plus at most
`6 log₂ |Vertex c|` from the single unmatched block being expanded. -/
private theorem effective_cut_le {lam B_sup : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hsup : ∀ s : ℕ,
      let P := D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s)
      ((D.Q.quotient.edgeCut P).ncard : ℝ) -
          (1 - lam) * ((D.Q.quotient.activeCleanPairs D.M D.M D.score P).ncard : ℝ) ≤ B_sup)
    (t : ℕ) :
    ((D.singleCut t).ncard : ℝ) + (1 + lam) * ((D.actPairs t).ncard : ℝ) ≤
      B_sup + 6 * Nat.log 2 (Nat.card (Vertex c)) := by
  classical
  have := Fintype.ofFinite (Vertex c)
  have := Fintype.ofFinite (Edge c)
  have h1lam : 0 ≤ 1 - lam := by linarith
  have h1lam_le : 1 - lam ≤ 1 := by linarith
  have hB0 : 0 ≤ B_sup := by
    have hend := hsup (Nat.card (D.Q.quotient.PairNode D.M D.M D.score))
    dsimp only at hend
    have hinit : D.pairLay.initial (Nat.card (D.Q.quotient.PairNode D.M D.M D.score)) = univ :=
      D.pairLay.initial_of_card_le le_rfl
    have hP_u : D.Q.quotient.pairNodeVerts D.M D.M D.score univ = univ := by
      ext B; simp only [mem_univ, iff_true]
      by_cases hm : B ∈ D.Q.quotient.matchedVertices D.eqPairs
      · obtain ⟨e₀, he₀, heB⟩ := hm
        exact (Multigraph.mem_pairNodeVerts_of_mem D.hM (Subset.refl _) ⟨e₀, he₀⟩ heB).mpr trivial
      · exact (Multigraph.mem_pairNodeVerts_of_notMem hm).mpr trivial
    rw [hinit, hP_u] at hend
    have hc0 : D.Q.quotient.edgeCut univ = ∅ := by ext g; simp
    have ha0 : D.Q.quotient.activeCleanPairs D.M D.M D.score univ = ∅ := by
      ext g; simp [Multigraph.activeCleanPairs, hc0]
    rw [hc0, ha0] at hend
    simpa using hend
  have hident : ((D.singleCut t).ncard : ℝ) + (1 + lam) * ((D.actPairs t).ncard : ℝ) =
      (((graph c).edgeCut (D.pastVerts t)).ncard : ℝ) -
        (1 - lam) * ((D.actPairs t).ncard : ℝ) := by
    have h := D.ncard_singleCut_add_actPairs t
    have hR : ((D.singleCut t).ncard : ℝ) + 2 * ((D.actPairs t).ncard : ℝ) =
        (((graph c).edgeCut (D.pastVerts t)).ncard : ℝ) := by exact_mod_cast h
    linarith
  rw [hident]
  rcases lt_or_ge t (Nat.card D.StepNode) with ht | ht
  · let x := D.stepLayout.symm ⟨t, ht⟩
    let s := (D.pairLay (D.stepPairNode x) : ℕ)
    let P_s := D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s)
    let T_part := D.intraPrefix x
    have hT_disj : Disjoint (D.Q.blockOf ⁻¹' P_s) T_part := D.disjoint_preimage_intraPrefix x
    have hT_cut : ((graph c).edgeCut T_part).ncard ≤ 3 * Nat.log 2 (Nat.card (Vertex c)) :=
      D.ncard_edgeCut_intraPrefix_le x
    have hpast_eq : D.pastVerts t = D.Q.blockOf ⁻¹' P_s ∪ T_part := D.pastVerts_eq_preimage_union ht
    have hcut_le : ((graph c).edgeCut (D.pastVerts t)).ncard ≤
        (D.Q.quotient.edgeCut P_s).ncard + ((graph c).edgeCut T_part).ncard := by
      rw [hpast_eq, ← D.Q.ncard_edgeCut_preimage P_s]
      exact (graph c).ncard_edgeCut_union_le _ _
    let Lost : Set D.Q.external :=
      {e₀ | ∃ he : e₀ ∈ D.Q.quotient.activeCleanPairs D.M D.M D.score P_s,
        (⟨e₀, ⟨he.1, he.2.1⟩⟩ : D.eqPairs) ∉ D.actPairs t}
    have hact_split : (D.Q.quotient.activeCleanPairs D.M D.M D.score P_s).ncard ≤
        (D.actPairs t).ncard + Lost.ncard := by
      have hsub : D.Q.quotient.activeCleanPairs D.M D.M D.score P_s ⊆
          (Subtype.val '' D.actPairs t) ∪ Lost := by
        intro e₀ he₀
        by_cases hm : (⟨e₀, ⟨he₀.1, he₀.2.1⟩⟩ : D.eqPairs) ∈ D.actPairs t
        · exact Or.inl ⟨_, hm, rfl⟩
        · exact Or.inr ⟨he₀, hm⟩
      refine (ncard_le_ncard hsub).trans ((ncard_union_le _ _).trans ?_)
      rw [ncard_image_of_injective _ Subtype.val_injective]
    have hLost_le : Lost.ncard ≤ ((graph c).edgeCut T_part).ncard := by
      have h_wit : ∀ e₀ ∈ Lost, ∃ g ∈ (graph c).edgeCut T_part,
          g ∈ ({(D.Q.quotient.outerHigh D.score (D.Q.quotient.src e₀) e₀).1,
            (D.Q.quotient.outerHigh D.score (D.Q.quotient.tgt e₀) e₀).1} : Set (Edge c)) := by
        rintro e₀ ⟨he₀, hnot⟩
        let e : D.eqPairs := ⟨e₀, ⟨he₀.1, he₀.2.1⟩⟩
        have hinr_s : .inr e ∈ D.pairLay.initial s :=
          (Multigraph.mem_pairNodeVerts_of_mem D.hM (Subset.refl _) e (Or.inl rfl)).mp he₀.2.2.1
        have hinr_t : .inr e ∈ D.stepLayout.initial t := by
          simp only [Layout.initial_eq_of_lt_iff D.stepLayout_lt_iff ht, mem_ofPred_eq, stepKey,
            Prod.Lex.toLex_lt_toLex]
          exact Or.inl hinr_s
        have hB_pre : (D.pinB e).1 ∈ (graph c).edgeCut (D.Q.blockOf ⁻¹' P_s) := he₀.2.2.2.2.1
        have hD_pre : (D.pinD e).1 ∈ (graph c).edgeCut (D.Q.blockOf ⁻¹' P_s) := he₀.2.2.2.2.2
        have sdiff_cut {g : Edge c} (hg₁ : g ∈ (graph c).edgeCut (D.Q.blockOf ⁻¹' P_s))
            (hg₂ : g ∉ (graph c).edgeCut (D.pastVerts t)) : g ∈ (graph c).edgeCut T_part := by
          rw [hpast_eq] at hg₂
          simp only [Multigraph.mem_edgeCut, mem_union, not_not] at hg₁ hg₂ ⊢
          have hd_s : (graph c).src g ∈ D.Q.blockOf ⁻¹' P_s → (graph c).src g ∉ T_part :=
            fun h => disjoint_left.mp hT_disj h
          have hd_t : (graph c).tgt g ∈ D.Q.blockOf ⁻¹' P_s → (graph c).tgt g ∉ T_part :=
            fun h => disjoint_left.mp hT_disj h
          tauto
        by_cases hB_t : (D.pinB e).1 ∈ (graph c).edgeCut (D.pastVerts t)
        · have hD_not : (D.pinD e).1 ∉ (graph c).edgeCut (D.pastVerts t) :=
            fun hD_t => hnot ⟨hinr_t, hB_t, hD_t⟩
          exact ⟨(D.pinD e).1, sdiff_cut hD_pre hD_not, Or.inr rfl⟩
        · exact ⟨(D.pinB e).1, sdiff_cut hB_pre hB_t, Or.inl rfl⟩
      choose g_of hg_cut hg_pair using fun e₀ : Lost => h_wit e₀.1 e₀.2
      have hinj_g : Function.Injective fun e₀ : Lost =>
          (⟨g_of e₀, hg_cut e₀⟩ : (graph c).edgeCut T_part) := by
        intro x₁ x₂ heq
        have hg_eq : g_of x₁ = g_of x₂ := congrArg Subtype.val heq
        by_contra hne
        have hne_val : x₁.1 ≠ x₂.1 := fun h => hne (Subtype.ext h)
        have hdisj := Multigraph.pairwiseDisjoint_activeCleanPairs D.hM (Subset.refl _)
          (D.h3 ⟨x₁.1, x₁.2.1.1⟩) D.score P_s x₁.2.1 x₂.2.1 hne_val
        have hg_ext : g_of x₁ ∈ D.Q.external := by
          rcases hg_pair x₁ with h | h <;> rw [h] <;> exact Subtype.prop _
        let gx : D.Q.external := ⟨g_of x₁, hg_ext⟩
        have hm₁ : gx ∈ ({D.Q.quotient.outerHigh D.score (D.Q.quotient.src x₁.1) x₁.1,
            D.Q.quotient.outerHigh D.score (D.Q.quotient.tgt x₁.1) x₁.1} : Set D.Q.external) := by
          rcases hg_pair x₁ with h | h
          · exact Or.inl (Subtype.ext h)
          · exact Or.inr (Subtype.ext h)
        have hm₂ : gx ∈ ({D.Q.quotient.outerHigh D.score (D.Q.quotient.src x₂.1) x₂.1,
            D.Q.quotient.outerHigh D.score (D.Q.quotient.tgt x₂.1) x₂.1} : Set D.Q.external) := by
          rcases hg_pair x₂ with h | h
          · exact Or.inl (Subtype.ext (hg_eq.trans h))
          · exact Or.inr (Subtype.ext (hg_eq.trans h))
        exact disjoint_left.mp hdisj hm₁ hm₂
      have h1 := Nat.card_le_card_of_injective _ hinj_g
      rwa [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h1
    have hsup_s := hsup s
    dsimp only at hsup_s
    have hcut_R : (((graph c).edgeCut (D.pastVerts t)).ncard : ℝ) ≤
        ((D.Q.quotient.edgeCut P_s).ncard : ℝ) + ((graph c).edgeCut T_part).ncard := by
      exact_mod_cast hcut_le
    have hact_R : ((D.Q.quotient.activeCleanPairs D.M D.M D.score P_s).ncard : ℝ) ≤
        ((D.actPairs t).ncard : ℝ) + ((graph c).edgeCut T_part).ncard := by
      exact_mod_cast hact_split.trans (Nat.add_le_add_left hLost_le _)
    have hT_R : (((graph c).edgeCut T_part).ncard : ℝ) ≤
        3 * Nat.log 2 (Nat.card (Vertex c)) := by exact_mod_cast hT_cut
    have hm1 := mul_le_mul_of_nonneg_left hact_R h1lam
    have hm2 := mul_le_mul_of_nonneg_right h1lam_le
      (Nat.cast_nonneg ((graph c).edgeCut T_part).ncard)
    linarith
  · have hp_univ : D.pastVerts t = univ := D.pastVerts_of_card_le ht
    have hc0 : (graph c).edgeCut (D.pastVerts t) = ∅ := by ext g; simp [hp_univ]
    have ha0 : D.actPairs t = ∅ := by ext e; simp [actPairs, hc0]
    rw [hc0, ha0]
    simp only [ncard_empty, Nat.cast_zero, mul_zero, sub_zero]
    positivity

/-- State of `D.branchingProgram` at layer `t` induced by an edge assignment `α`. -/
private noncomputable def stateAt (t : ℕ) (α : Edge c → Bool) :
    (Edge c → Option Bool) × (D.eqPairs → Option (Fin 3)) :=
  letI := Classical.propDecidable
  (fun f => if f ∈ D.singleCut t then some (α f) else none,
    fun e => if e ∈ D.actPairs t then some (D.rectIdx e α) else none)

private theorem stateAt_zero (α : Edge c → Bool) :
    D.stateAt 0 α = (fun _ => none, fun _ => none) := by
  have hc0 : (graph c).edgeCut (D.pastVerts 0) = ∅ := by simp [D.pastVerts_zero]
  have hs0 : D.singleCut 0 = ∅ := by simp [singleCut, hc0]
  have ha0 : D.actPairs 0 = ∅ := by ext e; simp [actPairs, hc0]
  ext f <;> simp [stateAt, hs0, ha0]

private theorem stateAt_of_card_le {t : ℕ} (ht : Nat.card D.StepNode ≤ t) (α : Edge c → Bool) :
    D.stateAt t α = (fun _ => none, fun _ => none) := by
  have hc0 : (graph c).edgeCut (D.pastVerts t) = ∅ := by
    ext g; simp [D.pastVerts_of_card_le ht]
  have hs0 : D.singleCut t = ∅ := by simp [singleCut, hc0]
  have ha0 : D.actPairs t = ∅ := by ext e; simp [actPairs, hc0]
  ext f <;> simp [stateAt, hs0, ha0]

private theorem stateAt_eq_iff {t : ℕ} {α β : Edge c → Bool} :
    D.stateAt t α = D.stateAt t β ↔
      EqOn α β (D.singleCut t) ∧ ∀ e ∈ D.actPairs t, D.rectIdx e α = D.rectIdx e β := by
  simp only [stateAt, Prod.mk.injEq]
  refine and_congr ?_ ?_
  · refine ⟨fun h f hf => ?_, fun h => funext fun f => ?_⟩
    · simpa [hf] using congrFun h f
    · by_cases hf : f ∈ D.singleCut t
      · simp [hf, h hf]
      · simp [hf]
  · refine ⟨fun h e he => ?_, fun h => funext fun e => ?_⟩
    · simpa [he] using congrFun h e
    · by_cases he : e ∈ D.actPairs t
      · simp [he, h e he]
      · simp [he]

/-- **`3`-state pair-compressed read-once branching program** associated with `D` and a constraint
network `N` on `Compiler.graph c`. -/
noncomputable def branchingProgram {ι : Type*}
    (N : Network Bool ι (Vertex c) (Edge c)) :
    ReadOnceNBP ι Bool ((Edge c → Option Bool) × (D.eqPairs → Option (Fin 3))) where
  length := Nat.card D.StepNode + 1
  revealed t := if t ≤ Nat.card D.StepNode then N.readIn (D.pastVerts t) else univ
  revealed_zero := by simp [D.pastVerts_zero]
  revealed_length := by simp
  revealed_mono s t hst := by
    dsimp only
    split_ifs with hs ht ht
    · rintro i ⟨v, hv, hi⟩
      exact ⟨v, D.pastVerts_mono hst hv, hi⟩
    · exact subset_univ _
    · exact absurd (hst.trans ht) hs
    · exact le_rfl
  start := (fun _ => none, fun _ => none)
  accept := (fun _ => none, fun _ => none)
  Edge t m a m' := ∃ (β : Edge c → Bool) (y : ι → Bool),
    m = D.stateAt t β ∧ m' = D.stateAt (t + 1) β ∧
    ((if t + 1 ≤ Nat.card D.StepNode then N.readIn (D.pastVerts (t + 1)) else univ) \
      (if t ≤ Nat.card D.StepNode then N.readIn (D.pastVerts t) else univ)).domRestrict y = a ∧
    (∀ v ∈ D.pastVerts (t + 1) \ D.pastVerts t, N.Constraint v y β) ∧
    (∀ e ∈ D.actPairs t, GateSatisfies I (D.pairVerts e) β)

section NetworkProps

variable {ι : Type*} (N : Network Bool ι (Vertex c) (Edge c))
  (hG : N.toMultigraph = graph c)
  (hclean_N : ∀ v, IsCleanVertex v →
    (∀ x α, N.Constraint v x α ↔ Constraint I (fun _ => univ) v (fun _ => false) α) ∧
      N.readAt v = ∅)

include hG hclean_N

omit hG in
private theorem isAcceptingPath_stateAt {x : ι → Bool} {α : Edge c → Bool}
    (hα : N.Satisfies x α) :
    (D.branchingProgram N).IsAcceptingPath x fun t => D.stateAt t α where
  start := D.stateAt_zero α
  accept := D.stateAt_of_card_le (Nat.le_succ _) α
  edge _ _ := ⟨α, x, rfl, rfl, rfl, fun v _ => hα v,
    fun e _ v hv => (hclean_N v (D.isCleanVertex_of_mem_pairVerts e hv)).1 x α |>.mp (hα v)⟩

/-- **Three-region prefix gluing.** An accepting path of `D.branchingProgram N` comes from a global
satisfying assignment `α` whose `stateAt` matches the path at every layer. -/
private theorem exists_satisfies_of_isAcceptingPath {x : ι → Bool}
    {γ : ℕ → (Edge c → Option Bool) × (D.eqPairs → Option (Fin 3))}
    (hγ : (D.branchingProgram N).IsAcceptingPath x γ) :
    ∃ α, N.Satisfies x α ∧ ∀ s ≤ Nat.card D.StepNode + 1, γ s = D.stateAt s α := by
  classical
  -- Prove by induction on `t ≤ Nat.card D.StepNode + 1`.
  suffices ∀ t ≤ Nat.card D.StepNode + 1, ∃ (α : Edge c → Bool) (x_t : ι → Bool),
      EqOn x_t x ((D.branchingProgram N).revealed t) ∧
      (∀ v ∈ D.pastVerts t, N.Constraint v x_t α) ∧
      (∀ s ≤ t, γ s = D.stateAt s α) by
    obtain ⟨α, x_T, hx_T, hsat_T, hγ_T⟩ := this (Nat.card D.StepNode + 1) le_rfl
    have hx_eq : x_T = x := funext fun i => hx_T (by
      change i ∈ (D.branchingProgram N).revealed (D.branchingProgram N).length
      rw [(D.branchingProgram N).revealed_length]
      trivial)
    rw [hx_eq, D.pastVerts_of_card_le (Nat.le_succ _)] at hsat_T
    exact ⟨α, fun v => hsat_T v trivial, hγ_T⟩
  intro t ht_all
  induction t with
  | zero =>
    refine ⟨fun _ => false, x, eqOn_refl _ _, ?_, fun s hs => ?_⟩
    · rw [D.pastVerts_zero]; intro v hv; exact hv.elim
    · obtain rfl : s = 0 := Nat.eq_zero_of_le_zero hs
      exact hγ.start.trans (D.stateAt_zero _).symm
  | succ t ih =>
    obtain ⟨α_t, x_t, hx_t, hsat_t, hγ_t⟩ := ih (Nat.le_of_succ_le ht_all)
    obtain ⟨β, y, hm, hm', hdom, hcon_step, hgate_β⟩ := hγ.edge t ht_all
    have hst_eq : D.stateAt t α_t = D.stateAt t β := (hγ_t t le_rfl).symm.trans hm
    obtain ⟨heq_single, heq_rect⟩ := D.stateAt_eq_iff.mp hst_eq
    -- Splice inputs on `revealed t`.
    let x' : ι → Bool := fun i => if i ∈ (D.branchingProgram N).revealed t then x_t i else y i
    have hx'_eq : EqOn x' x ((D.branchingProgram N).revealed (t + 1)) := by
      intro i hi
      by_cases hit : i ∈ (D.branchingProgram N).revealed t
      · dsimp only [x']; rw [ite_eq_left hit]; exact hx_t hit
      · dsimp only [x']; rw [ite_eq_right hit]
        exact congrFun hdom ⟨i, hi, hit⟩
    -- At `t = Nat.card D.StepNode`, `pastVerts t = univ` and only unread inputs are updated.
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp ht_all) with rfl | ht_lt
    · refine ⟨α_t, x', hx'_eq, ?_, fun s hs => ?_⟩
      · intro v hv
        refine N.constraint_congr v x_t x' α_t α_t (fun i hsite => ?_) (fun _ _ => rfl)
          (hsat_t v (by rw [D.pastVerts_of_card_le le_rfl]; trivial))
        have hirev : i ∈ (D.branchingProgram N).revealed (Nat.card D.StepNode) := by
          change i ∈ if Nat.card D.StepNode ≤ Nat.card D.StepNode then _ else _
          rw [ite_eq_left le_rfl]
          exact ⟨v, by rw [D.pastVerts_of_card_le le_rfl]; trivial, hsite⟩
        dsimp only [x']
        exact (ite_eq_left hirev).symm
      · rcases Nat.of_le_succ hs with hs' | rfl
        · exact hγ_t s hs'
        · exact hγ.accept.trans (D.stateAt_of_card_le (Nat.le_succ _) α_t).symm
    -- Main step `t < Nat.card D.StepNode`: three-region splice of `α_t` and `β`.
    -- Baseline assignment `γ₀`: `β` on `(graph c).touching (D.pastVerts t)ᶜ`, `α_t` elsewhere.
    let γ₀ : Edge c → Bool := fun g =>
      if g ∈ (graph c).touching (D.pastVerts t)ᶜ then β g else α_t g
    -- On every `e ∈ D.actPairs t`, check `(γ₀ pinB, γ₀ pinD) = (β pinB, β pinD)` and
    -- `(γ₀ pinA, γ₀ pinC) = (α_t pinA, α_t pinC)`, giving internal witness `β_e`.
    have hpin_γ₀ (e : D.eqPairs) (he : e ∈ D.actPairs t) :
        γ₀ (D.pinB e).1 = β (D.pinB e).1 ∧ γ₀ (D.pinD e).1 = β (D.pinD e).1 ∧
          γ₀ (D.pinA e).1 = α_t (D.pinA e).1 ∧ γ₀ (D.pinC e).1 = α_t (D.pinC e).1 := by
      have cut_touch {g : Edge c} (hg : g ∈ (graph c).edgeCut (D.pastVerts t)) :
          g ∈ (graph c).touching (D.pastVerts t)ᶜ := by
        by_contra hnt
        rw [Multigraph.mem_touching, mem_compl_iff, mem_compl_iff, not_or, not_not, not_not] at hnt
        exact hg (iff_of_true hnt.1 hnt.2)
      have hB : γ₀ (D.pinB e).1 = β (D.pinB e).1 := ite_eq_left (cut_touch he.2.1)
      have hD : γ₀ (D.pinD e).1 = β (D.pinD e).1 := ite_eq_left (cut_touch he.2.2)
      have hsub_e := (D.pairVerts_subset_pastVerts_iff e t).mpr he.1
      obtain ⟨hA_notM, hC_notM⟩ := D.pinAC_notMem_masked t he
      have checkAC (g : Edge c)
          (hend : src g ∈ D.pairVerts e ∨ tgt g ∈ D.pairVerts e)
          (hnotM : g ∉ ⋃ e' ∈ D.actPairs t, ({(D.pinB e').1, (D.pinD e').1} : Set (Edge c))) :
          γ₀ g = α_t g := by
        dsimp only [γ₀]
        split_ifs with htc
        · have hg_cut : g ∈ (graph c).edgeCut (D.pastVerts t) := by
            rcases hend with hs | ht <;> rcases htc with hcs | hct
            · exact (hcs (hsub_e hs)).elim
            · exact fun hiff => hct (hiff.mp (hsub_e hs))
            · exact fun hiff => hcs (hiff.mpr (hsub_e ht))
            · exact (hct (hsub_e ht)).elim
          exact (heq_single ⟨hg_cut, hnotM⟩).symm
        · rfl
      exact ⟨hB, hD, checkAC _ (D.pinA_end e) hA_notM, checkAC _ (D.pinC_end e) hC_notM⟩
    have hex_patch : ∀ e : D.actPairs t,
        D.rectIdx e.1 γ₀ = D.rectIdx e.1 α_t ∧
        ∃ β_e : Edge c → Bool,
          EqOn β_e γ₀ (internalEdges c (D.pairVerts e.1))ᶜ ∧
          GateSatisfies I (D.pairVerts e.1) β_e := by
      rintro ⟨e, he⟩
      obtain ⟨hB, hD, hA, hC⟩ := hpin_γ₀ e he
      have hsat_α : GateSatisfies I (D.pairVerts e) α_t := by
        have hsub_e := (D.pairVerts_subset_pastVerts_iff e t).mpr he.1
        intro v hv
        exact (hclean_N v (D.isCleanVertex_of_mem_pairVerts e hv)).1 x_t α_t |>.mp
          (hsat_t v (hsub_e hv))
      have hrc_α := D.rectIdx_spec_of_sat e hsat_α
      have hrc_β := D.rectIdx_spec_of_sat e (hgate_β e he)
      rw [← heq_rect e he] at hrc_β
      exact D.rectIdx_eq_and_realize e (r := D.rectIdx e α_t)
        ⟨by rw [hB, hD]; exact hrc_β.1, by rw [hA, hC]; exact hrc_α.2⟩
    choose hrect_γ₀ β_patch hβ_eq hβ_sat using hex_patch
    -- Assemble `α'` by patching `internalEdges c (D.pairVerts e)` for each `e : D.actPairs t`.
    let α' : Edge c → Bool := fun g =>
      if h : ∃ e : D.actPairs t, g ∈ internalEdges c (D.pairVerts e.1) then
        β_patch h.choose g
      else γ₀ g
    have hint_unique {e₁ e₂ : D.actPairs t} {g : Edge c}
        (h₁ : g ∈ internalEdges c (D.pairVerts e₁.1))
        (h₂ : g ∈ internalEdges c (D.pairVerts e₂.1)) : e₁ = e₂ := by
      by_contra hne
      have hne_val : e₁.1 ≠ e₂.1 := fun h => hne (Subtype.ext h)
      exact disjoint_left.mp (D.disjoint_pairVerts hne_val) h₁.1 h₂.1
    have hα'_not_int {g : Edge c}
        (hn : ¬∃ e : D.actPairs t, g ∈ internalEdges c (D.pairVerts e.1)) : α' g = γ₀ g := by
      dsimp only [α']; exact dite_eq_right hn
    have hα'_on_pair (e : D.actPairs t) :
        EqOn α' (β_patch e) ((graph c).touching (D.pairVerts e.1)) := by
      intro g hg
      dsimp only [α']
      split_ifs with hex
      · set e' := hex.choose
        have he' : g ∈ internalEdges c (D.pairVerts e'.1) := hex.choose_spec
        suffices e' = e by rw [this]
        by_contra hne
        have hne_val : e'.1 ≠ e.1 := fun h => hne (Subtype.ext h)
        rcases hg with hs | ht
        · exact disjoint_left.mp (D.disjoint_pairVerts hne_val) he'.1 hs
        · exact disjoint_left.mp (D.disjoint_pairVerts hne_val) he'.2 ht
      · have hni : g ∉ internalEdges c (D.pairVerts e.1) := fun hin => hex ⟨e, hin⟩
        exact (hβ_eq e hni).symm
    have hα'_touch_compl : EqOn α' β ((graph c).touching (D.pastVerts t)ᶜ) := by
      intro g hg
      rw [hα'_not_int]
      · exact ite_eq_left hg
      · rintro ⟨⟨e, he⟩, hin⟩
        have hsub_e := (D.pairVerts_subset_pastVerts_iff e t).mpr he.1
        rcases hg with hs | ht
        · exact hs (hsub_e hin.1)
        · exact ht (hsub_e hin.2)
    refine ⟨α', x', hx'_eq, ?_, ?_⟩
    · -- Satisfaction on `D.pastVerts (t + 1)`.
      obtain ⟨hsdiff, hun, _⟩ := D.pastVerts_succ_sdiff ht_lt
      rw [hun]
      rintro v (hv_new | hv_old)
      · -- Vertex in `D.nodeVerts x = pastVerts (t + 1) \ pastVerts t ⊆ (pastVerts t)ᶜ`.
        have hv_compl : v ∈ (D.pastVerts t)ᶜ := by
          have hd := (D.pastVerts_succ_sdiff ht_lt).2.2
          exact disjoint_left.mp hd hv_new
        refine N.constraint_congr v y x' β α' (fun i hsite => ?_) (fun g hg => ?_)
          (hcon_step v (hsdiff ▸ hv_new))
        · have hnot_rev : i ∉ (D.branchingProgram N).revealed t := by
            change i ∉ if t ≤ Nat.card D.StepNode then N.readIn (D.pastVerts t) else univ
            rw [ite_eq_left ht_lt.le]
            rintro ⟨u, hu, husite⟩
            have huv : u = v := Option.some.inj (husite.symm.trans hsite)
            exact hv_compl (huv ▸ hu)
          dsimp only [x']
          exact (ite_eq_right hnot_rev).symm
        · symm
          apply hα'_touch_compl
          rw [hG] at hg
          rcases hg with hs | ht
          · exact Or.inl (hs.symm ▸ hv_compl)
          · exact Or.inr (ht.symm ▸ hv_compl)
      · -- Vertex in `D.pastVerts t`: either in some `pairVerts e` (`e ∈ actPairs t`) or outside.
        by_cases hv_act : ∃ e : D.actPairs t, v ∈ D.pairVerts e.1
        · obtain ⟨e, hve⟩ := hv_act
          have hv_cl := D.isCleanVertex_of_mem_pairVerts e.1 hve
          rw [(hclean_N v hv_cl).1 x' α']
          exact gateSatisfies_congr (fun g hg => (hα'_on_pair e hg).symm) (hβ_sat e) v hve
        · refine N.constraint_congr v x_t x' α_t α' (fun i hsite => ?_) (fun g hg => ?_)
            (hsat_t v hv_old)
          · have hirev : i ∈ (D.branchingProgram N).revealed t := by
              change i ∈ if t ≤ Nat.card D.StepNode then N.readIn (D.pastVerts t) else univ
              rw [ite_eq_left ht_lt.le]
              exact ⟨v, hv_old, hsite⟩
            dsimp only [x']
            exact (ite_eq_left hirev).symm
          · rw [hG] at hg
            symm
            rw [hα'_not_int]
            · dsimp only [γ₀]
              split_ifs with htc
              · have hg_cut : g ∈ (graph c).edgeCut (D.pastVerts t) := by
                  rcases hg with hs | ht <;> rcases htc with hcs | hct
                  · exact (hcs (hs.symm ▸ hv_old)).elim
                  · exact fun hiff => hct (hiff.mp (hs.symm ▸ hv_old))
                  · exact fun hiff => hcs (hiff.mpr (ht.symm ▸ hv_old))
                  · exact (hct (ht.symm ▸ hv_old)).elim
                have hnotM : g ∉ ⋃ e' ∈ D.actPairs t,
                    ({(D.pinB e').1, (D.pinD e').1} : Set (Edge c)) := by
                  rintro ⟨_, ⟨e', rfl⟩, _, ⟨he', rfl⟩, hmem⟩
                  have hend_e' := D.pinBD_end e' hmem
                  have hv_in_e' : v ∈ D.pairVerts e' := by
                    rcases hg with hs | ht <;> rcases hend_e' with hs' | ht'
                    · exact hs ▸ hs'
                    · -- Then `src g = v ∈ pastVerts t` and `tgt g ∈ pairVerts e' ⊆ pastVerts t`!
                      have hsub := (D.pairVerts_subset_pastVerts_iff e' t).mpr he'.1
                      exact (hg_cut (iff_of_true (hs.symm ▸ hv_old) (hsub ht'))).elim
                    · have hsub := (D.pairVerts_subset_pastVerts_iff e' t).mpr he'.1
                      exact (hg_cut (iff_of_true (hsub hs') (ht.symm ▸ hv_old))).elim
                    · exact ht ▸ ht'
                  exact hv_act ⟨⟨e', he'⟩, hv_in_e'⟩
                exact (heq_single ⟨hg_cut, hnotM⟩).symm
              · rfl
            · rintro ⟨e', hin⟩
              rcases hg with hs | ht
              · exact hv_act ⟨e', hs ▸ hin.1⟩
              · exact hv_act ⟨e', ht ▸ hin.2⟩
    · -- Path agreement `∀ s ≤ t + 1, γ s = D.stateAt s α'`.
      intro s hs_le
      rcases Nat.of_le_succ hs_le with hs_lt | rfl
      · -- Earlier layer `s ≤ t`: show `D.stateAt s α' = D.stateAt s α_t`.
        rw [hγ_t s hs_lt, eq_comm, D.stateAt_eq_iff]
        have hpast_sub : D.pastVerts s ⊆ D.pastVerts t := D.pastVerts_mono hs_lt
        refine ⟨fun g hg => ?_, fun e he_s => ?_⟩
        · -- `g ∈ D.singleCut s`: cannot be internal to any `pairVerts e'`.
          rw [hα'_not_int]
          · dsimp only [γ₀]
            split_ifs with htc
            · -- `g ∈ edgeCut (pastVerts s)` and touches `(pastVerts t)ᶜ`, so one endpoint is in
              -- `pastVerts s ⊆ pastVerts t` and the other is in `(pastVerts t)ᶜ`, giving
              -- `g ∈ edgeCut (pastVerts t)`!
              have hg_cut_s : g ∈ (graph c).edgeCut (D.pastVerts s) := hg.1
              have hg_cut_t : g ∈ (graph c).edgeCut (D.pastVerts t) := by
                rcases htc with hcs | hct
                · have ht_in_s : (graph c).tgt g ∈ D.pastVerts s :=
                    by_contra fun hn => hg_cut_s (iff_of_false (fun hs => hcs (hpast_sub hs)) hn)
                  exact fun hiff => hcs (hiff.mpr (hpast_sub ht_in_s))
                · have hs_in_s : (graph c).src g ∈ D.pastVerts s :=
                    by_contra fun hn => hg_cut_s (iff_of_false hn (fun ht => hct (hpast_sub ht)))
                  exact fun hiff => hct (hiff.mp (hpast_sub hs_in_s))
              -- Could `g ∈ {pinB e', pinD e'}` for `e' ∈ actPairs t`? If so, `e' ∈ actPairs s`,
              -- contradicting `g ∈ singleCut s`!
              have hnotM_t : g ∉ ⋃ e' ∈ D.actPairs t,
                  ({(D.pinB e').1, (D.pinD e').1} : Set (Edge c)) := by
                rintro ⟨_, ⟨e', rfl⟩, _, ⟨he'_t, rfl⟩, hmem⟩
                have hinr_s : .inr e' ∈ D.stepLayout.initial s := by
                  by_contra hnot_s
                  have hdisj_s : Disjoint (D.pairVerts e') (D.pastVerts s) := by
                    refine disjoint_iUnion₂_right.mpr fun y hy => ?_
                    exact D.pairwiseDisjoint_nodeVerts trivial trivial fun (heq : .inr e' = y) =>
                      hnot_s (by rwa [heq])
                  have hend_e' := D.pinBD_end e' hmem
                  -- One endpoint of `g` is in `pairVerts e'` (`∉ pastVerts s`) and the other is in
                  -- `(pastVerts t)ᶜ ⊆ (pastVerts s)ᶜ` (`∉ pastVerts s`), contradicting `hg_cut_s`!
                  have hsub_t := (D.pairVerts_subset_pastVerts_iff e' t).mpr he'_t.1
                  rcases hend_e' with hs_p | ht_p
                  · have ht_out_t : (graph c).tgt g ∉ D.pastVerts t :=
                      fun ht_in => hg_cut_t (iff_of_true (hsub_t hs_p) ht_in)
                    exact hg_cut_s (iff_of_false (disjoint_left.mp hdisj_s hs_p)
                      (fun ht_in => ht_out_t (hpast_sub ht_in)))
                  · have hs_out_t : (graph c).src g ∉ D.pastVerts t :=
                      fun hs_in => hg_cut_t (iff_of_true hs_in (hsub_t ht_p))
                    exact hg_cut_s (iff_of_false (fun hs_in => hs_out_t (hpast_sub hs_in))
                      (disjoint_left.mp hdisj_s ht_p))
                have hsub_s := (D.pairVerts_subset_pastVerts_iff e' s).mpr hinr_s
                have cut_s_of_t {f : Edge c}
                    (hf_end : src f ∈ D.pairVerts e' ∨ tgt f ∈ D.pairVerts e')
                    (hf_t : f ∈ (graph c).edgeCut (D.pastVerts t)) :
                    f ∈ (graph c).edgeCut (D.pastVerts s) := by
                  have hsub_t := (D.pairVerts_subset_pastVerts_iff e' t).mpr he'_t.1
                  rcases hf_end with hs_p | ht_p
                  · have ht_out : tgt f ∉ D.pastVerts t :=
                      fun ht_in => hf_t (iff_of_true (hsub_t hs_p) ht_in)
                    exact fun hiff => ht_out (hpast_sub (hiff.mp (hsub_s hs_p)))
                  · have hs_out : src f ∉ D.pastVerts t :=
                      fun hs_in => hf_t (iff_of_true hs_in (hsub_t ht_p))
                    exact fun hiff => hs_out (hpast_sub (hiff.mpr (hsub_s ht_p)))
                have he'_s : e' ∈ D.actPairs s :=
                  ⟨hinr_s, cut_s_of_t (D.pinB_end e') he'_t.2.1,
                    cut_s_of_t (D.pinD_end e') he'_t.2.2⟩
                exact hg.2 (mem_biUnion he'_s hmem)
              exact (heq_single ⟨hg_cut_t, hnotM_t⟩).symm
            · rfl
          · rintro ⟨⟨e', he'⟩, hin⟩
            by_cases hinr_s : .inr e' ∈ D.stepLayout.initial s
            · have hsub_s := (D.pairVerts_subset_pastVerts_iff e' s).mpr hinr_s
              exact hg.1 (iff_of_true (hsub_s hin.1) (hsub_s hin.2))
            · have hdisj_s : Disjoint (D.pairVerts e') (D.pastVerts s) := by
                refine disjoint_iUnion₂_right.mpr fun y hy => ?_
                exact D.pairwiseDisjoint_nodeVerts trivial trivial fun (heq : .inr e' = y) =>
                  hinr_s (by rwa [heq])
              exact hg.1 (iff_of_false (disjoint_left.mp hdisj_s hin.1)
                (disjoint_left.mp hdisj_s hin.2))
        · -- `e ∈ D.actPairs s`: check `D.rectIdx e α' = D.rectIdx e α_t`.
          have hinr_t : .inr e ∈ D.stepLayout.initial t := lt_of_lt_of_le he_s.1 hs_lt
          have hsub_t := (D.pairVerts_subset_pastVerts_iff e t).mpr hinr_t
          have hni_pin (p : D.Q.external) (hp : p ∉ D.eqPairs) :
              ¬∃ e' : D.actPairs t, p.1 ∈ internalEdges c (D.pairVerts e'.1) :=
            fun ⟨e', hin⟩ => D.notMem_internalEdges_pairVerts hp hin
          have hEq_γ₀ : D.rectIdx e α' = D.rectIdx e γ₀ :=
            D.rectIdx_congr e (hα'_not_int (hni_pin _ (D.pinA_notMem_eqPairs e)))
              (hα'_not_int (hni_pin _ (D.pinB_notMem_eqPairs e)))
              (hα'_not_int (hni_pin _ (D.pinC_notMem_eqPairs e)))
              (hα'_not_int (hni_pin _ (D.pinD_notMem_eqPairs e)))
          rw [hEq_γ₀]
          by_cases he_t : e ∈ D.actPairs t
          · exact hrect_γ₀ ⟨e, he_t⟩
          · -- When `e ∉ actPairs t`, any pin of `e` touching `(pastVerts t)ᶜ` lies in
            -- `edgeCut (pastVerts t)` and is outside `{pinB e', pinD e'}` for `e' ∈ actPairs t`,
            -- so `γ₀` agrees with `α_t` on all 4 pins of `e`!
            have pin_eq (g : Edge c) (hend : src g ∈ D.pairVerts e ∨ tgt g ∈ D.pairVerts e) :
                γ₀ g = α_t g := by
              dsimp only [γ₀]
              split_ifs with htc
              · have hg_cut_t : g ∈ (graph c).edgeCut (D.pastVerts t) := by
                  rcases hend with hs_p | ht_p <;> rcases htc with hcs | hct
                  · exact (hcs (hsub_t hs_p)).elim
                  · exact fun hiff => hct (hiff.mp (hsub_t hs_p))
                  · exact fun hiff => hcs (hiff.mpr (hsub_t ht_p))
                  · exact (hct (hsub_t ht_p)).elim
                have hnotM : g ∉ ⋃ e' ∈ D.actPairs t,
                    ({(D.pinB e').1, (D.pinD e').1} : Set (Edge c)) := by
                  rintro ⟨_, ⟨e', rfl⟩, _, ⟨he'_t, rfl⟩, hmem⟩
                  by_cases hee' : e = e'
                  · exact he_t (hee' ▸ he'_t)
                  · have hsub_e' := (D.pairVerts_subset_pastVerts_iff e' t).mpr he'_t.1
                    have hend' := D.pinBD_end e' hmem
                    rcases hend with hs₁ | ht₁ <;> rcases hend' with hs₂ | ht₂
                    · exact disjoint_left.mp (D.disjoint_pairVerts hee') hs₁ hs₂
                    · exact hg_cut_t (iff_of_true (hsub_t hs₁) (hsub_e' ht₂))
                    · exact hg_cut_t (iff_of_true (hsub_e' hs₂) (hsub_t ht₁))
                    · exact disjoint_left.mp (D.disjoint_pairVerts hee') ht₁ ht₂
                exact (heq_single ⟨hg_cut_t, hnotM⟩).symm
              · rfl
            exact D.rectIdx_congr e (pin_eq _ (D.pinA_end e)) (pin_eq _ (D.pinB_end e))
              (pin_eq _ (D.pinC_end e)) (pin_eq _ (D.pinD_end e))
      · -- Layer `t + 1`: show `γ (t + 1) = D.stateAt (t + 1) α'`.
        rw [hm', eq_comm, D.stateAt_eq_iff]
        have hpast_sub : D.pastVerts t ⊆ D.pastVerts (t + 1) :=
          D.pastVerts_mono (Nat.le_succ t)
        have touch_of_cut {g : Edge c} (hg : g ∈ (graph c).edgeCut (D.pastVerts (t + 1))) :
            g ∈ (graph c).touching (D.pastVerts t)ᶜ := by
          by_contra hnt
          rw [Multigraph.mem_touching, mem_compl_iff, mem_compl_iff, not_or, not_not,
            not_not] at hnt
          exact hg (iff_of_true (hpast_sub hnt.1) (hpast_sub hnt.2))
        refine ⟨fun g hg => hα'_touch_compl (touch_of_cut hg.1), fun e he_t1 => ?_⟩
        -- Either `e` was processed at step `t` (`pairVerts e ⊆ (pastVerts t)ᶜ`, all 4 pins touch
        -- `(pastVerts t)ᶜ`) or `e ∈ actPairs t`!
        by_cases hinr_t : .inr e ∈ D.stepLayout.initial t
        · have hsub_t := (D.pairVerts_subset_pastVerts_iff e t).mpr hinr_t
          have cut_t_of_t1 {g : Edge c}
              (hend : src g ∈ D.pairVerts e ∨ tgt g ∈ D.pairVerts e)
              (hg1 : g ∈ (graph c).edgeCut (D.pastVerts (t + 1))) :
              g ∈ (graph c).edgeCut (D.pastVerts t) := by
            rcases hend with hs_p | ht_p
            · have ht_out : tgt g ∉ D.pastVerts (t + 1) :=
                fun ht_in => hg1 (iff_of_true (hpast_sub (hsub_t hs_p)) ht_in)
              exact fun hiff => ht_out (hpast_sub (hiff.mp (hsub_t hs_p)))
            · have hs_out : src g ∉ D.pastVerts (t + 1) :=
                fun hs_in => hg1 (iff_of_true hs_in (hpast_sub (hsub_t ht_p)))
              exact fun hiff => hs_out (hpast_sub (hiff.mpr (hsub_t ht_p)))
          have he_t : e ∈ D.actPairs t :=
            ⟨hinr_t, cut_t_of_t1 (D.pinB_end e) he_t1.2.1,
              cut_t_of_t1 (D.pinD_end e) he_t1.2.2⟩
          have hni_pin (p : D.Q.external) (hp : p ∉ D.eqPairs) :
              ¬∃ e' : D.actPairs t, p.1 ∈ internalEdges c (D.pairVerts e'.1) :=
            fun ⟨e', hin⟩ => D.notMem_internalEdges_pairVerts hp hin
          have hEq_γ₀ : D.rectIdx e α' = D.rectIdx e γ₀ :=
            D.rectIdx_congr e (hα'_not_int (hni_pin _ (D.pinA_notMem_eqPairs e)))
              (hα'_not_int (hni_pin _ (D.pinB_notMem_eqPairs e)))
              (hα'_not_int (hni_pin _ (D.pinC_notMem_eqPairs e)))
              (hα'_not_int (hni_pin _ (D.pinD_notMem_eqPairs e)))
          rw [hEq_γ₀, hrect_γ₀ ⟨e, he_t⟩, heq_rect e he_t]
        · -- `e` entered at step `t`, so `pairVerts e ⊆ (pastVerts t)ᶜ` and all 4 pins touch
          -- `(pastVerts t)ᶜ`.
          have hdisj_e : Disjoint (D.pairVerts e) (D.pastVerts t) := by
            refine disjoint_iUnion₂_right.mpr fun y hy => ?_
            exact D.pairwiseDisjoint_nodeVerts trivial trivial fun (heq : .inr e = y) =>
              hinr_t (by rwa [heq])
          have touch_pin {g : Edge c} (hend : src g ∈ D.pairVerts e ∨ tgt g ∈ D.pairVerts e) :
              g ∈ (graph c).touching (D.pastVerts t)ᶜ :=
            hend.imp (fun hs => disjoint_left.mp hdisj_e hs) (fun ht => disjoint_left.mp hdisj_e ht)
          exact D.rectIdx_congr e (hα'_touch_compl (touch_pin (D.pinA_end e)))
            (hα'_touch_compl (touch_pin (D.pinB_end e)))
            (hα'_touch_compl (touch_pin (D.pinC_end e)))
            (hα'_touch_compl (touch_pin (D.pinD_end e)))

theorem accepted_branchingProgram : (D.branchingProgram N).accepted = N.accepted := by
  ext x
  exact ⟨fun ⟨γ, hγ⟩ => by
      obtain ⟨α, hα, -⟩ := D.exists_satisfies_of_isAcceptingPath N hG hclean_N hγ
      exact ⟨α, hα⟩,
    fun ⟨α, hα⟩ => ⟨_, D.isAcceptingPath_stateAt N hclean_N hα⟩⟩

theorem unambiguous_branchingProgram
    (hunique : ∀ x α β, N.Satisfies x α → N.Satisfies x β → α = β) :
    (D.branchingProgram N).Unambiguous := by
  intro x γ δ hγ hδ t ht
  obtain ⟨α, hα, hγα⟩ := D.exists_satisfies_of_isAcceptingPath N hG hclean_N hγ
  obtain ⟨β, hβ, hδβ⟩ := D.exists_satisfies_of_isAcceptingPath N hG hclean_N hδ
  rw [hγα t ht, hδβ t ht, hunique x α β hα hβ]

omit hG in
private theorem ncard_newly_le [Finite ι] (hm : ∀ v, (N.readAt v).ncard ≤ 1)
    {t : ℕ} (ht : t < Nat.card D.StepNode) :
    ((D.branchingProgram N).newly t).ncard ≤ 1 := by
  have hsub : (D.branchingProgram N).newly t ⊆
      N.readIn (D.nodeVerts (D.stepLayout.symm ⟨t, ht⟩)) := by
    rintro i ⟨hi₁, hi₂⟩
    dsimp only [branchingProgram] at hi₁ hi₂
    rw [ite_eq_left (Nat.succ_le_of_lt ht)] at hi₁
    rw [ite_eq_left ht.le] at hi₂
    obtain ⟨v, hv, hsite⟩ := hi₁
    rw [(D.pastVerts_succ_sdiff ht).2.1] at hv
    rcases hv with hv_node | hv_old
    · exact ⟨v, hv_node, hsite⟩
    · exact (hi₂ ⟨v, hv_old, hsite⟩).elim
  refine (ncard_le_ncard hsub).trans ?_
  rcases D.stepLayout.symm ⟨t, ht⟩ with u | e
  · have hread_eq : N.readIn {u.1} = N.readAt u.1 := by ext i; simp [Network.readIn, Network.readAt]
    dsimp only [nodeVerts]
    rw [hread_eq]
    exact hm u.1
  · have hem : N.readIn (D.pairVerts e) = ∅ := by
      ext i
      simp only [Network.readIn, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨v, hv, hsite⟩
      have hem_v := (hclean_N v (D.isCleanVertex_of_mem_pairVerts e hv)).2
      have hi_mem : i ∈ N.readAt v := hsite
      rw [hem_v] at hi_mem
      exact hi_mem
    dsimp only [nodeVerts]
    rw [hem, ncard_empty]
    exact Nat.zero_le 1

omit hG in
private theorem exists_ncard_revealed_eq [Finite ι] (hm : ∀ v, (N.readAt v).ncard ≤ 1)
    {k : ℕ} (hk : k ≤ N.read.ncard) :
    ∃ t ≤ Nat.card D.StepNode, ((D.branchingProgram N).revealed t).ncard = k := by
  have hlast : ((D.branchingProgram N).revealed (Nat.card D.StepNode)).ncard = N.read.ncard := by
    dsimp only [branchingProgram]
    rw [ite_eq_left le_rfl, D.pastVerts_of_card_le le_rfl]
    rfl
  refine Nat.exists_eq_of_forall_le_add_one
    (a := fun t => ((D.branchingProgram N).revealed t).ncard)
    (by rw [(D.branchingProgram N).revealed_zero, ncard_empty]; exact Nat.zero_le k)
    (by rw [hlast]; exact hk) fun t ht => ?_
  have hun : (D.branchingProgram N).revealed (t + 1) =
      (D.branchingProgram N).revealed t ∪ (D.branchingProgram N).newly t := by
    ext i
    simp only [ReadOnceNBP.newly, mem_union, mem_sdiff]
    have hmono := @(D.branchingProgram N).revealed_mono t (t + 1) (Nat.le_succ t) i
    tauto
  rw [hun]
  exact (ncard_union_le _ _).trans
    (Nat.add_le_add_left (D.ncard_newly_le N hclean_N hm ht) _)

private theorem ncard_image_path_le {t : ℕ} (ht : t ≤ Nat.card D.StepNode + 1) :
    ((fun x => (D.branchingProgram N).path x t) '' N.accepted).ncard ≤
      2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard := by
  classical
  have := Fintype.ofFinite (Edge c)
  have := Fintype.ofFinite D.eqPairs
  set F := D.singleCut t
  set A := D.actPairs t
  let φ : (F → Bool) × (A → Fin 3) →
      (Edge c → Option Bool) × (D.eqPairs → Option (Fin 3)) := fun sr =>
    (fun f => if hf : f ∈ F then some (sr.1 ⟨f, hf⟩) else none,
      fun e => if he : e ∈ A then some (sr.2 ⟨e, he⟩) else none)
  have hsub : (fun x => (D.branchingProgram N).path x t) '' N.accepted ⊆ range φ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← D.accepted_branchingProgram N hG hclean_N] at hx
    obtain ⟨α, -, hα⟩ := D.exists_satisfies_of_isAcceptingPath N hG hclean_N
      ((D.branchingProgram N).isAcceptingPath_path hx)
    refine ⟨(F.domRestrict α, A.domRestrict (D.rectIdx · α)), ?_⟩
    dsimp only [φ]
    rw [hα t ht]
    ext f <;> simp only [stateAt, domRestrict_apply] <;> split_ifs <;> rfl
  calc _ ≤ (range φ).ncard := ncard_le_ncard hsub (toFinite _)
    _ ≤ Nat.card ((F → Bool) × (A → Fin 3)) := by
        rw [← image_univ]
        exact (ncard_image_le (toFinite _)).trans (ncard_univ _).le
    _ = 2 ^ F.ncard * 3 ^ A.ncard := by
        rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
          Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
          Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]

omit hG hclean_N in
private theorem ncard_edges_last_le [Finite ι] :
    ((D.branchingProgram N).edges (Nat.card D.StepNode)).ncard ≤ 2 ^ N.readᶜ.ncard := by
  have hnewly : (D.branchingProgram N).newly (Nat.card D.StepNode) = N.readᶜ := by
    change (if Nat.card D.StepNode + 1 ≤ Nat.card D.StepNode then _ else univ) \
      (if Nat.card D.StepNode ≤ Nat.card D.StepNode then _ else univ) = _
    rw [ite_eq_right (by omega), ite_eq_left le_rfl, D.pastVerts_of_card_le le_rfl,
      compl_eq_univ_sdiff]
    rfl
  let φ : ((D.branchingProgram N).newly (Nat.card D.StepNode) → Bool) →
      ((Edge c → Option Bool) × (D.eqPairs → Option (Fin 3))) ×
        ((D.branchingProgram N).newly (Nat.card D.StepNode) → Bool) ×
        ((Edge c → Option Bool) × (D.eqPairs → Option (Fin 3))) := fun a =>
    ((fun _ => none, fun _ => none), a, (fun _ => none, fun _ => none))
  have hsub : (D.branchingProgram N).edges (Nat.card D.StepNode) ⊆ range φ := by
    rintro ⟨m, a, m'⟩ ⟨β, y, rfl, rfl, ha, -, -⟩
    refine ⟨a, ?_⟩
    subst ha
    dsimp only [φ]
    rw [D.stateAt_of_card_le le_rfl, D.stateAt_of_card_le (Nat.le_succ _)]
  calc _ ≤ (range φ).ncard := ncard_le_ncard hsub (toFinite _)
    _ ≤ Nat.card ((D.branchingProgram N).newly (Nat.card D.StepNode) → Bool) := by
        rw [← image_univ]
        exact (ncard_image_le (toFinite _)).trans (ncard_univ _).le
    _ = 2 ^ N.readᶜ.ncard := by
        rw [Nat.card_fun, Nat.card_coe_set_eq, hnewly,
          Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]

omit hG in
private theorem ncard_edges_step_le [Finite ι] (hdeg : (graph c).MaxDegreeLE 3)
    (hm : ∀ v, (N.readAt v).ncard ≤ 1) {t : ℕ} (ht : t < Nat.card D.StepNode) :
    ((D.branchingProgram N).edges t).ncard ≤
      24576 * (2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard) := by
  classical
  have := Fintype.ofFinite (Edge c)
  have := Fintype.ofFinite D.eqPairs
  set x := D.stepLayout.symm ⟨t, ht⟩
  obtain ⟨_, hun, hdisj⟩ := D.pastVerts_succ_sdiff ht
  set E_touch : Set (Edge c) := (graph c).edgeCut (D.nodeVerts x)
  have htouch_le : E_touch.ncard ≤ 4 := by
    rcases x with u | e
    · dsimp only [E_touch, nodeVerts]
      rw [Multigraph.edgeCut_singleton _ loopless]
      exact (hdeg u.1).trans (by decide)
    · dsimp only [E_touch, nodeVerts]
      rw [D.edgeCut_pairVerts e]
      refine (ncard_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
      refine (ncard_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
      refine (ncard_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
      simp
  set A_lost : Set D.eqPairs := D.actPairs t \ D.actPairs (t + 1)
  have hAlost_le : A_lost.ncard ≤ 4 := by
    have sdiff_cut {g : Edge c} (hg₀ : g ∈ (graph c).edgeCut (D.pastVerts t))
        (hg₁ : g ∉ (graph c).edgeCut (D.pastVerts (t + 1))) : g ∈ E_touch := by
      rw [hun] at hg₁
      simp only [Multigraph.mem_edgeCut, mem_union, not_not] at hg₀ hg₁
      simp only [E_touch, Multigraph.mem_edgeCut]
      have hd_s : (graph c).src g ∈ D.nodeVerts x → (graph c).src g ∉ D.pastVerts t :=
        fun h => disjoint_left.mp hdisj h
      have hd_t : (graph c).tgt g ∈ D.nodeVerts x → (graph c).tgt g ∉ D.pastVerts t :=
        fun h => disjoint_left.mp hdisj h
      tauto
    have hwit : ∀ e ∈ A_lost, ∃ g ∈ E_touch, g ∈ ({(D.pinB e).1, (D.pinD e).1} : Set (Edge c)) := by
      rintro e ⟨he_t, he_not⟩
      have hinr_1 : .inr e ∈ D.stepLayout.initial (t + 1) :=
        lt_of_lt_of_le he_t.1 (Nat.le_succ t)
      by_cases hB₁ : (D.pinB e).1 ∈ (graph c).edgeCut (D.pastVerts (t + 1))
      · have hD₁ : (D.pinD e).1 ∉ (graph c).edgeCut (D.pastVerts (t + 1)) :=
          fun h => he_not ⟨hinr_1, hB₁, h⟩
        exact ⟨(D.pinD e).1, sdiff_cut he_t.2.2 hD₁, Or.inr rfl⟩
      · exact ⟨(D.pinB e).1, sdiff_cut he_t.2.1 hB₁, Or.inl rfl⟩
    choose g_of hg_mem hg_pin using fun e : A_lost => hwit e.1 e.2
    have hinj : Function.Injective fun e : A_lost => (⟨g_of e, hg_mem e⟩ : E_touch) := by
      intro e₁ e₂ heq
      have hg_eq : g_of e₁ = g_of e₂ := congrArg Subtype.val heq
      by_contra hne
      have hne_val : e₁.1 ≠ e₂.1 := fun h => hne (Subtype.ext h)
      exact disjoint_left.mp (D.pairwiseDisjoint_actPairs t e₁.2.1 e₂.2.1 hne_val)
        (hg_pin e₁) (hg_eq.symm ▸ hg_pin e₂)
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h1
    exact h1.trans htouch_le
  set E_unmask : Set (Edge c) := ⋃ e ∈ A_lost, ({(D.pinB e).1, (D.pinD e).1} : Set (Edge c))
  have hEunmask_le : E_unmask.ncard ≤ 8 := by
    let Lfin : Finset D.eqPairs := A_lost.toFinset
    have hU_eq : E_unmask =
        ((Lfin.biUnion fun e => {(D.pinB e).1, (D.pinD e).1}) : Set (Edge c)) := by
      ext g; simp [E_unmask, Lfin]
    rw [hU_eq, ncard_coe_finset]
    calc (Lfin.biUnion fun e => {(D.pinB e).1, (D.pinD e).1}).card
        ≤ ∑ e ∈ Lfin, ({(D.pinB e).1, (D.pinD e).1} : Finset (Edge c)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ Lfin, 2 := Finset.sum_le_sum fun _ _ => Finset.card_insert_le _ _
      _ = 2 * A_lost.ncard := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm, ← ncard_eq_toFinset_card']
      _ ≤ 8 := by omega
  set E_extra : Set (Edge c) := E_touch ∪ E_unmask
  have hEextra_le : E_extra.ncard ≤ 12 := (ncard_union_le _ _).trans (by omega)
  set A_gain : Set D.eqPairs := D.actPairs (t + 1) \ D.actPairs t
  have hAgain_le : A_gain.ncard ≤ 1 := by
    have hsub_x : A_gain ⊆ {e | (.inr e : D.StepNode) = x} := by
      rintro e ⟨he_1, he_not⟩
      have hinr := he_1.1
      rw [D.stepLayout.initial_succ ht, mem_insert_iff] at hinr
      refine hinr.resolve_right fun hinr_t => he_not ?_
      have hsub_t := (D.pairVerts_subset_pastVerts_iff e t).mpr hinr_t
      have hpast_sub := D.pastVerts_mono (Nat.le_succ t)
      have cut_t {g : Edge c} (hend : src g ∈ D.pairVerts e ∨ tgt g ∈ D.pairVerts e)
          (hg1 : g ∈ (graph c).edgeCut (D.pastVerts (t + 1))) :
          g ∈ (graph c).edgeCut (D.pastVerts t) := by
        rcases hend with hs_p | ht_p
        · have ht_out : tgt g ∉ D.pastVerts (t + 1) :=
            fun ht_in => hg1 (iff_of_true (hpast_sub (hsub_t hs_p)) ht_in)
          exact fun hiff => ht_out (hpast_sub (hiff.mp (hsub_t hs_p)))
        · have hs_out : src g ∉ D.pastVerts (t + 1) :=
            fun hs_in => hg1 (iff_of_true hs_in (hpast_sub (hsub_t ht_p)))
          exact fun hiff => hs_out (hpast_sub (hiff.mpr (hsub_t ht_p)))
      exact ⟨hinr_t, cut_t (D.pinB_end e) he_1.2.1, cut_t (D.pinD_end e) he_1.2.2⟩
    refine (ncard_le_ncard hsub_x).trans ?_
    rcases x with u | e₀
    · have hem : {e : D.eqPairs | (.inr e : D.StepNode) = .inl u} = ∅ := by ext e; simp
      rw [hem, ncard_empty]; exact Nat.zero_le 1
    · have hsg : {e : D.eqPairs | (.inr e : D.StepNode) = .inr e₀} = {e₀} := by ext e; simp
      rw [hsg, ncard_singleton]
  -- Every `f ∈ singleCut (t + 1) \ E_extra` lies in `singleCut t`.
  have hpersist_single {f : Edge c} (hf₁ : f ∈ D.singleCut (t + 1)) (hnot_ex : f ∉ E_extra) :
      f ∈ D.singleCut t := by
    have hf_not_touch : f ∉ E_touch := fun h => hnot_ex (Or.inl h)
    have hf_not_unmask : f ∉ E_unmask := fun h => hnot_ex (Or.inr h)
    have hf_cut_t : f ∈ (graph c).edgeCut (D.pastVerts t) := by
      have hf_cut_1 := hf₁.1
      rw [hun] at hf_cut_1
      simp only [Multigraph.mem_edgeCut, mem_union] at hf_cut_1
      simp only [E_touch, Multigraph.mem_edgeCut, not_not] at hf_not_touch
      simp only [Multigraph.mem_edgeCut]
      tauto
    refine ⟨hf_cut_t, ?_⟩
    rintro ⟨_, ⟨e', rfl⟩, _, ⟨he'_t, rfl⟩, hmem⟩
    by_cases he'_1 : e' ∈ D.actPairs (t + 1)
    · exact hf₁.2 (mem_biUnion he'_1 hmem)
    · exact hf_not_unmask (mem_biUnion ⟨he'_t, he'_1⟩ hmem)
  set F := D.singleCut t
  set A := D.actPairs t
  set Nw := (D.branchingProgram N).newly t
  let Dom := ((F → Bool) × (A → Fin 3)) × (E_extra → Bool) × (Nw → Bool) × (A_gain → Fin 3)
  let ψ : Dom → ((Edge c → Option Bool) × (D.eqPairs → Option (Fin 3))) ×
      (Nw → Bool) × ((Edge c → Option Bool) × (D.eqPairs → Option (Fin 3))) :=
    fun ⟨⟨fs, ar⟩, ex, nw, gn⟩ =>
      ((fun f => if hf : f ∈ F then some (fs ⟨f, hf⟩) else none,
          fun e => if he : e ∈ A then some (ar ⟨e, he⟩) else none),
        nw,
        (fun f =>
            if hf₁ : f ∈ D.singleCut (t + 1) then
              if hex : f ∈ E_extra then some (ex ⟨f, hex⟩)
              else some (fs ⟨f, hpersist_single hf₁ hex⟩)
            else none,
          fun e =>
            if he₁ : e ∈ D.actPairs (t + 1) then
              if he₀ : e ∈ A then some (ar ⟨e, he₀⟩)
              else some (gn ⟨e, ⟨he₁, he₀⟩⟩)
            else none))
  have hsub : (D.branchingProgram N).edges t ⊆ range ψ := by
    rintro ⟨m, a, m'⟩ ⟨β, y, rfl, rfl, ha, -, -⟩
    refine ⟨((F.domRestrict β, A.domRestrict (D.rectIdx · β)),
      E_extra.domRestrict β, a, A_gain.domRestrict (D.rectIdx · β)), ?_⟩
    subst ha
    dsimp only [ψ]
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · ext f <;> simp only [stateAt, domRestrict_apply] <;> split_ifs <;> rfl
    · ext f
      · simp only [stateAt, domRestrict_apply]
        split_ifs <;> rfl
      · simp only [stateAt, domRestrict_apply]
        split_ifs <;> rfl
  have hNw_le : Nw.ncard ≤ 1 := D.ncard_newly_le N hclean_N hm ht
  calc ((D.branchingProgram N).edges t).ncard
      ≤ (range ψ).ncard := ncard_le_ncard hsub (toFinite _)
    _ ≤ Nat.card Dom := by
        rw [← image_univ]
        exact (ncard_image_le (toFinite _)).trans (ncard_univ _).le
    _ = (2 ^ F.ncard * 3 ^ A.ncard) * (2 ^ E_extra.ncard * (2 ^ Nw.ncard * 3 ^ A_gain.ncard)) := by
        dsimp only [Dom]
        simp only [Nat.card_prod, Nat.card_fun, Nat.card_coe_set_eq,
          Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
          Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
    _ ≤ (2 ^ F.ncard * 3 ^ A.ncard) * (2 ^ 12 * (2 ^ 1 * 3 ^ 1)) := by
        refine Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hEextra_le)
          (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hNw_le)
            (Nat.pow_le_pow_right (by decide) hAgain_le)))
    _ = 24576 * (2 ^ F.ncard * 3 ^ A.ncard) := by ring

omit hG in
theorem size_branchingProgram_le [Finite ι] (hdeg : (graph c).MaxDegreeLE 3)
    (hm : ∀ v, (N.readAt v).ncard ≤ 1) {B_sup : ℝ}
    (hsup : ∀ s : ℕ,
      let P := D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s)
      ((D.Q.quotient.edgeCut P).ncard : ℝ) -
          (2 - Real.logb 2 3) *
            ((D.Q.quotient.activeCleanPairs D.M D.M D.score P).ncard : ℝ) ≤ B_sup) :
    ((D.branchingProgram N).size : ℝ) ≤
      24576 * (Nat.card (Vertex c) : ℝ) *
        (2 : ℝ) ^ (B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) +
      (2 : ℝ) ^ N.readᶜ.ncard := by
  have hlog23_lo : (1 : ℝ) ≤ Real.logb 2 3 := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
    norm_num
  have hlog23_hi : Real.logb 2 3 ≤ 2 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
    norm_num
  set lam : ℝ := Real.logb 2 3 - 1
  have hlam0 : 0 ≤ lam := by dsimp [lam]; linarith
  have hlam1 : lam ≤ 1 := by dsimp [lam]; linarith
  have h1m : 1 - lam = 2 - Real.logb 2 3 := by dsimp [lam]; ring
  have h1p : 1 + lam = Real.logb 2 3 := by dsimp [lam]; ring
  have hsup' : ∀ s : ℕ,
      let P := D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s)
      ((D.Q.quotient.edgeCut P).ncard : ℝ) -
          (1 - lam) * ((D.Q.quotient.activeCleanPairs D.M D.M D.score P).ncard : ℝ) ≤ B_sup := by
    intro s; rw [h1m]; exact hsup s
  have hstate_rpow (t : ℕ) :
      ((2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) := by
    have heff := D.effective_cut_le hlam0 hlam1 hsup' t
    rw [h1p] at heff
    have h3eq : ((3 : ℝ) ^ (D.actPairs t).ncard) =
        (2 : ℝ) ^ (Real.logb 2 3 * (D.actPairs t).ncard) := by
      rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
        Real.rpow_natCast]
    push_cast
    rw [h3eq, ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) heff
  rw [ReadOnceNBP.size, show (D.branchingProgram N).length = Nat.card D.StepNode + 1 from rfl,
    Finset.sum_range_succ, Nat.cast_add, Nat.cast_sum]
  refine add_le_add ?_ ?_
  · calc ∑ t ∈ Finset.range (Nat.card D.StepNode), (((D.branchingProgram N).edges t).ncard : ℝ)
        ≤ ∑ _t ∈ Finset.range (Nat.card D.StepNode),
            24576 * (2 : ℝ) ^ (B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) := by
          refine Finset.sum_le_sum fun t ht => ?_
          have ht' := Finset.mem_range.mp ht
          have hstep : (((D.branchingProgram N).edges t).ncard : ℝ) ≤
              24576 * ((2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard : ℕ) : ℝ) := by
            exact_mod_cast D.ncard_edges_step_le N hclean_N hdeg hm ht'
          exact hstep.trans (mul_le_mul_of_nonneg_left (hstate_rpow t) (by norm_num))
      _ = (Nat.card D.StepNode : ℝ) *
            (24576 * (2 : ℝ) ^ (B_sup + 6 * Nat.log 2 (Nat.card (Vertex c)))) := by
          simp
      _ ≤ 24576 * (Nat.card (Vertex c) : ℝ) *
            (2 : ℝ) ^ (B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) := by
          have hcard : (Nat.card D.StepNode : ℝ) ≤ Nat.card (Vertex c) := by
            exact_mod_cast D.card_stepNode_le
          have hrpos : 0 ≤ (2 : ℝ) ^ (B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) := by positivity
          nlinarith
  · exact_mod_cast D.ncard_edges_last_le N

omit hG in
private theorem mul_size_branchingProgram_le_rpow [Finite ι]
    (hV_pos : 1 ≤ Nat.card (Vertex c)) (hdeg : (graph c).MaxDegreeLE 3)
    (hm : ∀ v, (N.readAt v).ncard ≤ 1) {K : ℕ} (hK : 1 ≤ K)
    (hu : 2 ^ N.readᶜ.ncard ≤ K) {B_sup : ℝ}
    (hsup : ∀ s : ℕ,
      let P := D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s)
      ((D.Q.quotient.edgeCut P).ncard : ℝ) -
          (2 - Real.logb 2 3) *
            ((D.Q.quotient.activeCleanPairs D.M D.M D.score P).ncard : ℝ) ≤ B_sup) :
    (((K - 1) ^ 2 * (D.branchingProgram N).size : ℕ) : ℝ) ≤
      (2 : ℝ) ^
        (max 0 B_sup + 15 + 3 * Real.logb 2 K + 7 * Real.logb 2 (Nat.card (Vertex c))) := by
  set V := Nat.card (Vertex c)
  set B' := max 0 B_sup
  have hsup' : ∀ s : ℕ,
      let P := D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s)
      ((D.Q.quotient.edgeCut P).ncard : ℝ) -
          (2 - Real.logb 2 3) *
            ((D.Q.quotient.activeCleanPairs D.M D.M D.score P).ncard : ℝ) ≤ B' :=
    fun s => (hsup s).trans (le_max_right 0 B_sup)
  have hsize := D.size_branchingProgram_le N hclean_N hdeg hm hsup'
  have hV1 : (1 : ℝ) ≤ V := by exact_mod_cast hV_pos
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have huR : (2 : ℝ) ^ N.readᶜ.ncard ≤ K := by exact_mod_cast hu
  have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (B' + 6 * Nat.log 2 V) :=
    Real.one_le_rpow (by norm_num) (add_nonneg (le_max_left 0 B_sup) (by positivity))
  have hsize' : ((D.branchingProgram N).size : ℝ) ≤
      24577 * K * V * (2 : ℝ) ^ (B' + 6 * Nat.log 2 V) := by
    have hVK : (1 : ℝ) ≤ V * K := by nlinarith
    have hpow0 : 0 ≤ (2 : ℝ) ^ (B' + 6 * Nat.log 2 V) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hVK hpow0,
      mul_le_mul_of_nonneg_left hK1 (by positivity : 0 ≤ 24576 * (V : ℝ) *
        (2 : ℝ) ^ (B' + 6 * Nat.log 2 V))]
  have hKsq : (((K - 1 : ℕ) ^ 2 : ℕ) : ℝ) ≤ (K : ℝ) ^ 2 := by
    have hle : (K - 1 : ℕ) ≤ K := Nat.sub_le K 1
    exact_mod_cast Nat.pow_le_pow_left hle 2
  have hprod : (((K - 1) ^ 2 * (D.branchingProgram N).size : ℕ) : ℝ) ≤
      24577 * (K : ℝ) ^ 3 * V * (2 : ℝ) ^ (B' + 6 * Nat.log 2 V) := by
    rw [Nat.cast_mul]
    calc (((K - 1 : ℕ) ^ 2 : ℕ) : ℝ) * ((D.branchingProgram N).size : ℝ)
        ≤ (K : ℝ) ^ 2 * (24577 * K * V * (2 : ℝ) ^ (B' + 6 * Nat.log 2 V)) :=
          mul_le_mul hKsq hsize' (Nat.cast_nonneg _) (by positivity)
      _ = 24577 * (K : ℝ) ^ 3 * V * (2 : ℝ) ^ (B' + 6 * Nat.log 2 V) := by ring
  have h15 : (24577 : ℝ) ≤ (2 : ℝ) ^ (15 : ℝ) := by norm_num
  have hK_rpow : (K : ℝ) ^ 3 = (2 : ℝ) ^ (3 * Real.logb 2 K) := by
    have hKr : (K : ℝ) = (2 : ℝ) ^ Real.logb 2 K :=
      (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
    conv_lhs => rw [hKr, ← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num)]
    ring_nf
  have hV_rpow : (V : ℝ) = (2 : ℝ) ^ Real.logb 2 V :=
    (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
  have hnatlog : (Nat.log 2 V : ℝ) ≤ Real.logb 2 V := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  refine hprod.trans ?_
  calc 24577 * (K : ℝ) ^ 3 * V * (2 : ℝ) ^ (B' + 6 * Nat.log 2 V)
      ≤ (2 : ℝ) ^ (15 : ℝ) * (2 : ℝ) ^ (3 * Real.logb 2 K) * (2 : ℝ) ^ Real.logb 2 V *
          (2 : ℝ) ^ (B' + 6 * Nat.log 2 V) := by
        rw [hK_rpow]
        conv_lhs => rw [show 24577 * (2 : ℝ) ^ (3 * Real.logb 2 K) * (V : ℝ) =
          24577 * (2 : ℝ) ^ (3 * Real.logb 2 K) * (2 : ℝ) ^ Real.logb 2 V by rw [← hV_rpow]]
        gcongr
    _ = (2 : ℝ) ^ (15 + 3 * Real.logb 2 K + Real.logb 2 V + (B' + 6 * Nat.log 2 V)) := by
        rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
          ← Real.rpow_add (by norm_num)]
    _ ≤ (2 : ℝ) ^ (B' + 15 + 3 * Real.logb 2 K + 7 * Real.logb 2 V) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end NetworkProps

private theorem sq_correlation_quadForm_le {n : ℕ} {c : Circuit σ n 1}
    {I : Interpretation σ Bool} (D : U2PairData c I) (Acc : Set Bool)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) {e B_sup : ℝ}
    (hQ : ∀ U : Set (Fin n), U.ncard = n / 2 → ((n / 2 : ℕ) : ℝ) ≤ (Q + Qᵀ).cutRank U + e)
    (hread : n / 2 ≤ (network c I fun _ => Acc).read.ncard)
    (hsup : ∀ s : ℕ,
      let P := D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s)
      ((D.Q.quotient.edgeCut P).ncard : ℝ) -
          (2 - Real.logb 2 3) *
            ((D.Q.quotient.activeCleanPairs D.M D.M D.score P).ncard : ℝ) ≤ B_sup) :
    correlation {x | BitString.quadForm Q x} {x | c.eval I x 0 ∈ Acc} ^ 2 ≤
      (2 : ℝ) ^ (B_sup - (n : ℝ) / 2 + 6 * Nat.log 2 (Nat.card (Vertex c)) + e + 3 / 2) := by
  classical
  set T := {x : Fin n → Bool | c.eval I x 0 ∈ Acc}
  set N₁ := network c I fun _ => Acc
  set N₀ := network c I fun _ => Accᶜ
  have hclean₁ : ∀ v, IsCleanVertex v →
      (∀ x α, N₁.Constraint v x α ↔ Constraint I (fun _ => univ) v (fun _ => false) α) ∧
        N₁.readAt v = ∅ :=
    fun v hv => ⟨constraint_iff_of_isCleanVertex I _ hv, readAt_eq_empty_of_isCleanVertex I _ hv⟩
  have hclean₀ : ∀ v, IsCleanVertex v →
      (∀ x α, N₀.Constraint v x α ↔ Constraint I (fun _ => univ) v (fun _ => false) α) ∧
        N₀.readAt v = ∅ :=
    fun v hv => ⟨constraint_iff_of_isCleanVertex I _ hv, readAt_eq_empty_of_isCleanVertex I _ hv⟩
  set P₁ := D.branchingProgram N₁
  set P₀ := D.branchingProgram N₀
  have hT₁ : P₁.accepted = T := by
    rw [D.accepted_branchingProgram N₁ rfl hclean₁, accepted_network_eq_eval]
  have hT₀ : P₀.accepted = Tᶜ := by
    rw [D.accepted_branchingProgram N₀ rfl hclean₀, accepted_network_eq_eval]; rfl
  obtain ⟨t, ht, hX⟩ :=
    D.exists_ncard_revealed_eq N₁ hclean₁ (ncard_readAt_le I _) hread
  have hrev_eq : P₀.revealed t = P₁.revealed t := rfl
  have htP₁ : t ≤ P₁.length := Nat.le_succ_of_le ht
  have htP₀ : t ≤ P₀.length := Nat.le_succ_of_le ht
  let msg : (Fin n → Bool) →
      Bool × ((Edge c → Option Bool) × (D.eqPairs → Option (Fin 3))) := fun x =>
    if x ∈ T then (true, P₁.path x t) else (false, P₀.path x t)
  have hclass₁ {x : Fin n → Bool} (hx : x ∈ T) : {y | msg y = msg x} = P₁.sweep.peers t x := by
    ext y
    rw [mem_ofPred_eq, ReadOnceNBP.mem_peers_sweep, hT₁]
    by_cases hy : y ∈ T <;> simp [msg, hx, hy]
  have hclass₀ {x : Fin n → Bool} (hx : x ∉ T) : {y | msg y = msg x} = P₀.sweep.peers t x := by
    ext y
    rw [mem_ofPred_eq, ReadOnceNBP.mem_peers_sweep, hT₀]
    by_cases hy : y ∈ T <;> simp [msg, hx, hy]
  have H := sq_correlation_quadForm_mul_le Q T msg (P₁.revealed t)
    (fun x y h => by by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;> simp_all [msg]) fun x => ?_
  · have hrange : range msg ⊆ Prod.mk true '' ((fun x => P₁.path x t) '' N₁.accepted) ∪
        Prod.mk false '' ((fun x => P₀.path x t) '' N₀.accepted) := by
      rintro _ ⟨x, rfl⟩
      by_cases hx : x ∈ T
      · refine Or.inl ⟨_, ⟨x, ?_, rfl⟩, by simp [msg, hx]⟩
        rwa [accepted_network_eq_eval]
      · refine Or.inr ⟨_, ⟨x, ?_, rfl⟩, by simp [msg, hx]⟩
        rw [accepted_network_eq_eval]; exact hx
    have h₁ := D.ncard_image_path_le N₁ rfl hclean₁ htP₁
    have h₀ := D.ncard_image_path_le N₀ rfl hclean₀ htP₀
    have hcount : (range msg).ncard ≤
        2 * (2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard) :=
      calc (range msg).ncard
          ≤ (Prod.mk true '' ((fun x => P₁.path x t) '' N₁.accepted)).ncard +
              (Prod.mk false '' ((fun x => P₀.path x t) '' N₀.accepted)).ncard :=
            (ncard_le_ncard hrange (toFinite _)).trans (ncard_union_le _ _)
        _ ≤ ((fun x => P₁.path x t) '' N₁.accepted).ncard +
              ((fun x => P₀.path x t) '' N₀.accepted).ncard :=
            Nat.add_le_add (ncard_image_le (toFinite _)) (ncard_image_le (toFinite _))
        _ ≤ 2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard +
              2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard :=
            Nat.add_le_add h₁ h₀
        _ = 2 * (2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard) := (two_mul _).symm
    have hlog23_lo : (1 : ℝ) ≤ Real.logb 2 3 := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]; norm_num
    have hlog23_hi : Real.logb 2 3 ≤ 2 := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]; norm_num
    set lam : ℝ := Real.logb 2 3 - 1
    have heff := D.effective_cut_le (lam := lam) (by dsimp [lam]; linarith)
      (by dsimp [lam]; linarith) (fun s => by
        change _ - (1 - lam) * _ ≤ B_sup
        rw [show 1 - lam = 2 - Real.logb 2 3 by dsimp [lam]; ring]
        exact hsup s) t
    rw [show 1 + lam = Real.logb 2 3 by dsimp [lam]; ring] at heff
    have hstate_rpow :
        ((2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard : ℕ) : ℝ) ≤
          (2 : ℝ) ^ (B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) := by
      have h3eq : ((3 : ℝ) ^ (D.actPairs t).ncard) =
          (2 : ℝ) ^ (Real.logb 2 3 * (D.actPairs t).ncard) := by
        rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
          Real.rpow_natCast]
      push_cast
      rw [h3eq, ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_add (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) heff
    have hmul_le : correlation {x | BitString.quadForm Q x} T ^ 2 *
        2 ^ (Q + Qᵀ).cutRank (P₁.revealed t) ≤
          (2 : ℝ) ^ (1 + B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) := by
      calc correlation {x | BitString.quadForm Q x} T ^ 2 *
            2 ^ (Q + Qᵀ).cutRank (P₁.revealed t)
          ≤ ((range msg).ncard : ℝ) := H
        _ ≤ 2 * ((2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard : ℕ) : ℝ) := by
            exact_mod_cast hcount
        _ ≤ 2 * (2 : ℝ) ^ (B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) :=
            mul_le_mul_of_nonneg_left hstate_rpow (by norm_num)
        _ = (2 : ℝ) ^ (1 + B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) := by
            symm
            rw [add_assoc 1 B_sup _, Real.rpow_add (by norm_num), Real.rpow_one]
    have hpos : (0 : ℝ) < 2 ^ (Q + Qᵀ).cutRank (P₁.revealed t) := by positivity
    have hdiv : correlation {x | BitString.quadForm Q x} T ^ 2 ≤
        (2 : ℝ) ^ (1 + B_sup + 6 * Nat.log 2 (Nat.card (Vertex c)) -
          (Q + Qᵀ).cutRank (P₁.revealed t)) := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_natCast]
      exact (le_div_iff₀ hpos).mpr hmul_le
    have hcut_rk := hQ (P₁.revealed t) hX
    have hhalf : (n : ℝ) / 2 - 1 / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
      have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (show n ≤ 2 * (n / 2) + 1 by omega)
      linarith
    exact hdiv.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by linarith only [hcut_rk, hhalf]))
  · have hex_rect {Y X : Set (Fin n)} (h : Y = X) (A : Set (Y → Bool))
        (B : Set (↥Yᶜ → Bool)) : ∃ A' B', rectangle Y A B = rectangle X A' B' :=
      h ▸ ⟨A, B, rfl⟩
    by_cases hx : x ∈ T
    · rw [hclass₁ hx, (D.unambiguous_branchingProgram N₁ rfl hclean₁
        fun _ _ _ => satisfies_unique).peers_eq_rectangle htP₁ x]
      exact ⟨_, _, rfl⟩
    · rw [hclass₀ hx, (D.unambiguous_branchingProgram N₀ rfl hclean₀
        fun _ _ _ => satisfies_unique).peers_eq_rectangle htP₀ x]
      exact hex_rect hrev_eq _ _

end U2PairData

end U2BranchingProgram

end Cslib.Circuits.Frontier.Compiler

/-! ### `U₂` cubic pair-node layout hypothesis and circuit lower-bound reductions -/

namespace Cslib.Circuits.Frontier

open Set Filter Asymptotics Matrix Cslib.Circuits.Frontier.Compiler

universe v

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

private theorem read_hiddenNetwork_zero {σ : Signature} {n m_out : ℕ}
    (c : Circuit σ n m_out) (I : Interpretation σ Bool) (Acc : Fin m_out → Set Bool) :
    (hiddenNetwork (k := 0) c I Acc).read = (network c I Acc).read := by
  ext i
  simp only [hiddenNetwork, Network.read, Network.readIn, Network.hide, Network.reindex,
    mem_ofPred_eq, mem_univ, true_and, Equiv.symm_symm]
  have hfin : (@finSumFinEquiv n 0) (.inl i) = i := Fin.ext rfl
  rw [hfin]

/-- Combine `exists_u2_saturated`, `Multigraph.exists_isMatching_mul_eight_ge`, and
`U2CubicPairBound p B_pair` to construct `U2PairData` for any `U₂` circuit with uniform constant
`C₀` depending only on `(p, B_pair, ξ)`. -/
private theorem exists_u2PairData_of_u2CubicPairBound {p B_pair : ℝ} (_hp : 0 < p)
    (hBp_le : B_pair ≤ 2 * p) (hbound : U2CubicPairBound p B_pair)
    (hδA : 2 * p - B_pair ≤ (7 / 8) * B_pair + (1 / 8) * (2 * p)) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ C₀ : ℝ, ∀ {n k : ℕ} {σ : Signature.{v}} {I : Interpretation σ Bool},
      I.IsU2 → ∀ (Acc : Set Bool) (c : Circuit σ (n + k) 1),
        ∃ D : U2PairData c I, ∀ s_idx : ℕ,
          let P := D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s_idx)
          ((D.Q.quotient.edgeCut P).ncard : ℝ) -
              (2 - Real.logb 2 3) *
                ((D.Q.quotient.activeCleanPairs D.M D.M D.score P).ncard : ℝ) ≤
            ((7 / 8) * B_pair + (1 / 8) * (2 * p)) * c.innerSize -
              (((7 / 8) * B_pair + (1 / 8) * (2 * p)) - (2 * p - B_pair)) *
                (hiddenNetwork c I fun _ => Acc).read.ncard +
              ξ * Nat.card (Vertex c) + C₀ := by
  classical
  obtain ⟨N₀, hN₀⟩ := hbound ξ hξ
  set δ_dirty := 2 * p - B_pair
  set A := (7 / 8) * B_pair + (1 / 8) * (2 * p)
  have hδ0 : 0 ≤ δ_dirty := by dsimp [δ_dirty]; linarith
  have hA_sub : 0 ≤ A - δ_dirty := by linarith
  let C₀ : ℝ := 3 * (max 1 N₀ : ℝ) + |A| + 1
  refine ⟨C₀, fun {n k σ I} hU2 Acc c => ?_⟩
  obtain ⟨Q, dirty, hsat, hdirty_sub, hgt1⟩ := exists_u2_saturated c hU2 (fun _ => Acc)
  set R := (hiddenNetwork c I fun _ => Acc).read.ncard
  have hfan : c.FanInAtMost 2 := hU2.fanInAtMost_two c
  have hR_le : R ≤ c.innerSize + 1 := by
    have h1 : R ≤ (network c I fun _ => Acc).read.ncard :=
      (Network.ncard_read_hide_le _).trans (Network.ncard_read_reindex _ _).le
    have h2 := cycleRank_add_ncard_read_le I (fun _ => Acc) hfan (connected c)
    omega
  have hblk_le_V : Nat.card Q.blocks ≤ Nat.card (Vertex c) := by
    refine Nat.card_le_card_of_injective (fun B : Q.blocks => B.1.head (Q.ne_nil B.1 B.2))
      fun B₁ B₂ h => Subtype.ext ?_
    dsimp only at h
    have hm : B₁.1.head (Q.ne_nil B₁.1 B₁.2) ∈ B₂.1 := h ▸ List.head_mem _
    exact Q.eq_of_mem B₁.1 B₁.2 B₂.1 B₂.2 _ (List.head_mem _) hm
  rcases le_or_gt (Nat.card Q.blocks) (max 1 N₀) with hsmall | hlarge
  · let score : Q.external → ℝ := fun _ => 0
    obtain ⟨pairLay, -⟩ :=
      Layout.exists_threshold (fun _ : Q.quotient.PairNode ∅ ∅ score => (0 : ℝ))
    refine ⟨U2PairData.mk Q hsat ∅ (fun ⟨_, h⟩ => h.elim) (fun _ h => h.elim)
      (fun _ h => h.elim) score pairLay, fun s_idx => ?_⟩
    dsimp only
    set P := Q.quotient.pairNodeVerts ∅ ∅ score (pairLay.initial s_idx)
    have hact0 : Q.quotient.activeCleanPairs ∅ ∅ score P = ∅ := by
      ext e; simp [Multigraph.activeCleanPairs]
    have hdegQ : Q.quotient.MaxDegreeLE 3 := fun B => by
      rw [Q.ncard_incidenceSet_quotient B]
      exact Q.ncard_edgeCut_le B.1 B.2
    have hcut_le : (Q.quotient.edgeCut P).ncard ≤ 3 * max 1 N₀ :=
      calc (Q.quotient.edgeCut P).ncard
          ≤ (Q.quotient.touching P).ncard := ncard_le_ncard (Q.quotient.edgeCut_subset_touching P)
        _ ≤ 3 * P.ncard := Q.quotient.ncard_touching_le hdegQ P
        _ ≤ 3 * Nat.card Q.blocks := Nat.mul_le_mul_left 3 (ncard_le_card P)
        _ ≤ 3 * max 1 N₀ := Nat.mul_le_mul_left 3 hsmall
    rw [hact0, ncard_empty, Nat.cast_zero, mul_zero, sub_zero]
    have hcutR : ((Q.quotient.edgeCut P).ncard : ℝ) ≤ 3 * (max 1 N₀ : ℝ) := by
      exact_mod_cast hcut_le
    have hRR : (R : ℝ) ≤ c.innerSize + 1 := by exact_mod_cast hR_le
    have hs0 : (0 : ℝ) ≤ c.innerSize := Nat.cast_nonneg _
    have hxi0 : 0 ≤ ξ * Nat.card (Vertex c) := by positivity
    have hA_abs : -|A| ≤ A := neg_abs_le A
    have hlow : -A ≤ A * c.innerSize - (A - δ_dirty) * R := by
      have hm := mul_le_mul_of_nonneg_left hRR hA_sub
      nlinarith
    dsimp only [C₀]
    linarith [le_abs_self A]
  · have htwo : 1 < Nat.card Q.blocks := (le_max_left 1 N₀).trans_lt hlarge
    have hN_lt : N₀ < Nat.card Q.blocks := (le_max_right 1 N₀).trans_lt hlarge
    obtain ⟨hclean3, hread_cnt, hdirty_cnt⟩ := hgt1 htwo
    have h3_all : ∀ B : Q.blocks, (Q.quotient.incidenceSet B).ncard = 3 :=
      hsat.ncard_incidenceSet_quotient (connected c) htwo
    obtain ⟨M_full, hM_full, hcov⟩ := Multigraph.exists_isMatching_mul_eight_ge Q.quotient
      Q.quotient_loopless hsat.injective_ends_quotient h3_all
    let M_clean : Set Q.external :=
      {e ∈ M_full | (Q.quotient.src e).1 ∉ dirty ∧ (Q.quotient.tgt e).1 ∉ dirty}
    have hM_clean : Q.quotient.IsMatching M_clean := fun _ h₁ _ h₂ => hM_full h₁.1 h₂.1
    have hclean_pair : ∀ e ∈ M_clean, CleanBlock3 I {v | v ∈ (Q.quotient.src e).1} ∧
        CleanBlock3 I {v | v ∈ (Q.quotient.tgt e).1} :=
      fun e he => ⟨hclean3 _ (Q.quotient.src e).2 he.2.1, hclean3 _ (Q.quotient.tgt e).2 he.2.2⟩
    have hdrop_le : M_full.ncard ≤ M_clean.ncard + dirty.card := by
      have := Fintype.ofFinite (Edge c)
      let M_drop : Set Q.external := M_full \ M_clean
      have hwit : ∀ e ∈ M_drop, ∃ b : dirty,
          (⟨b.1, hdirty_sub b.2⟩ : Q.blocks) = Q.quotient.src e ∨
            (⟨b.1, hdirty_sub b.2⟩ : Q.blocks) = Q.quotient.tgt e := by
        rintro e ⟨heM, hnot⟩
        by_cases hs : (Q.quotient.src e).1 ∈ dirty
        · exact ⟨⟨(Q.quotient.src e).1, hs⟩, Or.inl rfl⟩
        · have ht : (Q.quotient.tgt e).1 ∈ dirty :=
            by_contra fun ht => hnot ⟨heM, hs, ht⟩
          exact ⟨⟨(Q.quotient.tgt e).1, ht⟩, Or.inr rfl⟩
      choose b_of hb_end using fun e : M_drop => hwit e.1 e.2
      have hinj : Function.Injective b_of := by
        intro e₁ e₂ heq
        have hBeq : (⟨(b_of e₁).1, hdirty_sub (b_of e₁).2⟩ : Q.blocks) =
            ⟨(b_of e₂).1, hdirty_sub (b_of e₂).2⟩ := by rw [heq]
        by_contra hne
        have hmem₁ : (⟨(b_of e₁).1, hdirty_sub (b_of e₁).2⟩ : Q.blocks) ∈
            ({Q.quotient.src e₁.1, Q.quotient.tgt e₁.1} : Set Q.blocks) := by
          rcases hb_end e₁ with h | h <;> simp [h]
        have hmem₂ : (⟨(b_of e₁).1, hdirty_sub (b_of e₁).2⟩ : Q.blocks) ∈
            ({Q.quotient.src e₂.1, Q.quotient.tgt e₂.1} : Set Q.blocks) := by
          rw [hBeq]; rcases hb_end e₂ with h | h <;> simp [h]
        exact disjoint_left.mp (hM_full e₁.2.1 e₂.2.1 fun h => hne (Subtype.ext h))
          hmem₁ hmem₂
      have hcard_drop : (M_full \ M_clean).ncard ≤ dirty.card := by
        have h1 := Nat.card_le_card_of_injective b_of hinj
        rwa [Nat.card_coe_set_eq, Nat.card_eq_finsetCard] at h1
      have hpart := ncard_sdiff_add_ncard_of_subset (fun _ he => he.1 : M_clean ⊆ M_full)
      omega
    have hmv_le : (Q.quotient.matchedVertices M_full).ncard ≤ 2 * M_full.ncard := by
      have := Fintype.ofFinite (Edge c)
      have hsub : Q.quotient.matchedVertices M_full ⊆
          (Q.quotient.src '' M_full) ∪ (Q.quotient.tgt '' M_full) := by
        rintro B ⟨e, he, rfl | rfl⟩
        · exact Or.inl ⟨e, he, rfl⟩
        · exact Or.inr ⟨e, he, rfl⟩
      calc (Q.quotient.matchedVertices M_full).ncard
          ≤ ((Q.quotient.src '' M_full) ∪ (Q.quotient.tgt '' M_full)).ncard :=
            ncard_le_ncard hsub (toFinite _)
        _ ≤ (Q.quotient.src '' M_full).ncard + (Q.quotient.tgt '' M_full).ncard :=
            ncard_union_le _ _
        _ ≤ M_full.ncard + M_full.ncard :=
            Nat.add_le_add (ncard_image_le (toFinite _)) (ncard_image_le (toFinite _))
        _ = 2 * M_full.ncard := (two_mul _).symm
    obtain ⟨score, pairLay, hσ⟩ := hN₀ Q.blocks Q.external Q.quotient Q.quotient_loopless
      hsat.injective_ends_quotient h3_all hN_lt M_clean M_clean hM_clean (Subset.refl _)
    refine ⟨U2PairData.mk Q hsat M_clean (fun _ => h3_all) hM_clean hclean_pair score pairLay,
      fun s_idx => ?_⟩
    dsimp only
    refine (hσ s_idx).trans ?_
    have hcov_nat : 7 * Nat.card Q.blocks ≤ 16 * M_full.ncard := by omega
    have hcovR : 7 * (Nat.card Q.blocks : ℝ) ≤ 16 * (M_full.ncard : ℝ) := by exact_mod_cast hcov_nat
    have hdropR : (M_full.ncard : ℝ) ≤ (M_clean.ncard : ℝ) + (dirty.card : ℝ) := by
      exact_mod_cast hdrop_le
    have hreadR : (Nat.card Q.blocks : ℝ) + 2 * R ≤ 2 * c.innerSize := by exact_mod_cast hread_cnt
    have hdirtyR : (Nat.card Q.blocks : ℝ) + 2 * (dirty.card : ℝ) ≤ 2 * c.innerSize + 2 := by
      exact_mod_cast hdirty_cnt
    have hblkR : (Nat.card Q.blocks : ℝ) ≤ Nat.card (Vertex c) := by exact_mod_cast hblk_le_V
    set h : ℝ := (Nat.card Q.blocks : ℝ)
    set m : ℝ := (M_clean.ncard : ℝ)
    set d : ℝ := (dirty.card : ℝ)
    have hm_lo : (7 / 16) * h - d ≤ m := by linarith
    have hcost_eq : (h - 2 * m) * p + m * B_pair = h * p - m * δ_dirty := by
      dsimp only [δ_dirty]; ring
    have hm_mul := mul_le_mul_of_nonneg_right hm_lo hδ0
    have hp_id : p - (7 / 16) * δ_dirty = A / 2 := by
      dsimp only [A, δ_dirty]; ring
    have hsplit_id : (A / 2) * h + δ_dirty * d =
        ((A - δ_dirty) / 2) * h + (δ_dirty / 2) * (h + 2 * d) := by ring
    have hterm1 := mul_le_mul_of_nonneg_left (show h ≤ 2 * c.innerSize - 2 * R by linarith)
      (by linarith : 0 ≤ (A - δ_dirty) / 2)
    have hterm2 := mul_le_mul_of_nonneg_left hdirtyR (by linarith : 0 ≤ δ_dirty / 2)
    have hxi_le : ξ * h ≤ ξ * Nat.card (Vertex c) := mul_le_mul_of_nonneg_left hblkR hξ.le
    have hC0_ge : δ_dirty ≤ C₀ := by
      have hN0_pos : (0 : ℝ) ≤ max 1 (N₀ : ℝ) := by positivity
      dsimp only [C₀]; linarith [le_abs_self A, hN0_pos]
    have hid1 : h * p - (7 / 16 * h - d) * δ_dirty =
        (p - 7 / 16 * δ_dirty) * h + δ_dirty * d := by ring
    rw [hp_id] at hid1
    have hid2 : (A - δ_dirty) / 2 * (2 * (c.innerSize : ℝ) - 2 * R) +
        δ_dirty / 2 * (2 * (c.innerSize : ℝ) + 2) =
        A * c.innerSize - (A - δ_dirty) * R + δ_dirty := by ring
    linarith

/-- **Parametric `U₂` nondeterministic frontier lower bound.** Under `U2CubicPairBound p B_pair`
with `0 < p`, `0 < B_pair ≤ 2 p`, and `δ_dirty := 2 p - B_pair ≤ A := (7/8) B_pair + (1/8)(2p)`,
every nondeterministic circuit over a `U₂` basis deciding dense `K_n`-rectangle-free sets `S_n`
with any number `k` of witness inputs requires more than `(1 + (1 - δ_dirty) / A - ε) n` inner
gates. -/
theorem eventually_lt_innerSize_u2_nondeterministic {p B_pair : ℝ} (hp : 0 < p)
    (hBp : 0 < B_pair) (hBp_le : B_pair ≤ 2 * p) (hbound : U2CubicPairBound p B_pair)
    (hδA : 2 * p - B_pair ≤ (7 / 8) * B_pair + (1 / 8) * (2 * p))
    {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ (n + k) 1), I.IsU2 → c.NondeterministicDecides I Acc (S n) →
        (1 + (1 - (2 * p - B_pair)) / ((7 / 8) * B_pair + (1 / 8) * (2 * p)) - ε) * n <
          c.innerSize := by
  set δ_dirty := 2 * p - B_pair
  set A := (7 / 8) * B_pair + (1 / 8) * (2 * p)
  have hA : 0 < A := by dsimp [A]; positivity
  have hA_sub : 0 ≤ A - δ_dirty := by linarith
  set L_u2 := 1 + (1 - δ_dirty) / A
  set ε' := min ε (1 / A)
  have hε' : 0 < ε' := lt_min hε (by positivity)
  have hε'_le : ε' ≤ ε := min_le_left _ _
  have h1mAε : 0 ≤ 1 - A * ε' := by
    have : A * ε' ≤ A * (1 / A) := mul_le_mul_of_nonneg_left (min_le_right _ _) hA.le
    rw [mul_one_div_cancel hA.ne'] at this
    linarith
  set ξ := A * ε' / (8 * (4 * |L_u2| + 4))
  have hξ : 0 < ξ := by positivity
  obtain ⟨C₀, hData⟩ := exists_u2PairData_of_u2CubicPairBound.{v} hp hBp_le hbound hδA hξ
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcard_bool : (Nat.card Bool : ℝ) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_bool]; norm_num
  have hdef_o : (fun n : ℕ => (n : ℝ) - Real.logb 2 (S n).ncard) =o[atTop] fun n => (n : ℝ) := by
    refine (hSK.isLittleO_deficit.const_mul_left (1 / Real.log 2)).congr_left fun n => ?_
    rw [hcard_bool, Real.logb]
    field_simp
  have hK_o : (fun n : ℕ => (3 + A) * Real.logb 2 (K n)) =o[atTop] fun n => (n : ℝ) := by
    refine (hSK.isLittleO_log.const_mul_left ((3 + A) / Real.log 2)).congr_left fun n => ?_
    simp only [Real.logb]; ring
  have hV_o : (fun n : ℕ => (7 / Real.log 2) * Real.log (4 * |L_u2| * n + 4)) =o[atTop]
      fun n => (n : ℝ) :=
    (isLittleO_log_affine (by positivity) (by norm_num)).const_mul_left _
  have hconst_o : (fun _ : ℕ => 15 + |C₀| + 3 * ξ) =o[atTop] fun n => (n : ℝ) :=
    (isLittleO_const_id_atTop _).natCast_atTop
  have herr_o := ((hdef_o.add hK_o).add hV_o).add hconst_o
  filter_upwards [herr_o.bound (show 0 < A * ε' / 2 by positivity),
    hSK.eventually_rectangleFree, eventually_card_mul_sq_le_ncard hSK,
    eventually_ge_atTop 1] with n herr hfreen hbign hn1
  intro k σ I Acc c hU2 hdec
  suffices hlt : (L_u2 - ε') * n < c.innerSize by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (sub_le_sub_left hε'_le L_u2) (Nat.cast_nonneg n)) hlt
  by_contra! hle
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hs_nonneg : (0 : ℝ) ≤ c.innerSize := Nat.cast_nonneg _
  have hL_nonneg : 0 ≤ L_u2 - ε' := by nlinarith
  have hs_le_L : (c.innerSize : ℝ) ≤ |L_u2| * n :=
    hle.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self L_u2]) (Nat.cast_nonneg n))
  set N := hiddenNetwork c I fun _ => Acc
  have hacc_N : N.accepted = S n := by
    rw [accepted_hiddenNetwork]
    ext x; rw [hdec x]
    exact exists_congr fun y => ⟨fun h => h 0, fun h o => Subsingleton.elim o 0 ▸ h⟩
  have hfreen' : RectangleFree N.accepted (K n) := hacc_N ▸ hfreen
  have hbign' : Nat.card Bool * K n ^ 2 ≤ N.accepted.ncard := hacc_N ▸ hbign
  have hu_lt : Nat.card Bool ^ N.readᶜ.ncard < K n :=
    hfreen'.pow_ncard_compl_lt N.dependsOn_read hbign'
  rw [Nat.card_eq_fintype_card, Fintype.card_bool] at hu_lt hbign'
  have hK_pos : 1 ≤ K n := hfreen.pos
  have hS_pos : (0 : ℝ) < (S n).ncard := by
    have : 0 < 2 * K n ^ 2 := by positivity
    rw [← hacc_N]
    exact_mod_cast this.trans_le hbign'
  obtain ⟨D, hD⟩ := hData hU2 Acc c
  have hclean_N : ∀ v, IsCleanVertex v →
      (∀ x α, N.Constraint v x α ↔ Constraint I (fun _ => univ) v (fun _ => false) α) ∧
        N.readAt v = ∅ :=
    fun v hv => ⟨hidden_constraint_iff_of_isCleanVertex I _ hv,
      readAt_hidden_eq_empty_of_isCleanVertex I _ hv⟩
  have hm_N : ∀ v, (N.readAt v).ncard ≤ 1 := fun v =>
    (Network.ncard_readAt_hide_le _ v).trans
      ((Network.ncard_readAt_reindex _ _ v).trans_le (ncard_readAt_le I _ v))
  have hfan : c.FanInAtMost 2 := hU2.fanInAtMost_two c
  have hV_pos : 1 ≤ Nat.card (Vertex c) := by
    have : Nonempty (Vertex c) := ⟨.output 0⟩
    exact Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  set B_sup := A * c.innerSize - (A - δ_dirty) * N.read.ncard + ξ * Nat.card (Vertex c) + C₀
  have hmul_bp := D.mul_size_branchingProgram_le_rpow N hclean_N hV_pos
    (maxDegreeLE le_rfl hfan) hm_N hK_pos hu_lt.le hD
  have hrect_bp := (D.branchingProgram N).ncard_accepted_le (Nat.succ_pos _)
    (by rwa [D.accepted_branchingProgram N rfl hclean_N])
  rw [D.accepted_branchingProgram N rfl hclean_N, hacc_N] at hrect_bp
  have hS_le_rpow : ((S n).ncard : ℝ) ≤ (2 : ℝ) ^
      (max 0 B_sup + 15 + 3 * Real.logb 2 (K n) + 7 * Real.logb 2 (Nat.card (Vertex c))) :=
    (show ((S n).ncard : ℝ) ≤ _ by exact_mod_cast hrect_bp).trans hmul_bp
  have hlogS : Real.logb 2 (S n).ncard ≤
      max 0 B_sup + 15 + 3 * Real.logb 2 (K n) + 7 * Real.logb 2 (Nat.card (Vertex c)) := by
    have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hS_pos hS_le_rpow
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at this
  have hcompl_eq : (N.read.ncard : ℝ) + N.readᶜ.ncard = n := by
    rw [← Nat.cast_add, ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hunread_log : (N.readᶜ.ncard : ℝ) ≤ Real.logb 2 (K n) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hK_pos), Real.rpow_natCast]
    exact_mod_cast hu_lt.le
  have hR_lo : (n : ℝ) - Real.logb 2 (K n) ≤ N.read.ncard := by linarith
  have hmain_id : A * (L_u2 - ε') * n - (A - δ_dirty) * n = (1 - A * ε') * n := by
    dsimp only [L_u2]
    field_simp
    ring
  have hlogK0 : 0 ≤ Real.logb 2 (K n) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hK_pos)
  have hmax_le : max 0 B_sup ≤
      (1 - A * ε') * n + A * Real.logb 2 (K n) + ξ * Nat.card (Vertex c) + |C₀| := by
    refine max_le (by positivity) ?_
    have h1 := mul_le_mul_of_nonneg_left hle hA.le
    have h2 := mul_le_mul_of_nonneg_left hR_lo hA_sub
    have h3 : (A - δ_dirty) * Real.logb 2 (K n) ≤ A * Real.logb 2 (K n) :=
      mul_le_mul_of_nonneg_right (by linarith) hlogK0
    dsimp only [B_sup]
    linarith [le_abs_self C₀]
  have hV_le : (Nat.card (Vertex c) : ℝ) ≤ 4 * |L_u2| * n + 3 := by
    have h1 : Nat.card (Vertex c) ≤ 2 * 2 * c.innerSize + 3 * 1 := card_vertex_le hfan
    have h2 : (Nat.card (Vertex c) : ℝ) ≤ 4 * c.innerSize + 3 := by exact_mod_cast h1
    linarith
  have hxiV : ξ * Nat.card (Vertex c) ≤ (A * ε' / 8) * n + 3 * ξ := by
    have h1 := mul_le_mul_of_nonneg_left hV_le hξ.le
    have h2 : ξ * (4 * |L_u2|) ≤ A * ε' / 8 := by
      dsimp only [ξ]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_pos hA hε', abs_nonneg L_u2]
    have h3 := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg (α := ℝ) n)
    linarith
  have hV_arg : (Nat.card (Vertex c) : ℝ) ≤ 4 * |L_u2| * n + 4 := by linarith only [hV_le]
  have hlogV : 7 * Real.logb 2 (Nat.card (Vertex c)) ≤
      (7 / Real.log 2) * Real.log (4 * |L_u2| * n + 4) := by
    rw [Real.logb, div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast hV_pos) hV_arg)
        hlog2_pos.le)
      (by norm_num)
  simp only [Real.norm_eq_abs, Nat.abs_cast] at herr
  have herr' := (le_abs_self _).trans herr
  have hpos_margin : 0 < A * ε' * n := by positivity
  linarith only [hlogS, hmax_le, hxiV, hlogV, herr', hpos_margin]

/-- **Parametric `U₂` worst-case frontier lower bound.** Every deterministic circuit over a `U₂`
basis deciding dense `K_n`-rectangle-free sets `S_n` requires more than
`(1 + (1 - δ_dirty) / A - ε) n` inner gates. -/
theorem eventually_lt_innerSize_u2 {p B_pair : ℝ} (hp : 0 < p) (hBp : 0 < B_pair)
    (hBp_le : B_pair ≤ 2 * p) (hbound : U2CubicPairBound p B_pair)
    (hδA : 2 * p - B_pair ≤ (7 / 8) * B_pair + (1 / 8) * (2 * p))
    {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), I.IsU2 → c.Decides I Acc (S n) →
        (1 + (1 - (2 * p - B_pair)) / ((7 / 8) * B_pair + (1 / 8) * (2 * p)) - ε) * n <
          c.innerSize := by
  filter_upwards [eventually_lt_innerSize_u2_nondeterministic.{v} hp hBp hBp_le hbound hδA hSK
    hε] with n hn σ I Acc c hU2 hdec
  exact hn 0 σ I Acc c hU2 hdec.nondeterministicDecides

/-- **Parametric `U₂` average-case frontier lower bound.** Below `(1 + (1 - δ_dirty) / A - ε) n`
inner gates, every circuit over a `U₂` basis agrees with a family `S_n` of rectangle bias `b_n`
(`log K_n = o(n)`) on at most `1 / 2 + b_n + exp (-γ n)` of inputs. -/
theorem eventually_agreement_le_u2 {p B_pair : ℝ} (hp : 0 < p) (hBp : 0 < B_pair)
    (hBp_le : B_pair ≤ 2 * p) (hbound : U2CubicPairBound p B_pair)
    (hδA : 2 * p - B_pair ≤ (7 / 8) * B_pair + (1 / 8) * (2 * p))
    {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} {b : ℕ → ℝ}
    (hbias : ∀ᶠ n in atTop, RectangleBias (S n) (K n) (b n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), I.IsU2 →
        (c.innerSize : ℝ) ≤
          (1 + (1 - (2 * p - B_pair)) / ((7 / 8) * B_pair + (1 / 8) * (2 * p)) - ε) * n →
        agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b n + Real.exp (-(γ * n)) := by
  set δ_dirty := 2 * p - B_pair
  set A := (7 / 8) * B_pair + (1 / 8) * (2 * p)
  have hA : 0 < A := by dsimp [A]; positivity
  have hA_sub : 0 ≤ A - δ_dirty := by linarith
  set L_u2 := 1 + (1 - δ_dirty) / A
  set ε' := min ε (1 / A)
  have hε' : 0 < ε' := lt_min hε (by positivity)
  have hε'_le : ε' ≤ ε := min_le_left _ _
  have h1mAε : 0 ≤ 1 - A * ε' := by
    have : A * ε' ≤ A * (1 / A) := mul_le_mul_of_nonneg_left (min_le_right _ _) hA.le
    rw [mul_one_div_cancel hA.ne'] at this
    linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  set μ := min (A * ε' / 4) (1 / 4)
  have hμ : 0 < μ := lt_min (by positivity) (by norm_num)
  refine ⟨μ * Real.log 2, by positivity, ?_⟩
  set ξ := A * ε' / (8 * (4 * |L_u2| + 4))
  have hξ : 0 < ξ := by positivity
  obtain ⟨C₀, hData⟩ := exists_u2PairData_of_u2CubicPairBound.{v} hp hBp_le hbound hδA hξ
  set K' : ℕ → ℕ := fun n => max (K n) 2
  have hK'_log : (fun n : ℕ => Real.log (K' n)) =o[atTop] fun n => (n : ℝ) := by
    refine IsBigO.trans_isLittleO (g := fun n => ‖Real.log (K n)‖ + Real.log 2) ?_
      (hK.norm_left.add (isLittleO_const_id_atTop _).natCast_atTop)
    refine IsBigO.of_bound' (Eventually.of_forall fun n => ?_)
    have hK2 : (2 : ℝ) ≤ (K' n : ℕ) := by exact_mod_cast le_max_right (K n) 2
    rw [Real.norm_of_nonneg (Real.log_nonneg (by linarith)),
      Real.norm_of_nonneg (by positivity)]
    rcases le_total (K n) 2 with h | h
    · dsimp only [K']; rw [max_eq_right h]; push_cast; linarith [norm_nonneg (Real.log (K n))]
    · dsimp only [K']; rw [max_eq_left h]; linarith [Real.le_norm_self (Real.log (K n))]
  have hK'_logb : (fun n : ℕ => Real.logb 2 (K' n)) =o[atTop] fun n => (n : ℝ) :=
    (hK'_log.const_mul_left (1 / Real.log 2)).congr_left fun n => by simp only [Real.logb]; ring
  have hV_o : (fun n : ℕ => (7 / Real.log 2) * Real.log (4 * |L_u2| * n + 4)) =o[atTop]
      fun n => (n : ℝ) :=
    (isLittleO_log_affine (by positivity) (by norm_num)).const_mul_left _
  have hconst_o : (fun _ : ℕ => 15 + |C₀| + 3 * ξ) =o[atTop] fun n => (n : ℝ) :=
    (isLittleO_const_id_atTop _).natCast_atTop
  have herr_o := ((hK'_logb.const_mul_left (3 + A)).add hV_o).add hconst_o
  have hsmall_o : (fun n : ℕ => 2 + 2 * Real.logb 2 (K' n)) =o[atTop] fun n => (n : ℝ) :=
    (isLittleO_const_id_atTop _).natCast_atTop.add (hK'_logb.const_mul_left 2)
  filter_upwards [hbias, herr_o.bound (show 0 < A * ε' / 2 by positivity),
    hsmall_o.bound (by norm_num : (0 : ℝ) < 1 / 2), eventually_ge_atTop 1] with
    n hbiasn herr hsmalln hn1
  intro σ I Acc c hU2 hsize
  have hsize' : (c.innerSize : ℝ) ≤ (L_u2 - ε') * n :=
    hsize.trans (mul_le_mul_of_nonneg_right (sub_le_sub_left hε'_le L_u2) (Nat.cast_nonneg n))
  have hK2 : 2 ≤ K' n := le_max_right _ _
  have hK_posR : (0 : ℝ) < K' n := by exact_mod_cast (show 0 < K' n by omega)
  have hK_ge1R : (1 : ℝ) ≤ K' n := by exact_mod_cast (show 1 ≤ K' n by omega)
  have hS : RectangleBias (S n) (K' n) (b n) := hbiasn.mono (le_max_left _ _)
  simp only [Real.norm_eq_abs, Nat.abs_cast] at herr hsmalln
  have hsmalln' := (le_abs_self _).trans hsmalln
  have hb : 0 ≤ b n := hS.nonneg (by
    rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin,
      Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
    have hn2 : (n : ℝ) ≤ 2 * (n / 2 : ℕ) + 1 := by
      exact_mod_cast (show n ≤ 2 * (n / 2) + 1 by omega)
    have hlogb : Real.logb 2 (K' n) ≤ (n / 2 : ℕ) := by linarith
    have hr := (Real.logb_le_iff_le_rpow (by norm_num) hK_posR).mp hlogb
    rw [Real.rpow_natCast] at hr
    exact_mod_cast hr)
  by_cases hu : K' n ≤ Nat.card Bool ^ (network c I fun _ => Acc).readᶜ.ncard
  · have hunr := agreement_le_of_unread I Acc c hS hb (by omega) hu
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, Nat.cast_ofNat] at hunr
    have hres_le : ((2 * K' n ^ 2 : ℕ) : ℝ) / (2 : ℝ) ^ n ≤
        Real.exp (-((μ * Real.log 2) * n)) := by
      have hKr : ((2 * K' n ^ 2 : ℕ) : ℝ) = (2 : ℝ) ^ (1 + 2 * Real.logb 2 (K' n)) := by
        push_cast
        rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm 2 (Real.logb 2 (K' n)),
          Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hK_posR,
          Real.rpow_ofNat]
      rw [hKr, ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_sub (by norm_num),
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      refine Real.exp_le_exp.mpr ?_
      have hμn : μ * n ≤ (1 / 4) * n :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg n)
      have hexp_le : 1 + 2 * Real.logb 2 (K' n) - n ≤ -(μ * n) := by linarith
      have := mul_le_mul_of_nonneg_left hexp_le hlog2_pos.le
      linarith
    exact hunr.trans (add_le_add_right hres_le _)
  · push Not at hu
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hu
    obtain ⟨D, hD⟩ := hData (n := n) (k := 0) hU2 Acc c
    rw [read_hiddenNetwork_zero] at hD
    set R := (network c I fun _ => Acc).read.ncard
    set V := Nat.card (Vertex c)
    set B_sup := A * c.innerSize - (A - δ_dirty) * R + ξ * V + C₀
    have hfan : c.FanInAtMost 2 := hU2.fanInAtMost_two c
    have hV_pos : 1 ≤ V := by
      have : Nonempty (Vertex c) := ⟨.output 0⟩
      exact Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
    let R_res : ℝ :=
      (2 : ℝ) ^ (max 0 B_sup + 15 + 3 * Real.logb 2 (K' n) + 7 * Real.logb 2 V)
    have bound_acc (A_set : Set Bool) :
        |signedCount (S n) (network c I fun _ => A_set).accepted| ≤
          2 * b n * (network c I fun _ => A_set).accepted.ncard + R_res := by
      set N_A := network c I fun _ => A_set
      have hclean_A : ∀ v, IsCleanVertex v →
          (∀ x α, N_A.Constraint v x α ↔ Constraint I (fun _ => univ) v (fun _ => false) α) ∧
            N_A.readAt v = ∅ :=
        fun v hv =>
          ⟨constraint_iff_of_isCleanVertex I _ hv, readAt_eq_empty_of_isCleanVertex I _ hv⟩
      have hunamb := D.unambiguous_branchingProgram N_A rfl hclean_A fun _ _ _ => satisfies_unique
      have hpeel := (D.branchingProgram N_A).abs_signedCount_accepted_le hunamb (Nat.succ_pos _)
        hb hS
      rw [D.accepted_branchingProgram N_A rfl hclean_A] at hpeel
      have hread_eq : N_A.read = (network c I fun _ => Acc).read := rfl
      have hmul := D.mul_size_branchingProgram_le_rpow N_A hclean_A hV_pos
        (maxDegreeLE le_rfl hfan) (ncard_readAt_le I _) (K := K' n) (by omega)
        (by rw [hread_eq]; exact hu.le) hD
      exact hpeel.trans (by gcongr)
    have h₁ := bound_acc Acc
    have h₂ := bound_acc Accᶜ
    rw [accepted_network_eq_eval] at h₁
    have hacc_c : (network c I fun _ => Accᶜ).accepted = {x | c.eval I x 0 ∈ Acc}ᶜ := by
      rw [accepted_network_eq_eval]; rfl
    rw [hacc_c] at h₂
    have hagr := agreement_le h₁ h₂
    have hcard_in : (Nat.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin,
        Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
      push_cast; rfl
    rw [hcard_in, show (1 + 2 * b n) / 2 = 1 / 2 + b n by ring,
      show (R_res + R_res) / (2 * (2 : ℝ) ^ n) = R_res / (2 : ℝ) ^ n by field_simp; ring] at hagr
    -- Bound the exponent of `R_res / 2 ^ n` by `-(A * ε' / 4) * n`.
    have hs_nonneg : (0 : ℝ) ≤ c.innerSize := Nat.cast_nonneg _
    have hs_le_L : (c.innerSize : ℝ) ≤ |L_u2| * n :=
      hsize'.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self L_u2]) (Nat.cast_nonneg n))
    have hcompl_eq : (R : ℝ) + (network c I fun _ => Acc).readᶜ.ncard = n := by
      rw [← Nat.cast_add, ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hunread_log : ((network c I fun _ => Acc).readᶜ.ncard : ℝ) ≤ Real.logb 2 (K' n) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) hK_posR, Real.rpow_natCast]
      exact_mod_cast hu.le
    have hR_lo : (n : ℝ) - Real.logb 2 (K' n) ≤ R := by linarith
    have hmain_id : A * (L_u2 - ε') * n - (A - δ_dirty) * n = (1 - A * ε') * n := by
      dsimp only [L_u2]; field_simp; ring
    have hlogK0 : 0 ≤ Real.logb 2 (K' n) := Real.logb_nonneg (by norm_num) hK_ge1R
    have hmax_le : max 0 B_sup ≤
        (1 - A * ε') * n + A * Real.logb 2 (K' n) + ξ * V + |C₀| := by
      refine max_le (by positivity) ?_
      have h1 := mul_le_mul_of_nonneg_left hsize' hA.le
      have h2 := mul_le_mul_of_nonneg_left hR_lo hA_sub
      have h3 : (A - δ_dirty) * Real.logb 2 (K' n) ≤ A * Real.logb 2 (K' n) :=
        mul_le_mul_of_nonneg_right (by linarith) hlogK0
      dsimp only [B_sup]
      linarith [le_abs_self C₀]
    have hV_le : (V : ℝ) ≤ 4 * |L_u2| * n + 3 := by
      have h1 : V ≤ 2 * 2 * c.innerSize + 3 * 1 := card_vertex_le hfan
      have h2 : (V : ℝ) ≤ 4 * c.innerSize + 3 := by exact_mod_cast h1
      linarith
    have hxiV : ξ * V ≤ (A * ε' / 8) * n + 3 * ξ := by
      have h1 := mul_le_mul_of_nonneg_left hV_le hξ.le
      have h2 : ξ * (4 * |L_u2|) ≤ A * ε' / 8 := by
        dsimp only [ξ]
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [mul_pos hA hε', abs_nonneg L_u2]
      have h3 := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg (α := ℝ) n)
      linarith
    have hV_arg : (V : ℝ) ≤ 4 * |L_u2| * n + 4 := by linarith only [hV_le]
    have hlogV : 7 * Real.logb 2 V ≤ (7 / Real.log 2) * Real.log (4 * |L_u2| * n + 4) := by
      rw [Real.logb, div_mul_eq_mul_div, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast hV_pos) hV_arg)
          hlog2_pos.le)
        (by norm_num)
    have herr' := (le_abs_self _).trans herr
    have hexp_le : max 0 B_sup + 15 + 3 * Real.logb 2 (K' n) + 7 * Real.logb 2 V - n ≤
        -(μ * n) := by
      have hμ_le : μ * n ≤ (A * ε' / 4) * n :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n)
      have hmargin : (0 : ℝ) ≤ A * ε' * n := by positivity
      linarith only [hmax_le, hxiV, hlogV, herr', hμ_le, hmargin]
    have hratio : R_res / (2 : ℝ) ^ n ≤ Real.exp (-((μ * Real.log 2) * n)) := by
      dsimp only [R_res]
      rw [← Real.rpow_natCast (2 : ℝ), ← Real.rpow_sub (by norm_num),
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      refine Real.exp_le_exp.mpr ?_
      have := mul_le_mul_of_nonneg_left hexp_le hlog2_pos.le
      linarith only [this]
    exact hagr.trans (add_le_add_right hratio _)

/-- **Parametric `U₂` quadratic-form correlation bound.** Under `U2CubicPairBound p B_pair` with
`δ_dirty := 2 p - B_pair < 1` and `δ_dirty ≤ A := (7/8) B_pair + (1/8)(2p)`, set
`L_u2 = 1 + (1 - δ_dirty) / A` and `c* = 1 + (1/2 - δ_dirty) / A`. For every `c ≥ 1/2`, every
`γ < (c* - c) / (2 L_u2)`, and every family `Q_n` whose polar matrix has bisection cut rank
`⌊n/2⌋ - o(n)`, every `U₂` circuit with at most `c n` inner gates has correlation at most
`2^{-γ n}` with `BitString.quadForm (Q n)`. -/
theorem eventually_abs_correlation_quadForm_le_u2 {p B_pair c γ : ℝ} (hp : 0 < p)
    (hBp : 0 < B_pair) (hBp_le : B_pair ≤ 2 * p) (hbound : U2CubicPairBound p B_pair)
    (hδA : 2 * p - B_pair ≤ (7 / 8) * B_pair + (1 / 8) * (2 * p))
    (hδ1 : 2 * p - B_pair < 1) (hc : 1 / 2 ≤ c)
    (hγ : γ <
      (1 + (1 / 2 - (2 * p - B_pair)) / ((7 / 8) * B_pair + (1 / 8) * (2 * p)) - c) /
        (2 * (1 + (1 - (2 * p - B_pair)) / ((7 / 8) * B_pair + (1 / 8) * (2 * p)))))
    (Q : ∀ n, Matrix (Fin n) (Fin n) (ZMod 2)) (e : ℕ → ℝ)
    (he : e =o[atTop] fun n => (n : ℝ))
    (hQ : ∀ᶠ n in atTop, ∀ U : Set (Fin n), U.ncard = n / 2 →
      ((n / 2 : ℕ) : ℝ) ≤ (Q n + (Q n)ᵀ).cutRank U + e n) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (C : Circuit σ n 1), I.IsU2 → (C.innerSize : ℝ) ≤ c * n →
        |correlation {x | BitString.quadForm (Q n) x} {x | C.eval I x 0 ∈ Acc}| ≤
          (2 : ℝ) ^ (-γ * n) := by
  set δ_dirty := 2 * p - B_pair
  set A := (7 / 8) * B_pair + (1 / 8) * (2 * p)
  have hA : 0 < A := by dsimp [A]; positivity
  have hδ0 : 0 ≤ δ_dirty := by dsimp [δ_dirty]; linarith
  have hA_sub : 0 ≤ A - δ_dirty := by linarith
  set L_u2 := 1 + (1 - δ_dirty) / A
  set c_star := 1 + (1 / 2 - δ_dirty) / A
  have hL_pos : 0 < L_u2 := by
    have : 0 < (1 - δ_dirty) / A := div_pos (by linarith) hA
    dsimp [L_u2]; linarith
  set θ := (c_star - c) / L_u2
  have h2γ : 2 * γ < θ := by
    have : (c_star - c) / (2 * L_u2) = θ / 2 := by dsimp only [θ]; ring_nf
    linarith
  have hdenom_pos : 0 < A + 1 - δ_dirty := by linarith
  have hθ_alt : θ = (A + 1 / 2 - δ_dirty - A * c) / (A + 1 - δ_dirty) := by
    dsimp only [θ, c_star, L_u2]
    field_simp
    ring
  have hθ_bal : A * c - (A - δ_dirty) * (1 - θ) - 1 / 2 = -θ := by
    rw [hθ_alt]
    field_simp
    ring
  have hθ_half : θ ≤ 1 / 2 := by
    rw [hθ_alt, div_le_iff₀ hdenom_pos]
    nlinarith
  set Δ := θ - 2 * γ
  have hΔ : 0 < Δ := by dsimp [Δ]; linarith
  set ξ := Δ / (8 * (4 * c + 4))
  have hξ : 0 < ξ := by positivity
  obtain ⟨C₀, hData⟩ := exists_u2PairData_of_u2CubicPairBound.{v} hp hBp_le hbound hδA hξ
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hV_o : (fun n : ℕ => (6 / Real.log 2) * Real.log (4 * c * n + 4)) =o[atTop]
      fun n => (n : ℝ) :=
    (isLittleO_log_affine (by positivity) (by norm_num)).const_mul_left _
  have hconst_o : (fun _ : ℕ => |C₀| + 3 * ξ + 3 / 2) =o[atTop] fun n => (n : ℝ) :=
    (isLittleO_const_id_atTop _).natCast_atTop
  have herr_o := (he.norm_left.add hV_o).add hconst_o
  filter_upwards [hQ, herr_o.bound (show 0 < Δ / 2 by positivity), eventually_ge_atTop 1] with
    n hQn herr hn1
  intro σ I Acc C hU2 hsize
  simp only [Real.norm_eq_abs, Nat.abs_cast] at herr
  have herr' := (le_abs_self _).trans herr
  have he_le : e n ≤ |e n| := le_abs_self (e n)
  have hΔn : 0 ≤ Δ * n := by positivity
  apply abs_le_of_sq_le_sq _ (by positivity)
  have hsq_rhs : ((2 : ℝ) ^ (-γ * n)) ^ 2 = (2 : ℝ) ^ (-(2 * γ) * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    push_cast; ring_nf
  rw [hsq_rhs]
  set N₁ := network C I fun _ => Acc
  have hcompl : (N₁.readᶜ.ncard : ℝ) + N₁.read.ncard = n := by
    rw [← Nat.cast_add, add_comm, ncard_add_ncard_compl, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hhalf_le : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast Nat.div_mul_le_self n 2
  have hhalf_ge : (n : ℝ) / 2 - 1 / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show n ≤ 2 * (n / 2) + 1 by omega)
    linarith
  by_cases hd : θ * n ≤ N₁.readᶜ.ncard
  · refine (sq_correlation_quadForm_le_of_unread I Acc C (Q n) hQn
      (k := min N₁.readᶜ.ncard (n / 2)) (min_le_right _ _) (min_le_left _ _)).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have hθn_half : θ * n ≤ (n : ℝ) / 2 := by
      linarith [mul_le_mul_of_nonneg_right hθ_half (Nat.cast_nonneg (α := ℝ) n)]
    have hk : θ * n - 1 / 2 ≤ ((min N₁.readᶜ.ncard (n / 2) : ℕ) : ℝ) := by
      rcases min_choice N₁.readᶜ.ncard (n / 2) with h | h <;> rw [h] <;> linarith
    have hxi0 : 0 ≤ 3 * ξ + |C₀| := by positivity
    have hVlog0 : 0 ≤ (6 / Real.log 2) * Real.log (4 * c * n + 4) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) n]))
    have hΔ_eq : Δ * n = θ * n - 2 * γ * n := by dsimp only [Δ]; ring
    linarith only [hk, herr', he_le, hxi0, hVlog0, hΔn, hΔ_eq]
  · push Not at hd
    have hread_lo : (1 - θ) * n < N₁.read.ncard := by linarith
    have hread_half : n / 2 ≤ N₁.read.ncard := by
      have h1 : ((n / 2 : ℕ) : ℝ) < N₁.read.ncard := by
        have := mul_le_mul_of_nonneg_right hθ_half (Nat.cast_nonneg (α := ℝ) n)
        linarith
      exact_mod_cast h1.le
    obtain ⟨D, hD⟩ := hData (n := n) (k := 0) hU2 Acc C
    rw [read_hiddenNetwork_zero] at hD
    set B_sup := A * C.innerSize - (A - δ_dirty) * N₁.read.ncard + ξ * Nat.card (Vertex C) + C₀
    refine (D.sq_correlation_quadForm_le Acc (Q n) hQn hread_half hD).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have hfan : C.FanInAtMost 2 := hU2.fanInAtMost_two C
    have hV_pos : 1 ≤ Nat.card (Vertex C) := by
      have : Nonempty (Vertex C) := ⟨.output 0⟩
      exact Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
    have hV_le : (Nat.card (Vertex C) : ℝ) ≤ 4 * c * n + 3 := by
      have h1 : Nat.card (Vertex C) ≤ 2 * 2 * C.innerSize + 3 * 1 := card_vertex_le hfan
      have h2 : (Nat.card (Vertex C) : ℝ) ≤ 4 * C.innerSize + 3 := by exact_mod_cast h1
      linarith
    have hxiV : ξ * Nat.card (Vertex C) ≤ (Δ / 8) * n + 3 * ξ := by
      have h1 := mul_le_mul_of_nonneg_left hV_le hξ.le
      have h2 : ξ * (4 * c) ≤ Δ / 8 := by
        dsimp only [ξ]
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      have h3 := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg (α := ℝ) n)
      linarith
    have hV_arg : (Nat.card (Vertex C) : ℝ) ≤ 4 * c * n + 4 := by linarith only [hV_le]
    have hnatlog : 6 * (Nat.log 2 (Nat.card (Vertex C)) : ℝ) ≤
        (6 / Real.log 2) * Real.log (4 * c * n + 4) := by
      have h1 : (Nat.log 2 (Nat.card (Vertex C)) : ℝ) ≤ Real.logb 2 (Nat.card (Vertex C)) := by
        rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
        exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have h2 : Real.logb 2 (Nat.card (Vertex C)) ≤
          Real.log (4 * c * n + 4) / Real.log 2 :=
        div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast hV_pos) hV_arg)
          hlog2_pos.le
      rw [div_mul_eq_mul_div, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (h1.trans h2) (by norm_num)
    have hB_le : B_sup - (n : ℝ) / 2 ≤ -θ * n + ξ * Nat.card (Vertex C) + |C₀| := by
      have h1 := mul_le_mul_of_nonneg_left hsize hA.le
      have h2 := mul_le_mul_of_nonneg_left hread_lo.le hA_sub
      have hbal_n : (A * c - (A - δ_dirty) * (1 - θ) - 1 / 2) * n = -θ * n := by
        rw [hθ_bal]
      have hC0 := le_abs_self C₀
      dsimp only [B_sup]
      linarith only [h1, h2, hbal_n, hC0]
    have hΔ_eq : Δ * n = θ * n - 2 * γ * n := by dsimp only [Δ]; ring
    have hn0 : ((n + 0 : ℕ) : ℝ) = n := by push_cast; ring
    linarith only [hB_le, hxiV, hnatlog, herr', he_le, hΔn, hΔ_eq, hn0]

end Cslib.Circuits.Frontier
