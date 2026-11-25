/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.CappedCompression
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Carving.Coefficient
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Carving.Decompositions
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Carving.OffMedian
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import CslibFrontier.Foundations.Probability.Gaussian.Real
import CslibFrontier.Foundations.Probability.UnionBound
import CslibFrontier.Foundations.Probability.WeightedSecondMoment
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Carving-width and branchwidth of cubic multigraphs below Gaspers' `c₃`

Every linear layout of a cubic multigraph `G` is a caterpillar carving decomposition, so
`G.carvingWidth ≤ G.cutwidth` (assuming `|V| ≥ 2`). Whereas any linear layout must sweep across the
 balanced cut on a path—forcing Gaspers' switched Gaussian layout to pay
`c₃ = (3 / (4π)) arccos (5 / 6) ≈ 0.139822` per vertex—a binary carving tree can place its top split
*away* from the median (`t₀ < 0`) and bisect the two resulting subgraphs independently along
distinct tree branches.

1. **Level-zero off-median cut and greedy `1`-vertex flips.** At a single threshold
   `t₀ ∈ [-3 / 10, 0]`, define `A₀ = {v | 2 ≤ #{e ∈ inc(v) | score e < t₀}}` and `R₀ = A₀ᶜ`.
   Without any grid windows, charging low cross-edges outside `A₀` and high cross-edges inside `A₀`
   gives `|G.edgeCut A₀| ≤ #{v | G.EdgeStraddles score t₀ v}`
   (`≤ (exp (-t₀^2 / 2) p + o(1)) |V|`), while the exact half-edge identity
   `2 E_{< t₀} + k₂ = 3 |A₀| + k₁` cancels the off-median vertex excess in the Lyapunov potential
   `Φ_p(S) = p |S| + (1 / 2 - p) |G.edgeCut S|`, bounding both `Φ_p(A₀)` and `Φ_p(R₀)` by
   `(carvingAt t₀ + o(1)) |V|`. Greedy `1`-vertex flips eliminate all vertices with `≥ 2` cut edges
   on their side while decreasing both `|G.edgeCut A|` and `Φ_p` on both sides, leaving `A*` and
   `R*` whose induced subgraphs have minimum degree at least `2`.
2. **Depth-one `CappedCompression` symmetric bisection.** On each `X ∈ {A*, R*}`, compress
   `H = G.induce X` with vertex weights `w(x) = 1 + |inc_G(x) ∩ ∂X| ≤ 2` and weight cap `M`. By
   `CappedCompression.card_deg_three_add_le_of_two_le_deg`, `#Q₃ ≤ |X| - |∂X| + O(|V| / M)`. A
   symmetric (`t = 0`) Gaussian cut on `Q₃` paired with independent fair signs on low-degree blocks
   puts every block on each side with probability `1 / 2`, concentrating via
   `WeightedSecondMoment` to bisect `X = X₁ ⊔ X₂` with `|X_i| ≤ 0.46 |V|` and
   `|G.edgeCut X_i| ≤ Φ_p(X) + o(|V|) ≤ (carvingAt t₀ + o(1)) |V|`.
3. **Depths two through five and leaf peeling.** Four rounds of symmetric (`t = 0`) Gaussian
   bisections on `G` halve piece sizes below `0.03 |V|` while keeping every cut below
   `(carvingAt t₀ + o(1)) |V|`, after which `BinTree.ofSet` peels individual vertices with cuts at
   most `3 · 0.03 |V| < carvingAt t₀ · |V|`. Combining with `Multigraph.branchwidth_le_carvingWidth`
   yields `G.branchwidth ≤ G.carvingWidth ≤ (carvingCoefficient + ξ) |V| ≤ (0.137432 + ξ) |V|`.

## Main results

* `Cslib.Circuits.Frontier.Carving.exists_carvingWidth_le_carvingAt`: parametric carving-width bound
  `(carvingAt t₀ + ξ) |V|` for `t₀ ∈ [-3 / 10, 0]`.
* `Cslib.Circuits.Frontier.Carving.exists_carvingWidth_le_carvingCoefficient`: asymptotic
  carving-width bound `(carvingCoefficient + ξ) |V|` on loopless cubic multigraphs.
* `Cslib.Circuits.Frontier.Carving.exists_carvingWidth_le_137432`: explicit rational carving-width
  bound `(137432 / 1000000 + ξ) |V|`.
* `Cslib.Circuits.Frontier.Carving.exists_branchwidth_le_carvingCoefficient`,
  `Cslib.Circuits.Frontier.Carving.exists_branchwidth_le_137432`: corresponding branchwidth bounds.
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace Cslib.Circuits.Frontier.Carving

open Cslib.Circuits.Frontier.Gaussian Cslib.Circuits.Frontier.Multigraph

/-! ### Single-threshold cuts and the exact half-edge identity -/

section SingleThreshold

variable {V E : Type*}

/-- Vertices with at least two incident edges scoring strictly below `t`. -/
private def lowSide (G : Multigraph V E) (score : E → ℝ) (t : ℝ) : Set V :=
  {v : V | 2 ≤ {e ∈ G.incidenceSet v | score e < t}.ncard}

/-- At a degree-`3` vertex `v`, the counts of incident edges `< t` and `≥ t` sum to `3`. -/
private theorem ncard_lt_add_ncard_ge [Finite E] {G : Multigraph V E} {v : V}
    (hv : (G.incidenceSet v).ncard = 3) (score : E → ℝ) (t : ℝ) :
    {e ∈ G.incidenceSet v | score e < t}.ncard +
      {e ∈ G.incidenceSet v | t ≤ score e}.ncard = 3 := by
  classical
  have := Fintype.ofFinite E
  set s := (G.incidenceSet v).toFinset
  have hs : s.card = 3 := by rw [← Set.ncard_eq_toFinset_card', hv]
  have h1 : {e ∈ G.incidenceSet v | score e < t}.ncard = (s.filter (score · < t)).card := by
    rw [← ncard_coe_finset]
    congr 1; ext e; simp [s]
  have h2 : {e ∈ G.incidenceSet v | t ≤ score e}.ncard = (s.filter (¬score · < t)).card := by
    rw [← ncard_coe_finset]
    congr 1; ext e; simp [s, not_lt]
  rw [h1, h2, Finset.card_filter_add_card_filter_not, hs]

/-- At a degree-`3` vertex `v`, `G.EdgeStraddles score t v` iff `1 ≤ #{< t} ≤ 2`. -/
private theorem edgeStraddles_iff_ncard [Finite E] {G : Multigraph V E} {v : V}
    (hv : (G.incidenceSet v).ncard = 3) (score : E → ℝ) (t : ℝ) :
    G.EdgeStraddles score t v ↔
      1 ≤ {e ∈ G.incidenceSet v | score e < t}.ncard ∧
        {e ∈ G.incidenceSet v | score e < t}.ncard ≤ 2 := by
  have hsum := ncard_lt_add_ncard_ge hv score t
  constructor
  · rintro ⟨⟨e, he, hlt⟩, ⟨e', he', hge⟩⟩
    have h1 : 1 ≤ {f ∈ G.incidenceSet v | score f < t}.ncard :=
      (ncard_pos (toFinite _)).mpr ⟨e, he, hlt⟩
    have h2 : 1 ≤ {f ∈ G.incidenceSet v | t ≤ score f}.ncard :=
      (ncard_pos (toFinite _)).mpr ⟨e', he', hge⟩
    omega
  · rintro ⟨h1, h2⟩
    obtain ⟨e, he, hlt⟩ := (ncard_pos (toFinite _)).mp
      (by omega : 0 < {f ∈ G.incidenceSet v | score f < t}.ncard)
    obtain ⟨e', he', hge⟩ := (ncard_pos (toFinite _)).mp
      (by omega : 0 < {f ∈ G.incidenceSet v | t ≤ score f}.ncard)
    exact ⟨⟨e, he, hlt⟩, ⟨e', he', hge⟩⟩

/-- Every edge in `G.edgeCut Y` has a canonical endpoint inside `Y`. -/
private noncomputable def endIn (G : Multigraph V E) (Y : Set V) (e : E) : V :=
  open Classical in
  if G.src e ∈ Y then G.src e else G.tgt e

/-- For `e ∈ G.edgeCut Y`, `endIn G Y e` is the unique endpoint of `e` lying in `Y`. -/
private theorem endIn_mem {G : Multigraph V E} {Y : Set V} {e : E} (he : e ∈ G.edgeCut Y) :
    endIn G Y e ∈ Y ∧ e ∈ G.incidenceSet (endIn G Y e) ∧
      (∀ v ∈ Y, e ∈ G.incidenceSet v → v = endIn G Y e) := by
  rw [mem_edgeCut] at he
  dsimp only [endIn]
  split_ifs with hs
  · refine ⟨hs, Or.inl rfl, fun v hv hvinc => ?_⟩
    rcases hvinc with rfl | rfl
    · rfl
    · exfalso; exact he (iff_of_true hs hv)
  · have ht : G.tgt e ∈ Y := by tauto
    refine ⟨ht, Or.inr rfl, fun v hv hvinc => ?_⟩
    rcases hvinc with rfl | rfl
    · exfalso; exact hs hv
    · rfl

/-- Inject cut edges satisfying a predicate `p` into their `T`-endpoints whenever every vertex in
`D ∩ T` has at most one incident edge satisfying `p`. -/
private theorem ncard_edgeCut_inter_le_of_ncard_le_one [Finite V] [Finite E] {G : Multigraph V E}
    {D T : Set V} (p : E → Prop)
    (hle : ∀ v ∈ D, v ∈ T → {f ∈ G.incidenceSet v | p f}.ncard ≤ 1) :
    {e ∈ G.edgeCut T | G.src e ∈ D ∧ G.tgt e ∈ D ∧ p e}.ncard ≤
      {v ∈ D | v ∈ T ∧ 1 ≤ {f ∈ G.incidenceSet v | p f}.ncard}.ncard := by
  refine ncard_le_ncard_of_injOn (endIn G T) ?_ ?_ (toFinite _)
  · rintro e ⟨he, hsD, htD, hp⟩
    obtain ⟨hwT, hwinc, _⟩ := endIn_mem he
    have hwD : endIn G T e ∈ D := by
      rcases hwinc with h | h <;> rw [← h] <;> assumption
    exact ⟨hwD, hwT, (ncard_pos (toFinite _)).mpr ⟨e, hwinc, hp⟩⟩
  · rintro e₁ ⟨he₁, hs₁, ht₁, hp₁⟩ e₂ ⟨he₂, -, -, hp₂⟩ heq
    obtain ⟨hwT, hwinc₁, _⟩ := endIn_mem he₁
    have hwD : endIn G T e₁ ∈ D := by
      rcases hwinc₁ with h | h <;> rw [← h] <;> assumption
    have hwinc₂ : e₂ ∈ G.incidenceSet (endIn G T e₁) := by
      rw [heq]; exact (endIn_mem he₂).2.1
    exact (ncard_le_one (toFinite _)).mp (hle _ hwD hwT) _ ⟨hwinc₁, hp₁⟩ _ ⟨hwinc₂, hp₂⟩

/-- **Restricted single-threshold cut-to-straddle injection.** Let `D : Set V` consist of vertices
of degree `3` in `G`, and let `S : Set V` agree with `lowSide G score t` on `D`. Every cut edge of
`S` with both endpoints in `D` maps injectively to a straddling endpoint in `D \ S` (if
`score e < t`) or in `D ∩ S` (if `t ≤ score e`). -/
private theorem ncard_edgeCut_inter_le_straddles [Finite V] [Finite E] {G : Multigraph V E}
    {D S : Set V} (hD : ∀ v ∈ D, (G.incidenceSet v).ncard = 3) (score : E → ℝ) (t : ℝ)
    (hS : ∀ v ∈ D, v ∈ S ↔ v ∈ lowSide G score t) :
    {e ∈ G.edgeCut S | G.src e ∈ D ∧ G.tgt e ∈ D}.ncard ≤
      {v ∈ D | v ∉ S ∧ G.EdgeStraddles score t v}.ncard +
        {v ∈ D | v ∈ S ∧ G.EdgeStraddles score t v}.ncard := by
  set Ec := {e ∈ G.edgeCut S | G.src e ∈ D ∧ G.tgt e ∈ D}
  have hpart : Ec ⊆ {e ∈ G.edgeCut Sᶜ | G.src e ∈ D ∧ G.tgt e ∈ D ∧ score e < t} ∪
      {e ∈ G.edgeCut S | G.src e ∈ D ∧ G.tgt e ∈ D ∧ t ≤ score e} := by
    intro e ⟨he, hsD, htD⟩
    rcases lt_or_ge (score e) t with h | h
    · exact Or.inl ⟨by rwa [G.edgeCut_compl], hsD, htD, h⟩
    · exact Or.inr ⟨he, hsD, htD, h⟩
  have hlo : ∀ v ∈ D, v ∈ Sᶜ → {f ∈ G.incidenceSet v | score f < t}.ncard ≤ 1 := fun v hv hns => by
    have hlt := mt (hS v hv).mpr hns
    simp only [lowSide, mem_ofPred_eq, not_le] at hlt
    omega
  have hhi : ∀ v ∈ D, v ∈ S → {f ∈ G.incidenceSet v | t ≤ score f}.ncard ≤ 1 := fun v hv hs => by
    have hsum := ncard_lt_add_ncard_ge (hD v hv) score t
    have hge2 : 2 ≤ {f ∈ G.incidenceSet v | score f < t}.ncard := (hS v hv).mp hs
    omega
  refine ((ncard_le_ncard hpart (toFinite _)).trans (ncard_union_le _ _)).trans
    (Nat.add_le_add ?_ ?_)
  · refine (ncard_edgeCut_inter_le_of_ncard_le_one (fun e => score e < t) hlo).trans
      (ncard_le_ncard (fun v ⟨hv, hns, hpos⟩ => ?_) (toFinite _))
    exact ⟨hv, hns, (edgeStraddles_iff_ncard (hD v hv) score t).mpr
      ⟨hpos, (hlo v hv hns).trans (by decide)⟩⟩
  · refine (ncard_edgeCut_inter_le_of_ncard_le_one (fun e => t ≤ score e) hhi).trans
      (ncard_le_ncard (fun v ⟨hv, hs, hpos⟩ => ?_) (toFinite _))
    have hsum := ncard_lt_add_ncard_ge (hD v hv) score t
    have hge2 : 2 ≤ {f ∈ G.incidenceSet v | score f < t}.ncard := (hS v hv).mp hs
    exact ⟨hv, hs, (edgeStraddles_iff_ncard (hD v hv) score t).mpr ⟨by omega, by omega⟩⟩

/-- Combined form of `ncard_edgeCut_inter_le_straddles`: cut edges with both endpoints in `D` are
at most the number of straddling vertices in `D`. -/
private theorem ncard_edgeCut_inter_le_straddling [Finite V] [Finite E] {G : Multigraph V E}
    {D S : Set V} (hD : ∀ v ∈ D, (G.incidenceSet v).ncard = 3) (score : E → ℝ) (t : ℝ)
    (hS : ∀ v ∈ D, v ∈ S ↔ v ∈ lowSide G score t) :
    {e ∈ G.edgeCut S | G.src e ∈ D ∧ G.tgt e ∈ D}.ncard ≤
      {v ∈ D | G.EdgeStraddles score t v}.ncard := by
  have hdisj : Disjoint
      {v ∈ D | v ∉ S ∧ G.EdgeStraddles score t v}
      {v ∈ D | v ∈ S ∧ G.EdgeStraddles score t v} :=
    disjoint_left.mpr fun _ h1 h2 => h1.2.1 h2.2.1
  refine (ncard_edgeCut_inter_le_straddles hD score t hS).trans ?_
  rw [← ncard_union_eq hdisj (toFinite _) (toFinite _)]
  exact ncard_le_ncard (by rintro _ (h | h) <;> exact ⟨h.1, h.2.2⟩) (toFinite _)

/-- **Zero-window single-threshold cut bound.** On a cubic multigraph, the cut of
`lowSide G score t` is at most the number of vertices straddling `t`. -/
private theorem ncard_edgeCut_lowSide_le [Finite V] [Finite E] {G : Multigraph V E}
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (score : E → ℝ) (t : ℝ) :
    (G.edgeCut (lowSide G score t)).ncard ≤
      {v : V | v ∉ lowSide G score t ∧ G.EdgeStraddles score t v}.ncard +
        {v : V | v ∈ lowSide G score t ∧ G.EdgeStraddles score t v}.ncard := by
  simpa using ncard_edgeCut_inter_le_straddles (D := univ) (S := lowSide G score t)
    (fun v _ => h3 v) score t (fun _ _ => Iff.rfl)

/-- Disjoint partition of straddling vertices across any set `P`. -/
private theorem ncard_straddle_split [Finite V] {G : Multigraph V E} (P : Set V)
    (score : E → ℝ) (t : ℝ) :
    {v : V | v ∉ P ∧ G.EdgeStraddles score t v}.ncard +
      {v : V | v ∈ P ∧ G.EdgeStraddles score t v}.ncard =
        {v : V | G.EdgeStraddles score t v}.ncard := by
  have hd : Disjoint {v : V | v ∉ P ∧ G.EdgeStraddles score t v}
      {v : V | v ∈ P ∧ G.EdgeStraddles score t v} :=
    disjoint_left.mpr fun _ h1 h2 => h1.1 h2.1
  rw [← ncard_union_eq hd (toFinite _) (toFinite _)]
  congr 1
  ext v
  simp only [mem_union, mem_ofPred_eq]
  tauto

/-- **Exact half-edge identity at threshold `t`.** On a loopless cubic multigraph,
`2 * #{e | score e < t} + #{v ∈ lowSide | straddles t}` equals
`3 * |lowSide| + #{v ∉ lowSide | straddles t}`. -/
private theorem two_mul_ncard_score_lt_eq [Finite V] [Finite E] {G : Multigraph V E}
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (score : E → ℝ) (t : ℝ) :
    2 * {e : E | score e < t}.ncard +
        {v : V | v ∈ lowSide G score t ∧ G.EdgeStraddles score t v}.ncard =
      3 * (lowSide G score t).ncard +
        {v : V | v ∉ lowSide G score t ∧ G.EdgeStraddles score t v}.ncard := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  set P := lowSide G score t
  have hpt (v : V) :
      {e ∈ G.incidenceSet v | score e < t}.ncard +
        (if v ∈ P ∧ G.EdgeStraddles score t v then 1 else 0) =
      3 * (if v ∈ P then 1 else 0) +
        (if v ∉ P ∧ G.EdgeStraddles score t v then 1 else 0) := by
    have hiff := edgeStraddles_iff_ncard (h3 v) score t
    have hsub : {e ∈ G.incidenceSet v | score e < t} ⊆ G.incidenceSet v := fun _ h => h.1
    have hle3 : {e ∈ G.incidenceSet v | score e < t}.ncard ≤ 3 :=
      (ncard_le_ncard hsub (toFinite _)).trans_eq (h3 v)
    simp only [P, lowSide, mem_ofPred_eq, hiff]
    interval_cases {e ∈ G.incidenceSet v | score e < t}.ncard <;> simp
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset V)) rfl fun v _ => hpt v
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hcard (q : V → Prop) [DecidablePred q] :
      (∑ v : V, if q v then 1 else 0) = {v : V | q v}.ncard := by
    rw [← Finset.card_filter, ← ncard_coe_finset]
    congr 1; ext v; simp
  rw [hcard, hcard, hcard] at hsum
  simp only [ofPred_mem_eq] at hsum
  have hdouble : (∑ v : V, {e ∈ G.incidenceSet v | score e < t}.ncard) =
      2 * {e : E | score e < t}.ncard := by
    have h1 (v : V) : {e ∈ G.incidenceSet v | score e < t}.ncard =
        (Finset.univ.filter fun e : E => (G.src e = v ∨ G.tgt e = v) ∧ score e < t).card := by
      rw [← ncard_coe_finset]
      congr 1; ext e; simp [mem_incidenceSet]
    simp_rw [h1, Finset.card_filter]
    rw [Finset.sum_comm]
    have h2 (e : E) : (∑ x : V, if (G.src e = x ∨ G.tgt e = x) ∧ score e < t then 1 else 0) =
        if score e < t then 2 else 0 := by
      by_cases he : score e < t
      · simp only [he, and_true, ↓reduceIte, ← Finset.card_filter]
        have hpair : (Finset.univ.filter fun x : V => G.src e = x ∨ G.tgt e = x) =
            {G.src e, G.tgt e} := by
          ext x; simp [eq_comm]
        rw [hpair, Finset.card_pair (hloop e)]
      · simp [he]
    simp_rw [h2]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
      Nat.mul_comm]
    congr 1
    rw [← ncard_coe_finset]
    congr 1; ext e; simp
  omega

/-- Handshaking lemma on a finite loopless cubic multigraph: `2 * |E| = 3 * |V|`. -/
private theorem two_mul_card_edges_eq_cubic [Finite V] [Finite E] {G : Multigraph V E}
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3) :
    2 * Nat.card E = 3 * Nat.card V := by
  have := Fintype.ofFinite V
  have hsum := G.sum_ncard_incidenceSet hloop
  simp only [h3, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card] at hsum
  omega

end SingleThreshold

/-! ### Lyapunov potential and greedy `1`-vertex flips -/

section GreedyFlips

variable {V E : Type*}

/-- The depth-one Lyapunov potential `μ * |S| + (1 / 2 - μ) * |G.edgeCut S|`. -/
private noncomputable def lyap (μ : ℝ) (G : Multigraph V E) (S : Set V) : ℝ :=
  μ * (S.ncard : ℝ) + (1 / 2 - μ) * ((G.edgeCut S).ncard : ℝ)

/-- Moving a vertex `v ∉ A` into `A` changes `G.edgeCut` according to
`|∂(insert v A)| + 2 |inc(v) ∩ ∂A| = 3 + |∂A|`. -/
private theorem ncard_edgeCut_insert_add [Finite E] {G : Multigraph V E} (hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) {A : Set V} {v : V} (hv : v ∉ A) :
    (G.edgeCut (insert v A)).ncard + 2 * (G.incidenceSet v ∩ G.edgeCut A).ncard =
      3 + (G.edgeCut A).ncard := by
  have hdisj : Disjoint ({v} : Set V) A := disjoint_singleton_left.mpr hv
  have hu := G.ncard_edgeCut_union_add hdisj (toFinite _) (toFinite _)
  rw [singleton_union, G.edgeCut_singleton hloop v, h3 v] at hu
  exact hu

/-- **Greedy `1`-vertex flips.** Starting from any subset `A₀` of a finite loopless cubic
multigraph `G` and any `μ ≤ 3 / 20`, repeatedly moving vertices with at least two incident cut
edges to the opposite side yields `A*` such that both `A*` and `A*ᶜ` have at most one cut edge per
vertex, without increasing `|G.edgeCut|`, `lyap μ G`, or `|X| + |G.edgeCut X|` on either side. -/
private theorem exists_greedy_flipped [Finite V] [Finite E] {G : Multigraph V E}
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3) {μ : ℝ}
    (hμ : μ ≤ 3 / 20) (A₀ : Set V) :
    ∃ A : Set V,
      (G.edgeCut A).ncard ≤ (G.edgeCut A₀).ncard ∧
      lyap μ G A ≤ lyap μ G A₀ ∧
      lyap μ G Aᶜ ≤ lyap μ G A₀ᶜ ∧
      A.ncard + (G.edgeCut A).ncard ≤ A₀.ncard + (G.edgeCut A₀).ncard ∧
      (Aᶜ).ncard + (G.edgeCut A).ncard ≤ (A₀ᶜ).ncard + (G.edgeCut A₀).ncard ∧
      (∀ v ∈ A, (G.incidenceSet v ∩ G.edgeCut A).ncard ≤ 1) ∧
      (∀ v ∈ Aᶜ, (G.incidenceSet v ∩ G.edgeCut A).ncard ≤ 1) := by
  -- `Le T S`: `T` is no worse than `S` in each of the five tracked quantities.
  let Le (T S : Set V) : Prop :=
    (G.edgeCut T).ncard ≤ (G.edgeCut S).ncard ∧ lyap μ G T ≤ lyap μ G S ∧
      lyap μ G Tᶜ ≤ lyap μ G Sᶜ ∧ T.ncard + (G.edgeCut T).ncard ≤ S.ncard + (G.edgeCut S).ncard ∧
      (Tᶜ).ncard + (G.edgeCut T).ncard ≤ (Sᶜ).ncard + (G.edgeCut S).ncard
  have le_compl {S T : Set V} (h : Le T S) : Le Tᶜ Sᶜ := by
    simp only [Le, compl_compl, G.edgeCut_compl]
    exact ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩
  obtain ⟨A, hA, hmin⟩ := (measure fun S : Set V => (G.edgeCut S).ncard).wf.has_min
    {S | Le S A₀} ⟨A₀, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  have hno {T : Set V} (hT : Le T A) (hlt : (G.edgeCut T).ncard < (G.edgeCut A).ncard) : False :=
    hmin T ⟨hT.1.trans hA.1, hT.2.1.trans hA.2.1, hT.2.2.1.trans hA.2.2.1,
      hT.2.2.2.1.trans hA.2.2.2.1, hT.2.2.2.2.trans hA.2.2.2.2⟩ hlt
  -- Flipping `v ∉ S` into `S` when `2 ≤ |inc(v) ∩ ∂S|` strictly decreases the cut, keeping `Le`.
  have step_insert {S : Set V} {v : V} (hv : v ∉ S)
      (h2 : 2 ≤ (G.incidenceSet v ∩ G.edgeCut S).ncard) :
      (G.edgeCut (insert v S)).ncard < (G.edgeCut S).ncard ∧ Le (insert v S) S := by
    have hcut := ncard_edgeCut_insert_add hloop h3 hv
    have hins : (insert v S).ncard = S.ncard + 1 := ncard_insert_of_notMem hv (toFinite S)
    have hcompl : (Sᶜ).ncard = ((insert v S)ᶜ).ncard + 1 := by
      rw [← ncard_insert_of_notMem (show v ∉ (insert v S)ᶜ by simp) (toFinite _)]
      congr 1; ext x; by_cases hx : x = v <;> simp [hx, hv]
    have hlt : ((G.edgeCut (insert v S)).ncard : ℝ) + 1 ≤ (G.edgeCut S).ncard := by
      exact_mod_cast (by omega : (G.edgeCut (insert v S)).ncard + 1 ≤ (G.edgeCut S).ncard)
    refine ⟨by omega, by omega, ?_, ?_, by omega, by omega⟩ <;>
      simp only [lyap, G.edgeCut_compl, hins, hcompl, Nat.cast_add, Nat.cast_one] <;> nlinarith
  refine ⟨A, hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2, fun v hv => ?_, fun v hv => ?_⟩ <;>
    by_contra hgt
  · obtain ⟨hlt, hle⟩ :=
      step_insert (S := Aᶜ) (v := v) (by simpa using hv) (by rw [G.edgeCut_compl]; omega)
    rw [G.edgeCut_compl] at hlt
    exact hno (by simpa only [compl_compl] using le_compl hle) (by rwa [G.edgeCut_compl])
  · obtain ⟨hlt, hle⟩ := step_insert hv (by omega)
    exact hno hle hlt

end GreedyFlips

/-! ### Gaussian projection symmetry and induced boundary identities -/

section Helpers

/-- Under `Measure.pi (gaussianReal 0 1)`, a unit inner-product projection has law
`gaussianReal 0 1`. -/
private theorem pi_gaussianReal_map_inner_unit {ι : Type*} [Fintype ι] {u : EuclideanSpace ℝ ι}
    (hu : ‖u‖ = 1) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun ω => ⟪u, WithLp.toLp 2 ω⟫) =
      gaussianReal 0 1 := by
  have hcomp : (fun ω : ι → ℝ => ⟪u, WithLp.toLp 2 ω⟫) =
      (fun x : EuclideanSpace ℝ ι => ⟪u, x⟫) ∘ WithLp.toLp 2 := rfl
  have hnn : ‖u‖₊ ^ 2 = 1 := by
    ext; simp [hu]
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    (measurePreserving_toLp_pi_gaussianReal ι).map_eq, stdGaussian_map_inner, hnn]

/-- Under `Measure.pi (gaussianReal 0 1)`, `{ω | ⟪u, ω⟫ < t}` has probability `Φ(t)`. -/
private theorem measureReal_inner_lt_eq_cdf {ι : Type*} [Fintype ι] {u : EuclideanSpace ℝ ι}
    (hu : ‖u‖ = 1) (t : ℝ) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real {ω | ⟪u, WithLp.toLp 2 ω⟫ < t} =
      cdf (gaussianReal 0 1) t := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hpre : {ω : ι → ℝ | ⟪u, WithLp.toLp 2 ω⟫ < t} =
      (fun ω => ⟪u, WithLp.toLp 2 ω⟫) ⁻¹' Iio t := rfl
  rw [hpre, ← map_measureReal_apply (by fun_prop) measurableSet_Iio,
    pi_gaussianReal_map_inner_unit hu, measureReal_congr Iio_ae_eq_Iic, ← cdf_eq_real]

/-- At a degree-`3` vertex `v` of a loopless subcubic multigraph `G`, `v` belongs to
`lowSide G (edgeScore G q R ·) 0` with probability `1 / 2`. -/
private theorem measureReal_lowSide_zero_eq_half {V E : Type*} [Fintype V] [Finite E]
    {G : Multigraph V E} (hloop : G.Loopless) (hdeg : G.MaxDegreeLE 3) {q : ℝ} (hq : 0 ≤ q)
    {R : ℕ} {ρ₀ : ℝ} (hρ₀ : -1 < ρ₀) (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    {v : V} (hv : (G.incidenceSet v).ncard = 3) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real
      {ω | v ∈ lowSide G (edgeScore G q R ω) 0} = 1 / 2 := by
  classical
  set P := Measure.pi fun _ : V => gaussianReal 0 1
  obtain ⟨e₀, e₁, e₂, h01, h02, h12, hinc⟩ := ncard_eq_three.mp hv
  set A : Set (V → ℝ) := {ω | v ∈ lowSide G (edgeScore G q R ω) 0}
  have hcount (ω : V → ℝ) (p : E → Prop) [DecidablePred p] :
      {e ∈ G.incidenceSet v | p e}.ncard =
        (if p e₀ then 1 else 0) + (if p e₁ then 1 else 0) + (if p e₂ then 1 else 0) := by
    have hs : {e ∈ G.incidenceSet v | p e} = ↑(({e₀, e₁, e₂} : Finset E).filter p) := by
      ext e; simp [hinc]
    rw [hs, ncard_coe_finset, Finset.card_filter, Finset.sum_insert (by simp [h01, h02]),
      Finset.sum_insert (by simp [h12]), Finset.sum_singleton, add_assoc]
  have hAm : MeasurableSet A := by
    have hA_eq : A =
        ({ω | edgeScore G q R ω e₀ < 0} ∩ {ω | edgeScore G q R ω e₁ < 0}) ∪
        ({ω | edgeScore G q R ω e₀ < 0} ∩ {ω | edgeScore G q R ω e₂ < 0}) ∪
        ({ω | edgeScore G q R ω e₁ < 0} ∩ {ω | edgeScore G q R ω e₂ < 0}) := by
      ext ω
      simp only [A, lowSide, mem_ofPred_eq, hcount ω, mem_union, mem_inter_iff]
      by_cases p0 : edgeScore G q R ω e₀ < 0 <;>
        by_cases p1 : edgeScore G q R ω e₁ < 0 <;>
        by_cases p2 : edgeScore G q R ω e₂ < 0 <;> simp [p0, p1, p2]
    rw [hA_eq]
    have hm (e : E) : MeasurableSet {ω | edgeScore G q R ω e < 0} :=
      measurableSet_lt (measurable_edgeScore q R e) measurable_const
    exact (((hm e₀).inter (hm e₁)).union ((hm e₀).inter (hm e₂))).union ((hm e₁).inter (hm e₂))
  have hneg_mp : MeasurePreserving (fun ω : V → ℝ => -ω) P P := by
    have hid : (fun ω : V → ℝ => -ω) = fun ω i => -ω i := rfl
    rw [hid]
    refine ⟨by fun_prop, ?_⟩
    simpa [gaussianReal_zero_map_neg] using
      (Measure.pi_map_pi (μ := fun _ : V => gaussianReal 0 1) fun _ => measurable_neg.aemeasurable)
  have hscore_neg (ω : V → ℝ) (e : E) : edgeScore G q R (-ω) e = -edgeScore G q R ω e := by
    simp only [edgeScore]
    have hlp : WithLp.toLp 2 (-ω) = -WithLp.toLp 2 ω := rfl
    rw [hlp, inner_neg_right]
  have hmap_eq : P.real ((fun ω : V → ℝ => -ω) ⁻¹' A) = P.real A :=
    hneg_mp.measureReal_preimage hAm.nullMeasurableSet
  set Z : Set (V → ℝ) :=
    {ω | edgeScore G q R ω e₀ = 0} ∪ {ω | edgeScore G q R ω e₁ = 0} ∪
      {ω | edgeScore G q R ω e₂ = 0}
  have hZ0 : P.real Z = 0 := by
    have hz (e : E) : P.real {ω | edgeScore G q R ω e = 0} = 0 :=
      measureReal_pi_gaussianReal_inner_eq_zero (norm_edgeVector hloop hdeg hq hρ₀ hρ e)
    have hle : P.real Z ≤ P.real {ω | edgeScore G q R ω e₀ = 0} +
        P.real {ω | edgeScore G q R ω e₁ = 0} + P.real {ω | edgeScore G q R ω e₂ = 0} :=
      (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
    rw [hz e₀, hz e₁, hz e₂] at hle
    exact le_antisymm (by linarith) measureReal_nonneg
  have hdisj : Disjoint A ((fun ω : V → ℝ => -ω) ⁻¹' A) := by
    refine disjoint_left.mpr fun ω h1 h2 => ?_
    rw [mem_preimage] at h2
    simp only [A, lowSide, mem_ofPred_eq, hscore_neg, neg_lt_zero] at h1 h2
    rw [hcount ω] at h1
    rw [hcount ω] at h2
    split_ifs at h1 h2 <;> linarith
  have hcover : (Set.univ : Set (V → ℝ)) ⊆ A ∪ ((fun ω : V → ℝ => -ω) ⁻¹' A) ∪ Z := by
    intro ω _
    by_cases hZ : ω ∈ Z
    · exact Or.inr hZ
    · left
      simp only [Z, mem_union, mem_ofPred_eq, not_or] at hZ
      obtain ⟨⟨hne0, hne1⟩, hne2⟩ := hZ
      simp only [A, lowSide, mem_union, mem_preimage, mem_ofPred_eq, hscore_neg, neg_lt_zero]
      rw [hcount ω, hcount ω]
      rcases lt_or_gt_of_ne hne0 with h0 | h0 <;>
        rcases lt_or_gt_of_ne hne1 with h1 | h1 <;>
        rcases lt_or_gt_of_ne hne2 with h2 | h2 <;>
        (split_ifs <;> omega)
  have hunion_eq : P.real (A ∪ (fun ω : V → ℝ => -ω) ⁻¹' A) = 2 * P.real A := by
    rw [measureReal_union hdisj (hAm.preimage (by fun_prop)), hmap_eq]
    ring
  have hle1 : 2 * P.real A ≤ 1 := by
    rw [← hunion_eq]
    exact measureReal_le_one
  have hge1 : 1 ≤ 2 * P.real A := by
    have h1 : (1 : ℝ) = P.real Set.univ := probReal_univ.symm
    have h2 : P.real Set.univ ≤ P.real (A ∪ (fun ω : V → ℝ => -ω) ⁻¹' A) + P.real Z :=
      (measureReal_mono hcover (measure_lt_top P _).ne).trans (measureReal_union_le _ _)
    rw [← h1, hunion_eq, hZ0, add_zero] at h2
    exact h2
  linarith

/-- Measurability of `lowSide` at any threshold `t`. -/
private theorem measurableSet_lowSide {V E : Type*} [Fintype V] [Finite E]
    (G : Multigraph V E) (q : ℝ) (R : ℕ) (t : ℝ) (v : V) :
    MeasurableSet {ω : V → ℝ | v ∈ lowSide G (edgeScore G q R ω) t} := by
  classical
  have := Fintype.ofFinite E
  let s := (G.incidenceSet v).toFinset
  have heq : {ω : V → ℝ | v ∈ lowSide G (edgeScore G q R ω) t} =
      ⋃ p ∈ s.offDiag,
        {ω | edgeScore G q R ω p.1 < t} ∩ {ω | edgeScore G q R ω p.2 < t} := by
    ext ω
    have hcard_eq : {e ∈ G.incidenceSet v | edgeScore G q R ω e < t}.ncard =
        (s.filter fun e => edgeScore G q R ω e < t).card := by
      rw [← ncard_coe_finset]; congr 1; ext e; simp [s]
    simp only [lowSide, mem_ofPred_eq, hcard_eq, mem_iUnion, mem_inter_iff, Finset.mem_offDiag]
    constructor
    · intro h2
      obtain ⟨e₁, e₂, he₁, he₂, hne⟩ :=
        Finset.one_lt_card_iff.mp (Nat.lt_of_lt_of_le Nat.one_lt_two h2)
      obtain ⟨h1s, ht1⟩ := Finset.mem_filter.mp he₁
      obtain ⟨h2s, ht2⟩ := Finset.mem_filter.mp he₂
      exact ⟨(e₁, e₂), ⟨h1s, h2s, hne⟩, ht1, ht2⟩
    · rintro ⟨⟨e₁, e₂⟩, ⟨h1s, h2s, hne⟩, ht1, ht2⟩
      have hsub : ({e₁, e₂} : Finset E) ⊆ s.filter fun e => edgeScore G q R ω e < t := by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he2
        · exact Finset.mem_filter.mpr ⟨h1s, ht1⟩
        · rw [Finset.mem_singleton.mp he2]
          exact Finset.mem_filter.mpr ⟨h2s, ht2⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_pair hne] at hle
      exact hle
  rw [heq]
  exact s.offDiag.measurableSet_biUnion fun p _ =>
    (measurableSet_lt (measurable_edgeScore q R p.1) measurable_const).inter
      (measurableSet_lt (measurable_edgeScore q R p.2) measurable_const)

/-- Locality of `lowSide`: depends only on `closedBall G.toSimpleGraph v (R + 1)`. -/
private theorem dependsOn_lowSide {V E : Type*} [Fintype V] (G : Multigraph V E) (q : ℝ) (R : ℕ)
    (t : ℝ) (v : V) :
    DependsOn (fun ω : V → ℝ => v ∈ lowSide G (edgeScore G q R ω) t)
      (closedBall G.toSimpleGraph v (R + 1)) := by
  intro ω₁ ω₂ hω
  simp only [lowSide, mem_ofPred_eq]
  have hset : {e ∈ G.incidenceSet v | edgeScore G q R ω₁ e < t} =
      {e ∈ G.incidenceSet v | edgeScore G q R ω₂ e < t} := by
    ext e
    exact and_congr_right fun he => by rw [edgeScore_congr he hω]
  rw [hset]

/-- Decompose `G.edgeCut Y₁` for a subset `Y₁ ⊆ Y` into internal edges of `Y` crossing `Y₁` and
boundary edges of `Y` whose `Y`-endpoint lies in `Y₁`. -/
private theorem ncard_edgeCut_sub_eq {V E : Type*} [Finite E] {G : Multigraph V E} {Y Y₁ : Set V}
    (hY₁ : Y₁ ⊆ Y) :
    (G.edgeCut Y₁).ncard =
      ((G.induce Y).edgeCut {x : Y | x.1 ∈ Y₁}).ncard +
        {e ∈ G.edgeCut Y | endIn G Y e ∈ Y₁}.ncard := by
  classical
  set A := Subtype.val '' (G.induce Y).edgeCut {x : Y | x.1 ∈ Y₁}
  set B := {e ∈ G.edgeCut Y | endIn G Y e ∈ Y₁}
  have hdisj : Disjoint A B := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨⟨e, hsY, htY⟩, -, rfl⟩ ⟨heCut, -⟩
    exact heCut (iff_of_true hsY htY)
  have hunion : G.edgeCut Y₁ = A ∪ B := by
    ext e
    constructor
    · intro he₁
      by_cases heY : e ∈ G.edgeCut Y
      · right
        refine ⟨heY, ?_⟩
        obtain ⟨hend, hinc, _⟩ := endIn_mem heY
        rw [mem_edgeCut] at he₁ heY
        dsimp only [endIn] at hend ⊢
        split_ifs with hs
        · by_contra hs₁
          have ht₁ : G.tgt e ∈ Y₁ := by tauto
          exact heY (iff_of_true hs (hY₁ ht₁))
        · by_contra ht₁
          have hs₁ : G.src e ∈ Y₁ := by tauto
          exact hs (hY₁ hs₁)
      · left
        rw [mem_edgeCut, not_not] at heY
        by_cases hsY : G.src e ∈ Y
        · have htY : G.tgt e ∈ Y := heY.mp hsY
          exact ⟨⟨e, hsY, htY⟩, he₁, rfl⟩
        · exfalso
          have htY : G.tgt e ∉ Y := fun h => hsY (heY.mpr h)
          have hs₁ : G.src e ∉ Y₁ := fun h => hsY (hY₁ h)
          have ht₁ : G.tgt e ∉ Y₁ := fun h => htY (hY₁ h)
          exact he₁ (iff_of_false hs₁ ht₁)
    · rintro (⟨⟨e, hsY, htY⟩, he₁, rfl⟩ | ⟨heY, hend₁⟩)
      · exact he₁
      · rw [mem_edgeCut] at heY ⊢
        dsimp only [endIn] at hend₁
        split_ifs at hend₁ with hs
        · exact fun h => heY (iff_of_true hs (hY₁ (h.mp hend₁)))
        · exact fun h => hs (hY₁ (h.mpr hend₁))
  rw [hunion, ncard_union_eq hdisj (toFinite _) (toFinite _),
    ncard_image_of_injective _ Subtype.val_injective]

/-- Degree identity at each vertex of `G.induce X` inside a loopless cubic multigraph `G`:
`|(G.induce X).incidenceSet x| + |G.incidenceSet x ∩ G.edgeCut X| = 3`, and summing over `X` yields
`2 |E(G.induce X)| + |G.edgeCut X| = 3 |X|`. -/
private theorem induce_degree_and_handshake {V E : Type*} [Finite E]
    {G : Multigraph V E} (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    (X : Set V) [Fintype X] :
    (∀ x : X, ((G.induce X).incidenceSet x).ncard +
        (G.incidenceSet x.1 ∩ G.edgeCut X).ncard = 3) ∧
      2 * Nat.card {e : E // G.src e ∈ X ∧ G.tgt e ∈ X} + (G.edgeCut X).ncard =
        3 * Nat.card X ∧
      ∑ x : X, (G.incidenceSet x.1 ∩ G.edgeCut X).ncard = (G.edgeCut X).ncard := by
  classical
  have := Fintype.ofFinite E
  have hpt (x : X) : ((G.induce X).incidenceSet x).ncard +
      (G.incidenceSet x.1 ∩ G.edgeCut X).ncard = 3 := by
    set A := Subtype.val '' (G.induce X).incidenceSet x
    set B := G.incidenceSet x.1 ∩ G.edgeCut X
    have hdisj : Disjoint A B := by
      refine disjoint_left.mpr ?_
      rintro _ ⟨⟨e, hs, ht⟩, -, rfl⟩ ⟨-, hcut⟩
      exact hcut (iff_of_true hs ht)
    have hunion : A ∪ B = G.incidenceSet x.1 := by
      ext e
      constructor
      · rintro (⟨⟨e, hs, ht⟩, hx, rfl⟩ | ⟨hx, -⟩)
        · rcases hx with hsx | htx
          · exact Or.inl (congrArg Subtype.val hsx)
          · exact Or.inr (congrArg Subtype.val htx)
        · exact hx
      · intro hx
        by_cases hcut : e ∈ G.edgeCut X
        · exact Or.inr ⟨hx, hcut⟩
        · rw [mem_edgeCut, not_not] at hcut
          rcases hx with heq | heq
          · have hs : G.src e ∈ X := heq ▸ x.2
            exact Or.inl ⟨⟨e, hs, hcut.mp hs⟩, Or.inl (Subtype.ext heq), rfl⟩
          · have ht : G.tgt e ∈ X := heq ▸ x.2
            exact Or.inl ⟨⟨e, hcut.mpr ht, ht⟩, Or.inr (Subtype.ext heq), rfl⟩
    rw [← ncard_image_of_injective _ Subtype.val_injective, ← ncard_union_eq hdisj, hunion, h3 x.1]
  have hsum_cut : ∑ x : X, (G.incidenceSet x.1 ∩ G.edgeCut X).ncard = (G.edgeCut X).ncard := by
    have h1 (x : X) : (G.incidenceSet x.1 ∩ G.edgeCut X).ncard =
        (Finset.univ.filter fun e : E => e ∈ G.incidenceSet x.1 ∧ e ∈ G.edgeCut X).card := by
      rw [← ncard_coe_finset]; congr 1; ext e; simp
    simp_rw [h1, Finset.card_filter]
    rw [Finset.sum_comm]
    have h2 (e : E) :
        (∑ x : X, if e ∈ G.incidenceSet x.1 ∧ e ∈ G.edgeCut X then 1 else 0) =
          if e ∈ G.edgeCut X then 1 else 0 := by
      by_cases he : e ∈ G.edgeCut X
      · simp only [he, and_true, ↓reduceIte, ← Finset.card_filter]
        obtain ⟨hm, hinc, hunq⟩ := endIn_mem he
        have hsingleton : (Finset.univ.filter fun x : X => e ∈ G.incidenceSet x.1) =
            {⟨endIn G X e, hm⟩} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
            Subtype.ext_iff]
          exact ⟨hunq x.1 x.2, fun h => h ▸ hinc⟩
        rw [hsingleton, Finset.card_singleton]
      · simp [he]
    simp_rw [h2, ← Finset.card_filter]
    rw [← ncard_coe_finset]
    congr 1; ext e; simp
  have hloop_ind : (G.induce X).Loopless := fun e h => hloop e.1 (congrArg Subtype.val h)
  have hind_sum := (G.induce X).sum_ncard_incidenceSet hloop_ind
  have htot := Finset.sum_congr (s₁ := (Finset.univ : Finset X)) rfl fun x _ => hpt x
  rw [Finset.sum_add_distrib, hind_sum, hsum_cut, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, ← Nat.card_eq_fintype_card (α := X)] at htot
  exact ⟨hpt, by omega, hsum_cut⟩

/-- Choose correlation parameters `(q, R, ρ₀)` with `straddleBound ρ₀ ≤ gaussianCoefficient + δ`. -/
private theorem exists_straddle_params {δ : ℝ} (hδ : 0 < δ) :
    ∃ (q : ℝ) (R : ℕ) (ρ₀ : ℝ), 0 ≤ q ∧ 0 ≤ ρ₀ ∧
      ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ∧
      straddleBound ρ₀ ≤ gaussianCoefficient + δ := by
  set g : ℝ := 2 * √2 / 3 with hg
  have hsqrt_lo : (7 : ℝ) / 5 < √2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    ((continuous_arccos.comp (by fun_prop : Continuous fun ρ : ℝ => (1 + 3 * ρ) / 4)
      ).continuousAt (x := g)) (2 * π * δ / 3) (by positivity)
  set ρ₀ := g - min η (1 / 4) / 2 with hρ₀
  have hmin : 0 < min η (1 / 4) := lt_min hη (by norm_num)
  have hρ₀g : ρ₀ < g := by linarith
  have hρ₀_nonneg : 0 ≤ ρ₀ := by
    rw [hρ₀, hg]; linarith [min_le_right η (1 / 4)]
  have h3 : vertexCorrelation 3 = g := by norm_num [vertexCorrelation, hg]
  obtain ⟨q, R, hq, hρ⟩ := exists_decay_radius_degree (by norm_num : 2 ≤ 3) (ρ := ρ₀)
    (by rw [h3]; exact hρ₀g)
  norm_num at hρ
  refine ⟨q, R, ρ₀, hq, hρ₀_nonneg, hρ, ?_⟩
  have hdist : dist ρ₀ g < η := by
    rw [Real.dist_eq, hρ₀, abs_of_neg (by linarith)]
    linarith [min_le_left η (1 / 4)]
  have hc := (le_abs_self _).trans (hcont hdist).le
  simp only [Function.comp_apply] at hc
  rw [straddleBound, gaussianCoefficient_eq, ← hg, straddleBound]
  have hpi := pi_pos
  calc 3 / (2 * π) * arccos ((1 + 3 * ρ₀) / 4)
      ≤ 3 / (2 * π) * (arccos ((1 + 3 * g) / 4) + 2 * π * δ / 3) := by
        gcongr; linarith only [hc]
    _ = 3 / (2 * π) * arccos ((1 + 3 * g) / 4) + δ := by field_simp

end Helpers

/-! ### Depth-one `CappedCompression` bisection -/

section DepthOne

/-- The second part of a partition `S = T ∪ U` has the remaining cardinality. -/
private theorem ncard_eq_sub_of_union {α : Type*} [Finite α] {S T U : Set α}
    (hTU : Disjoint T U) (h : T ∪ U = S) : (U.ncard : ℝ) = S.ncard - T.ncard := by
  rw [← h, ncard_union_eq hTU (toFinite _) (toFinite _)]
  push_cast
  ring

/-- Splitting `X = X₁ ⊔ X₂` splits the cut edges of `X` by the part that contains their end in
`X`. -/
private theorem ncard_edgeCut_endIn_eq_sub {V E : Type*} [Finite E] {G : Multigraph V E}
    {X X₁ X₂ : Set V} (hd : Disjoint X₁ X₂) (hu : X₁ ∪ X₂ = X) :
    ({e ∈ G.edgeCut X | endIn G X e ∈ X₂}.ncard : ℝ) =
      (G.edgeCut X).ncard - ({e ∈ G.edgeCut X | endIn G X e ∈ X₁}.ncard : ℝ) := by
  refine ncard_eq_sub_of_union (disjoint_left.mpr fun _ h1 h2 => disjoint_left.mp hd h1.2 h2.2) ?_
  ext e
  refine ⟨by rintro (h | h) <;> exact h.1, fun he => ?_⟩
  rcases (hu ▸ (endIn_mem he).1 : endIn G X e ∈ X₁ ∪ X₂) with h | h
  exacts [Or.inl ⟨he, h⟩, Or.inr ⟨he, h⟩]

/-- Two complementary parts summing to `t` with `|a - t / 2| < c` are each at most
`t / 2 + c`. -/
private theorem le_half_add_of_abs_lt {a b t c : ℝ} (hb : b = t - a)
    (habs : |a - 1 / 2 * t| < c) :
    a ≤ 1 / 2 * t + c ∧ b ≤ 1 / 2 * t + c := by
  have ⟨h1, h2⟩ := abs_lt.mp habs
  exact ⟨by linarith only [h2], by linarith only [h1, hb]⟩

/-- Real-cast decomposition of `G.edgeCut Y₁` for a subset `Y₁ ⊆ Y`. -/
private theorem ncard_edgeCut_sub_cast_eq {V E : Type*} [Finite E] {G : Multigraph V E}
    {Y Y₁ : Set V} (hY₁ : Y₁ ⊆ Y) :
    ((G.edgeCut Y₁).ncard : ℝ) =
      (((G.induce Y).edgeCut {x : Y | x.1 ∈ Y₁}).ncard : ℝ) +
        ({e ∈ G.edgeCut Y | endIn G Y e ∈ Y₁}.ncard : ℝ) := by
  exact_mod_cast ncard_edgeCut_sub_eq (G := G) hY₁

/-! #### Paired Gaussian events on a subcubic quotient multigraph -/

/-- First-coordinate projection of a paired Gaussian sample. -/
private abbrev fstProj {β : Type*} (ω : β → ℝ × ℝ) : β → ℝ :=
  fun B => (ω B).1

/-- Projecting each block coordinate `(g, h) ↦ g` preserves the product Gaussian law. -/
private theorem measurePreserving_fstProj {β : Type*} [Fintype β] :
    MeasurePreserving (fstProj (β := β))
      (Measure.pi fun _ : β => (gaussianReal 0 1).prod (gaussianReal 0 1))
      (Measure.pi fun _ : β => gaussianReal 0 1) := by
  refine ⟨by fun_prop, ?_⟩
  have h1 := Measure.pi_map_pi
    (μ := fun _ : β => (gaussianReal 0 1).prod (gaussianReal 0 1))
    (f := fun _ (z : ℝ × ℝ) => z.1) fun _ => measurable_fst.aemeasurable
  simpa [fstProj, Measure.fst_prod] using h1

/-- Symmetric (`t = 0`) side event on a subcubic multigraph `Q`: degree-`3` vertices follow the
Gaussian `lowSide` score using the first coordinate, while lower-degree vertices use an independent
fair sign `(ω B).2 < 0`. -/
private noncomputable def blockSideEvent {β ε : Type*} [Fintype β] (Q : Multigraph β ε)
    (q : ℝ) (R : ℕ) (B : β) : Set (β → ℝ × ℝ) :=
  if (Q.incidenceSet B).ncard = 3 then
    {ω | B ∈ lowSide Q (edgeScore Q q R (fstProj ω)) 0}
  else
    {ω | (ω B).2 < 0}

/-- Measurability of `blockSideEvent`. -/
private theorem measurableSet_blockSideEvent {β ε : Type*} [Fintype β] [Finite ε]
    (Q : Multigraph β ε) (q : ℝ) (R : ℕ) (B : β) :
    MeasurableSet (blockSideEvent Q q R B) := by
  dsimp only [blockSideEvent]
  split_ifs
  · exact (measurableSet_lowSide Q q R 0 B).preimage (by fun_prop)
  · exact measurableSet_lt (measurable_snd.comp (measurable_pi_apply B)) measurable_const

/-- Locality of `blockSideEvent`: depends only on coordinates inside `closedBall _ B (R + 1)`. -/
private theorem dependsOn_blockSideEvent {β ε : Type*} [Fintype β] (Q : Multigraph β ε)
    (q : ℝ) (R : ℕ) (B : β) :
    DependsOn (· ∈ blockSideEvent Q q R B) (closedBall Q.toSimpleGraph B (R + 1)) := by
  intro ω₁ ω₂ hω
  dsimp only [blockSideEvent]
  split_ifs
  · exact dependsOn_lowSide Q q R 0 B fun z hz => congrArg Prod.fst (hω z hz)
  · have hB_mem : B ∈ closedBall Q.toSimpleGraph B (R + 1) := by simp [closedBall]
    simp [congrArg Prod.snd (hω B hB_mem)]

/-- Every vertex `B` of a loopless subcubic multigraph enters `blockSideEvent` with probability
`1 / 2`. -/
private theorem measureReal_blockSideEvent_eq_half {β ε : Type*} [Fintype β] [Finite ε]
    {Q : Multigraph β ε} (hloop : Q.Loopless) (hdeg : Q.MaxDegreeLE 3) {q : ℝ} (hq : 0 ≤ q)
    {R : ℕ} {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (B : β) :
    (Measure.pi fun _ : β => (gaussianReal 0 1).prod (gaussianReal 0 1)).real
      (blockSideEvent Q q R B) = 1 / 2 := by
  dsimp only [blockSideEvent]
  split_ifs with hdegB
  · have hpre : {ω : β → ℝ × ℝ | B ∈ lowSide Q (edgeScore Q q R (fstProj ω)) 0} =
        fstProj ⁻¹' {ω' | B ∈ lowSide Q (edgeScore Q q R ω') 0} := rfl
    rw [hpre, measurePreserving_fstProj.measureReal_preimage
      (measurableSet_lowSide Q q R 0 B).nullMeasurableSet]
    exact measureReal_lowSide_zero_eq_half hloop hdeg hq (by linarith) hρ hdegB
  · have hsnd : MeasurePreserving Prod.snd ((gaussianReal 0 1).prod (gaussianReal 0 1))
        (gaussianReal 0 1) := ⟨measurable_snd, Measure.snd_prod⟩
    have hproj_mp := hsnd.comp
      (measurePreserving_eval (fun _ : β => (gaussianReal 0 1).prod (gaussianReal 0 1)) B)
    have hpre : {ω : β → ℝ × ℝ | (ω B).2 < 0} =
        (Prod.snd ∘ Function.eval B) ⁻¹' Iio 0 := rfl
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    rw [hpre, hproj_mp.measureReal_preimage measurableSet_Iio.nullMeasurableSet,
      measureReal_congr Iio_ae_eq_Iic, ← cdf_eq_real, cdf_gaussianReal_zero_zero one_ne_zero]
    norm_num

/-- Straddling event on degree-`3` vertices of a subcubic multigraph under the paired Gaussian
sample (empty on vertices of degree `< 3`). -/
private noncomputable def blockStradEvent {β ε : Type*} [Fintype β] (Q : Multigraph β ε)
    (q : ℝ) (R : ℕ) (B : β) : Set (β → ℝ × ℝ) :=
  if (Q.incidenceSet B).ncard = 3 then
    fstProj ⁻¹' straddleEvent Q q R 0 B
  else
    ∅

/-- Measurability of `blockStradEvent`. -/
private theorem measurableSet_blockStradEvent {β ε : Type*} [Fintype β] [Finite ε]
    (Q : Multigraph β ε) (q : ℝ) (R : ℕ) (B : β) :
    MeasurableSet (blockStradEvent Q q R B) := by
  dsimp only [blockStradEvent]
  split_ifs
  · exact (measurableSet_straddleEvent 0 B (q := q) (R := R)).preimage (by fun_prop)
  · exact MeasurableSet.empty

/-- Locality of `blockStradEvent`: depends only on coordinates inside `closedBall _ B (R + 1)`. -/
private theorem dependsOn_blockStradEvent {β ε : Type*} [Fintype β] (Q : Multigraph β ε)
    (q : ℝ) (R : ℕ) (B : β) :
    DependsOn (· ∈ blockStradEvent Q q R B) (closedBall Q.toSimpleGraph B (R + 1)) := by
  intro ω₁ ω₂ hω
  dsimp only [blockStradEvent]
  split_ifs
  · exact dependsOn_straddleEvent q R 0 B fun z hz => congrArg Prod.fst (hω z hz)
  · rfl

/-- Single-vertex straddle probability bound for `blockStradEvent`. -/
private theorem measureReal_blockStradEvent_le {β ε : Type*} [Fintype β] [Finite ε]
    {Q : Multigraph β ε} (hloop : Q.Loopless) (hdeg : Q.MaxDegreeLE 3) {q : ℝ} (hq : 0 ≤ q)
    {R : ℕ} {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (B : β) :
    (Measure.pi fun _ : β => (gaussianReal 0 1).prod (gaussianReal 0 1)).real
        (blockStradEvent Q q R B) ≤
      if (Q.incidenceSet B).ncard = 3 then straddleBound ρ₀ else 0 := by
  dsimp only [blockStradEvent]
  split_ifs with hdegB
  · rw [measurePreserving_fstProj.measureReal_preimage
      (measurableSet_straddleEvent q R 0 B).nullMeasurableSet]
    have hb := measureReal_straddleEvent_le_of_ncard_eq_three hloop hdeg hq hρ₀ hρ 0 hdegB
    simpa using hb
  · simp

/-- Cut bound on `blockSideEvent`: cut edges of `S_Q = {B | ω ∈ blockSideEvent Q q R B}` either
touch a block of degree `1` or `2` (at most `2` each) or join two degree-`3` blocks (injected into
`blockStradEvent`). -/
private theorem ncard_edgeCut_blockSideEvent_le {β ε : Type*} [Fintype β] [Finite ε]
    {Q : Multigraph β ε} (hdeg : Q.MaxDegreeLE 3) (q : ℝ) (R : ℕ) (ω : β → ℝ × ℝ) :
    (Q.edgeCut {B | ω ∈ blockSideEvent Q q R B}).ncard ≤
      2 * (Finset.univ.filter fun B : β =>
          1 ≤ (Q.incidenceSet B).ncard ∧ (Q.incidenceSet B).ncard ≤ 2).card +
        {B : β | ω ∈ blockStradEvent Q q R B}.ncard := by
  classical
  have := Fintype.ofFinite ε
  set S_Q : Set β := {B | ω ∈ blockSideEvent Q q R B}
  set Lset := Finset.univ.filter fun B : β =>
    1 ≤ (Q.incidenceSet B).ncard ∧ (Q.incidenceSet B).ncard ≤ 2
  set E_low := {e ∈ Q.edgeCut S_Q | Q.src e ∈ Lset ∨ Q.tgt e ∈ Lset}
  set E_33 := {e ∈ Q.edgeCut S_Q | (Q.incidenceSet (Q.src e)).ncard = 3 ∧
    (Q.incidenceSet (Q.tgt e)).ncard = 3}
  have hcover : Q.edgeCut S_Q ⊆ E_low ∪ E_33 := by
    intro e he
    have hs0 : 1 ≤ (Q.incidenceSet (Q.src e)).ncard := (ncard_pos (toFinite _)).mpr ⟨e, Or.inl rfl⟩
    have ht0 : 1 ≤ (Q.incidenceSet (Q.tgt e)).ncard := (ncard_pos (toFinite _)).mpr ⟨e, Or.inr rfl⟩
    have hs3 := hdeg (Q.src e)
    have ht3 := hdeg (Q.tgt e)
    by_cases hsL : (Q.incidenceSet (Q.src e)).ncard ≤ 2
    · exact Or.inl ⟨he, Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs0, hsL⟩)⟩
    by_cases htL : (Q.incidenceSet (Q.tgt e)).ncard ≤ 2
    · exact Or.inl ⟨he, Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht0, htL⟩)⟩
    · exact Or.inr ⟨he, by omega, by omega⟩
  have hlow_bound : E_low.ncard ≤ 2 * Lset.card := by
    have hsub : E_low ⊆ ↑(Lset.biUnion fun B => (Q.incidenceSet B).toFinset) := by
      rintro e ⟨-, hs | ht⟩
      · exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨Q.src e, hs,
          Set.mem_toFinset.mpr (Or.inl rfl)⟩)
      · exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨Q.tgt e, ht,
          Set.mem_toFinset.mpr (Or.inr rfl)⟩)
    refine (ncard_le_ncard hsub (toFinite _)).trans ?_
    rw [ncard_coe_finset]
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ B ∈ Lset, (Q.incidenceSet B).toFinset.card
        ≤ ∑ _B ∈ Lset, 2 := Finset.sum_le_sum fun B hB => by
          rw [← Set.ncard_eq_toFinset_card']
          exact (Finset.mem_filter.mp hB).2.2
      _ = 2 * Lset.card := by simp [Nat.mul_comm]
  have h33_bound : E_33.ncard ≤ {B : β | ω ∈ blockStradEvent Q q R B}.ncard := by
    set D3 : Set β := {B | (Q.incidenceSet B).ncard = 3}
    have hcut := ncard_edgeCut_inter_le_straddling (G := Q) (D := D3) (S := S_Q)
      (fun _ h => h) (edgeScore Q q R (fstProj ω)) 0 fun B hB => by
        simp only [D3, mem_ofPred_eq] at hB
        simp [S_Q, blockSideEvent, hB, lowSide]
    refine hcut.trans (ncard_le_ncard ?_ (toFinite _))
    rintro B ⟨hB, hstrad⟩
    simp only [D3, mem_ofPred_eq] at hB
    simpa [blockStradEvent, hB, straddleEvent] using hstrad
  exact ((ncard_le_ncard hcover (toFinite _)).trans (ncard_union_le _ _)).trans
    (Nat.add_le_add hlow_bound h33_bound)

/-- Simultaneous second-moment concentration on `Q` for two bounded vertex-weight functions `vWt`
and `bWt` on `blockSideEvent` and the unweighted count of `blockStradEvent`. -/
private theorem exists_concentrated_blockSample {β ε : Type*} [Fintype β] [Finite ε]
    {Q : Multigraph β ε} (hdeg : Q.MaxDegreeLE 3) (q : ℝ) (R : ℕ)
    {M : ℕ} (hM1 : (1 : ℝ) ≤ M) {h η : ℝ} (hη : 0 < η) (hcard : (Fintype.card β : ℝ) ≤ h)
    (large : 4 * (M : ℝ) ^ 2 * (vertexOverlap 3 R : ℝ) / η ^ 2 < h)
    {vWt bWt : β → ℝ} (hvWt : ∀ B, 0 ≤ vWt B ∧ vWt B ≤ M) (hbWt : ∀ B, 0 ≤ bWt B ∧ bWt B ≤ M) :
    let P := Measure.pi fun _ : β => (gaussianReal 0 1).prod (gaussianReal 0 1)
    ∃ ω : β → ℝ × ℝ,
      ω ∉ weightedDeviation P Finset.univ vWt (blockSideEvent Q q R) (η * h) ∧
      ω ∉ weightedDeviation P Finset.univ bWt (blockSideEvent Q q R) (η * h) ∧
      ω ∉ weightedDeviation P Finset.univ 1 (blockStradEvent Q q R) (η * h) := by
  intro P
  set c : ℝ := η * h
  set D := vertexOverlap 3 R
  have hh_pos : 0 < h := lt_of_le_of_lt (by positivity) large
  have hdev (w : β → ℝ) {A : β → Set (β → ℝ × ℝ)} (hA : ∀ B, MeasurableSet (A B))
      (hAd : ∀ B, DependsOn (· ∈ A B) (closedBall Q.toSimpleGraph B (R + 1)))
      (hw : ∀ B, 0 ≤ w B ∧ w B ≤ M) :
      P.real (weightedDeviation P Finset.univ w A c) ≤ h * M ^ 2 * D / c ^ 2 :=
    (measureReal_weightedDeviation_le _ (fun B _ => hA B) (fun B _ => (hw B).1)
      (fun B _ => (hw B).2) _ (fun B _ => hAd B)
      (fun B _ => card_not_disjoint_closedBall_le hdeg (by norm_num) R B)
      (by positivity)).trans (by gcongr; simpa using hcard)
  have hdevV := hdev vWt (measurableSet_blockSideEvent Q q R) (dependsOn_blockSideEvent Q q R) hvWt
  have hdevB := hdev bWt (measurableSet_blockSideEvent Q q R) (dependsOn_blockSideEvent Q q R) hbWt
  have hdevS := hdev 1 (measurableSet_blockStradEvent Q q R) (dependsOn_blockStradEvent Q q R)
    fun _ => ⟨zero_le_one, hM1⟩
  obtain ⟨ω, hω⟩ := exists_notMem_of_measureReal_lt_one (((measureReal_union_le _ _).trans
    (add_le_add ((measureReal_union_le _ _).trans (add_le_add hdevV hdevB)) hdevS)).trans_lt
    (by calc _ = 3 * (M : ℝ) ^ 2 * D * h / c ^ 2 := by ring
      _ < 1 := mul_div_mul_sq_lt_one hη.ne' hh_pos
        ((by gcongr; norm_num : 3 * (M : ℝ) ^ 2 * D / η ^ 2 ≤ _).trans_lt large)))
  simp only [mem_union, not_or] at hω
  exact ⟨ω, hω.1.1, hω.1.2, hω.2⟩

/-- Extract the upper bound on `{B | ω ∈ blockStradEvent Q q R B}.ncard` from non-membership in the
unweighted `weightedDeviation` bad event. -/
private theorem ncard_blockStradEvent_le {β ε : Type*} [Fintype β] [Finite ε]
    {Q : Multigraph β ε} (hloop : Q.Loopless) (hdeg : Q.MaxDegreeLE 3) {q : ℝ} (hq : 0 ≤ q)
    {R : ℕ} {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) {c : ℝ} {ω : β → ℝ × ℝ}
    (hω : ω ∉ weightedDeviation
      (Measure.pi fun _ : β => (gaussianReal 0 1).prod (gaussianReal 0 1))
      Finset.univ 1 (blockStradEvent Q q R) c) :
    ({B : β | ω ∈ blockStradEvent Q q R B}.ncard : ℝ) ≤
      ((Finset.univ.filter fun B : β => (Q.incidenceSet B).ncard = 3).card : ℝ) *
        straddleBound ρ₀ + c := by
  classical
  set P := Measure.pi fun _ : β => (gaussianReal 0 1).prod (gaussianReal 0 1)
  simp only [weightedDeviation, mem_ofPred_eq, not_le, Pi.one_apply, one_mul] at hω
  have hmean_le : ∑ B : β, P.real (blockStradEvent Q q R B) ≤
      ((Finset.univ.filter fun B : β => (Q.incidenceSet B).ncard = 3).card : ℝ) *
        straddleBound ρ₀ := by
    calc ∑ B : β, P.real (blockStradEvent Q q R B)
        ≤ ∑ B : β, if (Q.incidenceSet B).ncard = 3 then straddleBound ρ₀ else 0 :=
          Finset.sum_le_sum fun B _ => measureReal_blockStradEvent_le hloop hdeg hq hρ₀ hρ B
      _ = ((Finset.univ.filter fun B : β => (Q.incidenceSet B).ncard = 3).card : ℝ) *
          straddleBound ρ₀ := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [← ncard_eq_sum_indicator] at hω
  linarith only [(abs_lt.mp hω).2, hmean_le]

/-! #### Saturated compression counts and lifted block weights -/

/-- Low-degree (`1 ≤ deg ≤ 2`) and degree-`3` block count bounds for a saturated weight-capped
compression of `G.induce X` with vertex weights `w x = 1 + |inc_G(x) ∩ ∂X|`. -/
private theorem saturated_block_count_bounds {V E : Type*} [Finite V] [Finite E]
    {G : Multigraph V E} (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {X : Set V} [Fintype X] (hH_min : ∀ x : X, 2 ≤ ((G.induce X).incidenceSet x).ncard)
    (hH_hand : 2 * Nat.card {e : E // G.src e ∈ X ∧ G.tgt e ∈ X} + (G.edgeCut X).ncard =
      3 * Nat.card X)
    (hH_cut_sum : ∑ x : X, (G.incidenceSet x.1 ∩ G.edgeCut X).ncard = (G.edgeCut X).ncard)
    {M : ℕ} (hM : 0 < M)
    {cmp : CappedCompression (G.induce X)
      (fun x : X => 1 + (G.incidenceSet x.1 ∩ G.edgeCut X).ncard) 3 M}
    (hsat : cmp.Saturated) :
    let Q := cmp.quotient
    let Lset := Finset.univ.filter fun B : cmp.blocks =>
      1 ≤ (Q.incidenceSet B).ncard ∧ (Q.incidenceSet B).ncard ≤ 2
    let Q3set := Finset.univ.filter fun B : cmp.blocks => (Q.incidenceSet B).ncard = 3
    (Lset.card : ℝ) ≤ 32 / (M : ℝ) * (Nat.card V : ℝ) ∧
      (Q3set.card : ℝ) + ((G.edgeCut X).ncard : ℝ) ≤ (X.ncard : ℝ) + (Lset.card : ℝ) := by
  classical
  have := Fintype.ofFinite E
  have hH_loop : (G.induce X).Loopless := fun e he => hloop e.1 (congrArg Subtype.val he)
  have hcard_X : Nat.card X = X.ncard := Nat.card_coe_set_eq X
  have hsum_w_le : ∑ x : X, (1 + (G.incidenceSet x.1 ∩ G.edgeCut X).ncard) ≤ 4 * Nat.card V := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card, hcard_X, hH_cut_sum]
    have hE := two_mul_card_edges_eq_cubic hloop h3
    have hcut_le : (G.edgeCut X).ncard ≤ Nat.card E := ncard_le_card _
    have hX_le : X.ncard ≤ Nat.card V := ncard_le_card X
    omega
  refine ⟨?_, ?_⟩
  · have hsat_bound := hsat.mul_card_deg_one_two_le
    rw [div_mul_eq_mul_div, le_div_iff₀ (Nat.cast_pos.mpr hM)]
    exact_mod_cast (by linarith : _ * M ≤ 32 * Nat.card V)
  · have hdeg3 := cmp.card_deg_three_add_le_of_two_le_deg hH_loop hH_min hH_hand
    have hQ1_sub : (Finset.univ.filter fun B : cmp.blocks =>
        (cmp.quotient.incidenceSet B).ncard = 1).card ≤
        (Finset.univ.filter fun B : cmp.blocks =>
          1 ≤ (cmp.quotient.incidenceSet B).ncard ∧
            (cmp.quotient.incidenceSet B).ncard ≤ 2).card :=
      Finset.card_le_card fun B hB => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
        omega
    rw [hcard_X] at hdeg3
    exact_mod_cast (by omega :
      (Finset.univ.filter fun B : cmp.blocks =>
        (cmp.quotient.incidenceSet B).ncard = 3).card + (G.edgeCut X).ncard ≤ X.ncard + _)

/-- Number of vertices in a compression block `B`, as a real weight. -/
private noncomputable def blockVertexWeight {V E : Type*} {G : Multigraph V E} {X : Set V}
    [Fintype X] {w : X → ℕ} {d M : ℕ} (cmp : CappedCompression (G.induce X) w d M)
    (B : cmp.blocks) : ℝ :=
  open Classical in
  ((Finset.univ.filter fun x : X => cmp.blockOf x = B).card : ℝ)

/-- Number of `G.edgeCut X` boundary edges incident to a compression block `B`, as a real
weight. -/
private noncomputable def blockCutWeight {V E : Type*} {G : Multigraph V E} {X : Set V}
    [Fintype X] {w : X → ℕ} {d M : ℕ} (cmp : CappedCompression (G.induce X) w d M)
    (B : cmp.blocks) : ℝ :=
  open Classical in
  ((∑ x ∈ Finset.univ.filter (fun x : X => cmp.blockOf x = B),
    (G.incidenceSet x.1 ∩ G.edgeCut X).ncard : ℕ) : ℝ)

/-- Bounds and sum identity for `blockVertexWeight`. -/
private theorem blockVertexWeight_spec {V E : Type*} {G : Multigraph V E} {X : Set V}
    [Fintype X] {M : ℕ}
    (cmp : CappedCompression (G.induce X)
      (fun x : X => 1 + (G.incidenceSet x.1 ∩ G.edgeCut X).ncard) 3 M) :
    (∀ B : cmp.blocks, 0 ≤ blockVertexWeight cmp B ∧ blockVertexWeight cmp B ≤ M) ∧
      ∑ B : cmp.blocks, blockVertexWeight cmp B = (X.ncard : ℝ) := by
  classical
  have hcard_eq (B : cmp.blocks) :
      (Finset.univ.filter fun x : X => cmp.blockOf x = B).card = ({x : X | x ∈ B.1}).ncard := by
    rw [← ncard_coe_finset]; congr 1; ext x; simp [cmp.mem_iff_blockOf_eq]
  refine ⟨fun B => ⟨Nat.cast_nonneg _, ?_⟩, ?_⟩
  · refine Nat.cast_le.mpr (le_trans ?_ (cmp.blockWeight_le B))
    rw [hcard_eq B, cmp.ncard_block_eq_length B, CappedCompression.blockWeight]
    exact (by simp : B.1.length = (B.1.map fun _ => 1).sum) ▸
      List.sum_le_sum (l := B.1) (f := fun _ => 1)
        (g := fun x : X => 1 + (G.incidenceSet x.1 ∩ G.edgeCut X).ncard)
        fun _ _ => Nat.le_add_right _ _
  · simp only [blockVertexWeight]
    rw [← Nat.cast_sum, Finset.sum_card_fiberwise_eq_card_filter,
      Finset.filter_true_of_mem fun _ _ => Finset.mem_univ _, Finset.card_univ,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

/-- Bounds and sum identity for `blockCutWeight`. -/
private theorem blockCutWeight_spec {V E : Type*} {G : Multigraph V E} {X : Set V}
    [Fintype X] {M : ℕ}
    (cmp : CappedCompression (G.induce X)
      (fun x : X => 1 + (G.incidenceSet x.1 ∩ G.edgeCut X).ncard) 3 M)
    (hcut_sum : ∑ x : X, (G.incidenceSet x.1 ∩ G.edgeCut X).ncard = (G.edgeCut X).ncard) :
    (∀ B : cmp.blocks, 0 ≤ blockCutWeight cmp B ∧ blockCutWeight cmp B ≤ M) ∧
      ∑ B : cmp.blocks, blockCutWeight cmp B = ((G.edgeCut X).ncard : ℝ) := by
  classical
  refine ⟨fun B => ⟨Nat.cast_nonneg _, ?_⟩, ?_⟩
  · have hfin : B.1.toFinset = Finset.univ.filter (fun x : X => cmp.blockOf x = B) := by
      ext x; simp [cmp.mem_iff_blockOf_eq]
    have hle : (∑ x ∈ Finset.univ.filter (fun x : X => cmp.blockOf x = B),
        (G.incidenceSet x.1 ∩ G.edgeCut X).ncard) ≤ cmp.blockWeight B := by
      rw [CappedCompression.blockWeight, ← List.sum_toFinset _ (cmp.nodup B.1 B.2), hfin]
      exact Finset.sum_le_sum fun _ _ => Nat.le_add_left _ _
    exact Nat.cast_le.mpr (hle.trans (cmp.blockWeight_le B))
  · simp only [blockCutWeight]
    rw [← Nat.cast_sum, Finset.sum_fiberwise, hcut_sum]

/-- Vertex count of the lift `Subtype.val '' (cmp.blockOf ⁻¹' {B | ω ∈ A B})` as an
indicator-weighted sum of `blockVertexWeight`. -/
private theorem ncard_lifted_eq_sum_vertexWeight {V E Ω : Type*} {G : Multigraph V E}
    {X : Set V} [Fintype X] {w : X → ℕ} {d M : ℕ}
    (cmp : CappedCompression (G.induce X) w d M) (A : cmp.blocks → Set Ω) (ω : Ω) :
    ((Subtype.val '' (cmp.blockOf ⁻¹' {B : cmp.blocks | ω ∈ A B})).ncard : ℝ) =
      ∑ B : cmp.blocks, blockVertexWeight cmp B * (A B).indicator 1 ω := by
  classical
  set S : Set cmp.blocks := {B | ω ∈ A B}
  rw [ncard_image_of_injective _ Subtype.val_injective]
  have hpre_fin : (cmp.blockOf ⁻¹' S).ncard =
      ∑ B ∈ Finset.univ.filter (· ∈ S),
        (Finset.univ.filter fun x : X => cmp.blockOf x = B).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter, ← ncard_coe_finset]
    congr 1; ext x; simp
  rw [hpre_fin]
  push_cast
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun B _ => ?_
  dsimp [blockVertexWeight]
  by_cases hB : ω ∈ A B <;> simp [S, hB]

/-- Boundary-edge count `{e ∈ ∂X | endIn G X e ∈ X₁}` for a lifted block set `X₁` as an
indicator-weighted sum of `blockCutWeight`. -/
private theorem ncard_endIn_lifted_eq_sum_cutWeight {V E Ω : Type*} [Finite E]
    {G : Multigraph V E} {X : Set V} [Fintype X] {w : X → ℕ} {d M : ℕ}
    (cmp : CappedCompression (G.induce X) w d M) (A : cmp.blocks → Set Ω) (ω : Ω) :
    ({e ∈ G.edgeCut X | endIn G X e ∈
        Subtype.val '' (cmp.blockOf ⁻¹' {B : cmp.blocks | ω ∈ A B})}.ncard : ℝ) =
      ∑ B : cmp.blocks, blockCutWeight cmp B * (A B).indicator 1 ω := by
  classical
  have := Fintype.ofFinite E
  set S : Set cmp.blocks := {B | ω ∈ A B}
  have hpart_cut : {e ∈ G.edgeCut X | endIn G X e ∈ Subtype.val '' (cmp.blockOf ⁻¹' S)}.ncard =
      ∑ x ∈ Finset.univ.filter (fun x : X => cmp.blockOf x ∈ S),
        (G.incidenceSet x.1 ∩ G.edgeCut X).ncard := by
    have h1 (x : X) : (G.incidenceSet x.1 ∩ G.edgeCut X).ncard =
        (Finset.univ.filter fun e : E => e ∈ G.incidenceSet x.1 ∧ e ∈ G.edgeCut X).card := by
      rw [← ncard_coe_finset]; congr 1; ext e; simp
    simp_rw [h1]
    rw [← Finset.card_biUnion]
    · rw [← ncard_coe_finset]
      congr 1; ext e
      simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
        true_and, mem_ofPred_eq]
      constructor
      · rintro ⟨heCut, x, hxS, heqx⟩
        obtain ⟨hm, hinc, _⟩ := endIn_mem heCut
        have hxeq : x = ⟨endIn G X e, hm⟩ := Subtype.ext heqx
        subst hxeq
        exact ⟨⟨endIn G X e, hm⟩, hxS, hinc, heCut⟩
      · rintro ⟨x, hxS, hinc, heCut⟩
        obtain ⟨_, _, hunq⟩ := endIn_mem heCut
        exact ⟨heCut, x, hxS, hunq x.1 x.2 hinc⟩
    · intro x₁ _ x₂ _ hne
      refine Finset.disjoint_left.mpr fun e h1' h2' => hne ?_
      obtain ⟨hi1, hc1⟩ := (Finset.mem_filter.mp h1').2
      obtain ⟨hi2, _⟩ := (Finset.mem_filter.mp h2').2
      obtain ⟨_, _, hunq⟩ := endIn_mem hc1
      exact Subtype.ext ((hunq x₁.1 x₁.2 hi1).trans (hunq x₂.1 x₂.2 hi2).symm)
  rw [hpart_cut]
  have hgrp : (Finset.univ.filter fun x : X => cmp.blockOf x ∈ S) =
      {x ∈ (Finset.univ : Finset X) | cmp.blockOf x ∈ Finset.univ.filter (· ∈ S)} := by
    ext x; simp
  rw [hgrp, ← Finset.sum_fiberwise_eq_sum_filter]
  push_cast
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun B _ => ?_
  dsimp [blockCutWeight]
  by_cases hB : ω ∈ A B <;> simp [S, hB]

/-- Internal edge-cut size in `G.induce X` of a lifted block set `Subtype.val ''` matches the
quotient edge cut `(cmp.quotient.edgeCut S).ncard`. -/
private theorem ncard_edgeCut_lifted_eq {V E : Type*} {G : Multigraph V E}
    {X : Set V} {w : X → ℕ} {d M : ℕ}
    (cmp : CappedCompression (G.induce X) w d M) (S : Set cmp.blocks) :
    ((G.induce X).edgeCut {x : X | x.1 ∈ Subtype.val '' (cmp.blockOf ⁻¹' S)}).ncard =
      (cmp.quotient.edgeCut S).ncard := by
  have hset : {x : X | x.1 ∈ Subtype.val '' (cmp.blockOf ⁻¹' S)} = cmp.blockOf ⁻¹' S := by
    ext x
    exact ⟨by rintro ⟨x', hx', heq⟩; rwa [← Subtype.ext heq], fun hx => ⟨x, hx, rfl⟩⟩
  rw [hset, cmp.ncard_edgeCut_preimage]

/-! #### Depth-one bisection inequality and assembly -/

/-- Algebraic reduction bounding the real quotient cut against `lyap gaussianCoefficient G X` minus
the half-boundary share and slack `η * h`. -/
private theorem quotient_cut_add_slack_le_lyap {qCut lCard q3Card xCard cutX sBound δ M η h : ℝ}
    (hδ : 0 < δ) (hh_pos : 0 < h) (hM_pos : 0 < M) (hM_real : 768 / δ ≤ M) (hηδ : η ≤ δ / 16)
    (hstrad : sBound ≤ gaussianCoefficient + δ / 8)
    (hL_nonneg : 0 ≤ lCard) (hq3_nonneg : 0 ≤ q3Card) (hq3_le_h : q3Card ≤ h)
    (hL_le : lCard ≤ 32 / M * h) (hq3_le : q3Card + cutX ≤ xCard + lCard)
    (hqCut : qCut ≤ 2 * lCard + (q3Card * sBound + η * h)) :
    qCut + (1 / 2 * cutX + η * h) ≤
      gaussianCoefficient * xCard + (1 / 2 - gaussianCoefficient) * cutX + δ / 2 * h := by
  have hp_pos := gaussianCoefficient_pos
  have hp_lt1 : gaussianCoefficient ≤ 1 :=
    gaussianCoefficient_lt_three_twentieths.le.trans (by norm_num)
  have hprod : q3Card * sBound ≤ q3Card * gaussianCoefficient + δ / 8 * h := by
    linarith only [mul_le_mul_of_nonneg_left hstrad hq3_nonneg,
      mul_le_mul_of_nonneg_right hq3_le_h (by positivity : (0 : ℝ) ≤ δ / 8)]
  have hq3_p : q3Card * gaussianCoefficient ≤ (xCard - cutX) * gaussianCoefficient + lCard := by
    have hmul := mul_le_mul_of_nonneg_right
      (by linarith only [hq3_le] : q3Card ≤ xCard - cutX + lCard) hp_pos.le
    have hL1 : lCard * gaussianCoefficient ≤ lCard := mul_le_of_le_one_right hL_nonneg hp_lt1
    linarith only [hmul, hL1]
  have h32 : 3 * (32 / M) ≤ δ / 8 := by
    rw [mul_div_assoc', div_le_iff₀ hM_pos]
    have hm := mul_le_mul_of_nonneg_left hM_real hδ.le
    rw [mul_div_cancel₀ _ hδ.ne'] at hm
    linarith only [hm]
  have hslack : (δ / 8 + 3 * (32 / M) + 2 * η) * h ≤ δ / 2 * h :=
    mul_le_mul_of_nonneg_right (by linarith only [h32, hηδ, hδ]) hh_pos.le
  linarith only [hqCut, hprod, hq3_p, hL_le, hslack]

/-- **Depth-one `CappedCompression` bisection.** For a subset `X ⊆ V` of a loopless cubic
multigraph `G` where every vertex in `X` has at most one incident edge in `G.edgeCut X`, a
weight-capped compression of `G.induce X` followed by a symmetric (`t = 0`) Gaussian cut bisects
`X = X₁ ⊔ X₂` with `|X_i| ≤ |X| / 2 + η |V|` and
`|G.edgeCut X_i| ≤ lyap p G X + (δ / 2) |V|`. -/
private theorem bisect_compressed_zero {V E : Type*} [Finite V] [Finite E] {G : Multigraph V E}
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {q : ℝ} (hq : 0 ≤ q) {R : ℕ} {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    {δ : ℝ} (hδ : 0 < δ) (hstrad : straddleBound ρ₀ ≤ gaussianCoefficient + δ / 8)
    {M : ℕ} (hM2 : 2 ≤ M) (hM_real : 768 / δ ≤ (M : ℝ))
    {η : ℝ} (hη : 0 < η) (hηδ : η ≤ δ / 16)
    (large : 4 * (M : ℝ) ^ 2 * (vertexOverlap 3 R : ℝ) / η ^ 2 < Nat.card V)
    (X : Set V) (hminX : ∀ v ∈ X, (G.incidenceSet v ∩ G.edgeCut X).ncard ≤ 1) :
    ∃ X₁ X₂ : Set V, Disjoint X₁ X₂ ∧ X₁ ∪ X₂ = X ∧
      (X₁.ncard : ℝ) ≤ 1 / 2 * (X.ncard : ℝ) + η * Nat.card V ∧
      (X₂.ncard : ℝ) ≤ 1 / 2 * (X.ncard : ℝ) + η * Nat.card V ∧
      ((G.edgeCut X₁).ncard : ℝ) ≤ lyap gaussianCoefficient G X + δ / 2 * Nat.card V ∧
      ((G.edgeCut X₂).ncard : ℝ) ≤ lyap gaussianCoefficient G X + δ / 2 * Nat.card V := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  have := Fintype.ofFinite X
  set h : ℝ := (Nat.card V : ℝ)
  have hh_pos : 0 < h := lt_of_le_of_lt (by positivity) large
  set H := G.induce X
  obtain ⟨hH_deg_eq, hH_hand, hH_cut_sum⟩ := induce_degree_and_handshake hloop h3 X
  have hH_max : H.MaxDegreeLE 3 := fun x => by
    have h1 : (H.incidenceSet x).ncard + (G.incidenceSet x.1 ∩ G.edgeCut X).ncard = 3 := hH_deg_eq x
    omega
  have hH_min : ∀ x : X, 2 ≤ (H.incidenceSet x).ncard := fun x => by
    have h1 : (H.incidenceSet x).ncard + (G.incidenceSet x.1 ∩ G.edgeCut X).ncard = 3 := hH_deg_eq x
    have h2 := hminX x.1 x.2
    omega
  let w : X → ℕ := fun x => 1 + (G.incidenceSet x.1 ∩ G.edgeCut X).ncard
  have hw_le_M : ∀ x : X, w x ≤ M := fun x => by
    have := hminX x.1 x.2; dsimp [w]; omega
  obtain ⟨cmp, hsat⟩ := CappedCompression.exists_saturated (d := 3) (M := M) hH_max hw_le_M
  set Q := cmp.quotient
  have hcards_le_h : (Fintype.card cmp.blocks : ℝ) ≤ h := by
    have hblocks_le : cmp.blocks.card ≤ X.ncard := Nat.card_coe_set_eq X ▸ cmp.card_blocks_le
    rw [Fintype.card_coe]
    exact Nat.cast_le.mpr (hblocks_le.trans (ncard_le_card X))
  obtain ⟨hL_le, hQ3_le⟩ :=
    saturated_block_count_bounds hloop h3 hH_min hH_hand hH_cut_sum (by omega) hsat
  obtain ⟨hvWt_le, hvWt_sum⟩ := blockVertexWeight_spec cmp
  obtain ⟨hbWt_le, hbWt_sum⟩ := blockCutWeight_spec cmp hH_cut_sum
  obtain ⟨ω, hωV, hωB, hωS⟩ := exists_concentrated_blockSample cmp.quotient_maxDegreeLE q R
    (by exact_mod_cast (by omega : 1 ≤ M)) hη hcards_le_h large hvWt_le hbWt_le
  set S_Q : Set cmp.blocks := {B | ω ∈ blockSideEvent Q q R B}
  set X₁ : Set V := Subtype.val '' (cmp.blockOf ⁻¹' S_Q)
  set X₂ : Set V := Subtype.val '' (cmp.blockOf ⁻¹' S_Qᶜ)
  have hX₁_sub : X₁ ⊆ X := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hX₂_sub : X₂ ⊆ X := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hdisjX : Disjoint X₁ X₂ := disjoint_left.mpr fun _ ⟨x₁, hx₁, h1⟩ ⟨x₂, hx₂, h2⟩ =>
    hx₂ (Subtype.ext (h1.trans h2.symm) ▸ hx₁)
  have hunionX : X₁ ∪ X₂ = X := by
    ext v
    refine ⟨by rintro (hv | hv); exacts [hX₁_sub hv, hX₂_sub hv], fun hv => ?_⟩
    by_cases hB : cmp.blockOf ⟨v, hv⟩ ∈ S_Q
    · exact Or.inl ⟨⟨v, hv⟩, hB, rfl⟩
    · exact Or.inr ⟨⟨v, hv⟩, hB, rfl⟩
  have hprob (B : cmp.blocks) :
      (Measure.pi fun _ : cmp.blocks => (gaussianReal 0 1).prod (gaussianReal 0 1)).real
        (blockSideEvent Q q R B) = 1 / 2 :=
    measureReal_blockSideEvent_eq_half cmp.quotient_loopless cmp.quotient_maxDegreeLE hq hρ₀ hρ B
  have habs_of_sum {f : cmp.blocks → ℝ} {total : ℝ} (hsum : ∑ B, f B = total)
      (hω : ω ∉ weightedDeviation
        (Measure.pi fun _ : cmp.blocks => (gaussianReal 0 1).prod (gaussianReal 0 1))
        Finset.univ f (blockSideEvent Q q R) (η * h)) :
      |∑ B : cmp.blocks, f B * (blockSideEvent Q q R B).indicator 1 ω - 1 / 2 * total| < η * h := by
    have hmean : ∑ B : cmp.blocks, f B *
        (Measure.pi fun _ : cmp.blocks => (gaussianReal 0 1).prod (gaussianReal 0 1)).real
          (blockSideEvent Q q R B) = 1 / 2 * total := by
      simp_rw [hprob, ← Finset.sum_mul, hsum]; ring
    rw [← hmean]
    exact not_le.mp hω
  have hv_abs : |(X₁.ncard : ℝ) - 1 / 2 * (X.ncard : ℝ)| < η * h := by
    rw [ncard_lifted_eq_sum_vertexWeight cmp (blockSideEvent Q q R) ω]
    exact habs_of_sum hvWt_sum hωV
  have hb_abs : |({e ∈ G.edgeCut X | endIn G X e ∈ X₁}.ncard : ℝ) -
      1 / 2 * ((G.edgeCut X).ncard : ℝ)| < η * h := by
    rw [ncard_endIn_lifted_eq_sum_cutWeight cmp (blockSideEvent Q q R) ω]
    exact habs_of_sum hbWt_sum hωB
  obtain ⟨hX₁_sz, hX₂_sz⟩ := le_half_add_of_abs_lt (ncard_eq_sub_of_union hdisjX hunionX) hv_abs
  obtain ⟨hbdry1_le, hbdry2_le⟩ :=
    le_half_add_of_abs_lt (ncard_edgeCut_endIn_eq_sub hdisjX hunionX) hb_abs
  have hqCut_le : ((Q.edgeCut S_Q).ncard : ℝ) ≤
      2 * ((Finset.univ.filter fun B : cmp.blocks =>
          1 ≤ (Q.incidenceSet B).ncard ∧ (Q.incidenceSet B).ncard ≤ 2).card : ℝ) +
        (((Finset.univ.filter fun B : cmp.blocks =>
          (Q.incidenceSet B).ncard = 3).card : ℝ) * straddleBound ρ₀ + η * h) := by
    have hnat : ((Q.edgeCut S_Q).ncard : ℝ) ≤
        ((2 * (Finset.univ.filter fun B : cmp.blocks =>
            1 ≤ (Q.incidenceSet B).ncard ∧ (Q.incidenceSet B).ncard ≤ 2).card +
          {B : cmp.blocks | ω ∈ blockStradEvent Q q R B}.ncard : ℕ) : ℝ) :=
      Nat.cast_le.mpr (ncard_edgeCut_blockSideEvent_le cmp.quotient_maxDegreeLE q R ω)
    have hst := ncard_blockStradEvent_le cmp.quotient_loopless cmp.quotient_maxDegreeLE hq hρ₀
      hρ hωS
    push_cast at hnat
    linarith only [hnat, hst]
  have hq3_le_h : ((Finset.univ.filter fun B : cmp.blocks =>
      (Q.incidenceSet B).ncard = 3).card : ℝ) ≤ h :=
    (Nat.cast_le.mpr ((Finset.card_filter_le _ _).trans_eq (by simp))).trans hcards_le_h
  have hlyap_comb := quotient_cut_add_slack_le_lyap hδ hh_pos (by positivity) hM_real hηδ hstrad
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hq3_le_h hL_le hQ3_le hqCut_le
  have cut_side {Z : Set V} (hZ : Z ⊆ X)
      (hint : (H.edgeCut {x : X | x.1 ∈ Z}).ncard = (Q.edgeCut S_Q).ncard)
      (hbd : ({e ∈ G.edgeCut X | endIn G X e ∈ Z}.ncard : ℝ) ≤
        1 / 2 * ((G.edgeCut X).ncard : ℝ) + η * h) :
      ((G.edgeCut Z).ncard : ℝ) ≤ lyap gaussianCoefficient G X + δ / 2 * h := by
    rw [ncard_edgeCut_sub_cast_eq hZ, hint]
    change _ ≤ gaussianCoefficient * (X.ncard : ℝ) +
      (1 / 2 - gaussianCoefficient) * ((G.edgeCut X).ncard : ℝ) + δ / 2 * h
    linarith only [hbd, hlyap_comb]
  refine ⟨X₁, X₂, hdisjX, hunionX, hX₁_sz, hX₂_sz,
    cut_side hX₁_sub (ncard_edgeCut_lifted_eq cmp S_Q) hbdry1_le,
    cut_side hX₂_sub ?_ hbdry2_le⟩
  rw [ncard_edgeCut_lifted_eq cmp S_Qᶜ, Q.edgeCut_compl]

end DepthOne

/-! ### Depths two through five (`t = 0` subset bisections on `G`) and leaf peeling -/

section DeeperLevels

/-- The number of indices in `F` whose event holds at `ω`, as a sum of indicators over `F`. -/
private theorem ncard_mem_and_eq_sum_indicator {κ Ω : Type*} (F : Finset κ) (A : κ → Set Ω)
    (ω : Ω) : ({k | k ∈ F ∧ ω ∈ A k}.ncard : ℝ) = ∑ k ∈ F, (A k).indicator (1 : Ω → ℝ) ω := by
  classical
  simp only [Set.indicator_apply, Pi.one_apply, Finset.sum_boole]
  rw [← ncard_coe_finset, Finset.coe_filter]

/-- **Single-step `t = 0` subset bisection on `G`.** Any subset `Y ⊆ V` of a large loopless cubic
multigraph `G` splits into `Y₁ ⊔ Y₂` with `|Y_i| ≤ |Y| / 2 + η |V|` and
`|G.edgeCut Y_i| ≤ straddleBound ρ₀ * |Y| + |G.edgeCut Y| / 2 + 2 η |V|`. -/
private theorem bisect_subset_zero {V E : Type*} [Finite V] [Finite E] {G : Multigraph V E}
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {q : ℝ} (hq : 0 ≤ q) {R : ℕ} {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    {η : ℝ} (hη : 0 < η)
    (large : 5 * (vertexOverlap 3 (R + 1) : ℝ) / η ^ 2 < Nat.card V) (Y : Set V) :
    ∃ Y₁ Y₂ : Set V, Disjoint Y₁ Y₂ ∧ Y₁ ∪ Y₂ = Y ∧
      (Y₁.ncard : ℝ) ≤ 1 / 2 * (Y.ncard : ℝ) + η * Nat.card V ∧
      (Y₂.ncard : ℝ) ≤ 1 / 2 * (Y.ncard : ℝ) + η * Nat.card V ∧
      ((G.edgeCut Y₁).ncard : ℝ) ≤
        straddleBound ρ₀ * (Y.ncard : ℝ) + 1 / 2 * ((G.edgeCut Y).ncard : ℝ) +
          2 * η * Nat.card V ∧
      ((G.edgeCut Y₂).ncard : ℝ) ≤
        straddleBound ρ₀ * (Y.ncard : ℝ) + 1 / 2 * ((G.edgeCut Y).ncard : ℝ) +
          2 * η * Nat.card V := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  set h : ℝ := (Nat.card V : ℝ)
  have hh_pos : 0 < h := lt_of_le_of_lt (by positivity) large
  have hdeg : G.MaxDegreeLE 3 := fun v => (h3 v).le
  set P := Measure.pi fun _ : V => gaussianReal 0 1
  set c : ℝ := η * h
  have hc_pos : 0 < c := by positivity
  set D := vertexOverlap 3 (R + 1)
  have hR_sub (v : V) :
      closedBall G.toSimpleGraph v (R + 1) ⊆ closedBall G.toSimpleGraph v (R + 1 + 1) :=
    fun _ (hz : G.toSimpleGraph.edist v _ ≤ _) => hz.trans (Nat.cast_le.mpr (Nat.le_succ _))
  -- Three families on `Y`, `G.edgeCut Y`, and `Y` straddling `0`.
  set Fv := Y.toFinset
  set Fe := (G.edgeCut Y).toFinset
  let Av : V → Set (V → ℝ) := fun v => {ω | v ∈ lowSide G (edgeScore G q R ω) 0}
  let Ae : E → Set (V → ℝ) := fun e => {ω | endIn G Y e ∈ lowSide G (edgeScore G q R ω) 0}
  let As : V → Set (V → ℝ) := fun v => straddleEvent G q R 0 v
  have hAe_dep (e : E) :
      DependsOn (· ∈ Ae e) (closedBall G.toSimpleGraph (G.src e) (R + 1 + 1)) := by
    intro ω₁ ω₂ hω
    refine dependsOn_lowSide G q R 0 (endIn G Y e) fun z hz => hω z ?_
    dsimp only [endIn] at hz
    split_ifs at hz
    · exact hR_sub _ hz
    · exact closedBall_tgt_subset e (R + 1) hz
  have hball_V (v : V) :
      (Fv.filter fun w =>
        ¬Disjoint (closedBall G.toSimpleGraph v (R + 1 + 1))
          (closedBall G.toSimpleGraph w (R + 1 + 1))).card ≤ D :=
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ Fv))).trans
      (card_not_disjoint_closedBall_le hdeg (by norm_num) (R + 1) v)
  have hball_E (e : E) :
      (Fe.filter fun l =>
        ¬Disjoint (closedBall G.toSimpleGraph (G.src e) (R + 1 + 1))
          (closedBall G.toSimpleGraph (G.src l) (R + 1 + 1))).card ≤ D :=
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ Fe))).trans
      (card_not_disjoint_closedBall_src_le hdeg (R + 1) e)
  have hdevV : P.real (weightedDeviation P Fv 1 Av c) ≤ (Fv.card : ℝ) * 1 ^ 2 * D / c ^ 2 :=
    measureReal_weightedDeviation_le Fv (fun v _ => measurableSet_lowSide G q R 0 v)
      (fun _ _ => zero_le_one) (fun _ _ => le_rfl) _
      (fun v _ ω₁ ω₂ hω => dependsOn_lowSide G q R 0 v fun z hz => hω z (hR_sub v hz))
      (fun v _ => hball_V v) hc_pos
  have hdevE : P.real (weightedDeviation P Fe 1 Ae c) ≤ (Fe.card : ℝ) * 1 ^ 2 * D / c ^ 2 :=
    measureReal_weightedDeviation_le Fe
      (fun e _ => measurableSet_lowSide G q R 0 (endIn G Y e))
      (fun _ _ => zero_le_one) (fun _ _ => le_rfl) _ (fun e _ => hAe_dep e)
      (fun e _ => hball_E e) hc_pos
  have hdevS : P.real (weightedDeviation P Fv 1 As c) ≤ (Fv.card : ℝ) * 1 ^ 2 * D / c ^ 2 :=
    measureReal_weightedDeviation_le Fv (fun v _ => measurableSet_straddleEvent q R 0 v)
      (fun _ _ => zero_le_one) (fun _ _ => le_rfl) _
      (fun v _ ω₁ ω₂ hω => dependsOn_straddleEvent q R 0 v fun z hz => hω z (hR_sub v hz))
      (fun v _ => hball_V v) hc_pos
  have hFv_le : (Fv.card : ℝ) ≤ h := by
    rw [← Set.ncard_eq_toFinset_card']
    exact Nat.cast_le.mpr (ncard_le_card Y)
  have hFe_le : (Fe.card : ℝ) ≤ 3 / 2 * h := by
    have h2r : (2 * (G.edgeCut Y).ncard : ℝ) ≤ 3 * Nat.card V := by
      exact_mod_cast (Nat.mul_le_mul_left 2 (ncard_le_card (G.edgeCut Y))).trans
        (two_mul_card_edges_eq_cubic hloop h3).le
    rw [← Set.ncard_eq_toFinset_card']
    linarith only [h2r, (rfl : h = (Nat.card V : ℝ))]
  obtain ⟨ω, hω⟩ := exists_notMem_of_measureReal_lt_one (((measureReal_union_le _ _).trans
    (add_le_add ((measureReal_union_le _ _).trans (add_le_add hdevV hdevE)) hdevS)).trans_lt
    (by
      calc _ ≤ 7 / 2 * D * h / c ^ 2 := by
            rw [one_pow, mul_one, mul_one, ← add_div, ← add_div]
            gcongr
            nlinarith only [hFv_le, hFe_le, (Nat.cast_nonneg D : (0 : ℝ) ≤ D)]
        _ < 1 := mul_div_mul_sq_lt_one hη.ne' hh_pos
          ((by gcongr; norm_num : 7 / 2 * (D : ℝ) / η ^ 2 ≤ _).trans_lt large)))
  simp only [mem_union, not_or, weightedDeviation, mem_ofPred_eq, not_le, Pi.one_apply,
    one_mul] at hω
  obtain ⟨⟨hωV, hωE⟩, hωS⟩ := hω
  set L0 := lowSide G (edgeScore G q R ω) 0
  set Y₁ := Y ∩ L0
  set Y₂ := Y \ L0
  have hdisjY : Disjoint Y₁ Y₂ := disjoint_left.mpr fun _ h1 h2 => h2.2 h1.2
  have hunionY : Y₁ ∪ Y₂ = Y := inter_union_sdiff Y L0
  -- Vertex sizes of `Y₁` and `Y₂`.
  have hmeanV : ∑ v ∈ Fv, P.real (Av v) = 1 / 2 * (Y.ncard : ℝ) := by
    have hpv (v : V) : P.real (Av v) = 1 / 2 :=
      measureReal_lowSide_zero_eq_half hloop hdeg hq (by linarith only [hρ₀]) hρ (h3 v)
    simp_rw [hpv]
    rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card']
    ring
  have hv_abs : |(Y₁.ncard : ℝ) - 1 / 2 * (Y.ncard : ℝ)| < c := by
    have hY₁ : Y₁ = {v | v ∈ Fv ∧ ω ∈ Av v} := by ext v; simp [Y₁, L0, Fv, Av]
    rwa [hY₁, ncard_mem_and_eq_sum_indicator, ← hmeanV]
  have hY₂_eq : (Y₂.ncard : ℝ) = (Y.ncard : ℝ) - (Y₁.ncard : ℝ) :=
    ncard_eq_sub_of_union hdisjY hunionY
  -- External boundary edges of `Y` landing in `Y₁` and `Y₂`.
  have hmeanE : ∑ e ∈ Fe, P.real (Ae e) = 1 / 2 * ((G.edgeCut Y).ncard : ℝ) := by
    have hpe (e : E) : P.real (Ae e) = 1 / 2 :=
      measureReal_lowSide_zero_eq_half hloop hdeg hq (by linarith only [hρ₀]) hρ (h3 (endIn G Y e))
    simp_rw [hpe]
    rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card']
    ring
  have he_abs : |({e ∈ G.edgeCut Y | endIn G Y e ∈ Y₁}.ncard : ℝ) -
      1 / 2 * ((G.edgeCut Y).ncard : ℝ)| < c := by
    have hE₁ : {e ∈ G.edgeCut Y | endIn G Y e ∈ Y₁} = {e | e ∈ Fe ∧ ω ∈ Ae e} := by
      ext e
      simp only [Fe, Set.mem_toFinset, mem_ofPred_eq, Y₁, mem_inter_iff, Ae, L0]
      exact ⟨fun ⟨he, _, hl⟩ => ⟨he, hl⟩, fun ⟨he, hl⟩ => ⟨he, (endIn_mem he).1, hl⟩⟩
    rwa [hE₁, ncard_mem_and_eq_sum_indicator, ← hmeanE]
  have hE₂_eq : ({e ∈ G.edgeCut Y | endIn G Y e ∈ Y₂}.ncard : ℝ) =
      ((G.edgeCut Y).ncard : ℝ) - ({e ∈ G.edgeCut Y | endIn G Y e ∈ Y₁}.ncard : ℝ) :=
    ncard_edgeCut_endIn_eq_sub hdisjY hunionY
  -- Internal cut of `Y` between `Y₁` and `Y₂` injects into `{v ∈ Y | G.EdgeStraddles ... 0 v}`.
  have hint_cut_le : ((G.induce Y).edgeCut {x : Y | x.1 ∈ Y₁}).ncard ≤
      {v : V | v ∈ Y ∧ ω ∈ As v}.ncard := by
    rw [← ncard_image_of_injective _ Subtype.val_injective]
    have hsub : Subtype.val '' (G.induce Y).edgeCut {x : Y | x.1 ∈ Y₁} ⊆
        {e ∈ G.edgeCut L0 | G.src e ∈ Y ∧ G.tgt e ∈ Y} := by
      rintro _ ⟨⟨e, hsY, htY⟩, heCut, rfl⟩
      change ¬(G.src e ∈ Y₁ ↔ G.tgt e ∈ Y₁) at heCut
      simp only [Y₁, mem_inter_iff, hsY, htY, true_and] at heCut
      exact ⟨heCut, hsY, htY⟩
    exact ((ncard_le_ncard hsub (toFinite _)).trans
      (ncard_edgeCut_inter_le_straddling (G := G) (D := Y) (S := L0)
        (fun v _ => h3 v) (edgeScore G q R ω) 0 fun _ _ => Iff.rfl))
  have hstrad_Y : ({v : V | v ∈ Y ∧ ω ∈ As v}.ncard : ℝ) ≤
      straddleBound ρ₀ * (Y.ncard : ℝ) + c := by
    have hmeanS : ∑ v ∈ Fv, P.real (As v) ≤ straddleBound ρ₀ * (Y.ncard : ℝ) :=
      (Finset.sum_le_sum fun v _ => measureReal_straddleEvent_le hloop h3 hq hρ₀ hρ 0 v).trans_eq
        (by rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card', mul_comm])
    have hY : {v : V | v ∈ Y ∧ ω ∈ As v} = {v | v ∈ Fv ∧ ω ∈ As v} := by
      simp only [Fv, Set.mem_toFinset]
    rw [hY, ncard_mem_and_eq_sum_indicator]
    linarith only [(abs_lt.mp hωS).2, hmeanS]
  have hint_cut_compl : ((G.induce Y).edgeCut {x : Y | x.1 ∈ Y₂}).ncard =
      ((G.induce Y).edgeCut {x : Y | x.1 ∈ Y₁}).ncard := by
    have hcompl : {x : Y | x.1 ∈ Y₂} = {x : Y | x.1 ∈ Y₁}ᶜ := by ext x; simp [Y₁, Y₂]
    rw [hcompl, (G.induce Y).edgeCut_compl]
  have hint_real : (((G.induce Y).edgeCut {x : Y | x.1 ∈ Y₁}).ncard : ℝ) ≤
      straddleBound ρ₀ * (Y.ncard : ℝ) + c :=
    (Nat.cast_le.mpr hint_cut_le).trans hstrad_Y
  obtain ⟨hY₁_le, hY₂_le⟩ := le_half_add_of_abs_lt hY₂_eq hv_abs
  obtain ⟨hE₁_le, hE₂_le⟩ := le_half_add_of_abs_lt hE₂_eq he_abs
  have cut_side {Z : Set V} (hZ : Z ⊆ Y)
      (hint : ((G.induce Y).edgeCut {x : Y | x.1 ∈ Z}).ncard =
        ((G.induce Y).edgeCut {x : Y | x.1 ∈ Y₁}).ncard)
      (hbd : ({e ∈ G.edgeCut Y | endIn G Y e ∈ Z}.ncard : ℝ) ≤
        1 / 2 * ((G.edgeCut Y).ncard : ℝ) + c) :
      ((G.edgeCut Z).ncard : ℝ) ≤
        straddleBound ρ₀ * (Y.ncard : ℝ) + 1 / 2 * ((G.edgeCut Y).ncard : ℝ) +
          2 * η * Nat.card V := by
    rw [ncard_edgeCut_sub_cast_eq hZ, hint]
    have hc_eq : c = η * (Nat.card V : ℝ) := rfl
    linarith only [hint_real, hbd, hc_eq]
  exact ⟨Y₁, Y₂, hdisjY, hunionY, hY₁_le, hY₂_le,
    cut_side inter_subset_left rfl hE₁_le, cut_side sdiff_subset hint_cut_compl hE₂_le⟩

/-- Joins two `BinTree.IsPartition` trees for disjoint subsets `Y₁` and `Y₂` with subtree edge cuts
bounded by `C` into one for `Y = Y₁ ∪ Y₂`, given `|G.edgeCut Y| ≤ C`. -/
private theorem joinOpt_isPartition_cut {V E : Type*} {G : Multigraph V E} {C : ℝ}
    {Y₁ Y₂ Y : Set V} (hdisj : Disjoint Y₁ Y₂) (hunion : Y₁ ∪ Y₂ = Y)
    (hcutY : ((G.edgeCut Y).ncard : ℝ) ≤ C) {o₁ o₂ : Option (BinTree V)}
    (ho₁ : match o₁ with
      | none => Y₁ = ∅
      | some t => t.IsPartition Y₁ ∧ ∀ S, t.IsSubtreeSet S → ((G.edgeCut S).ncard : ℝ) ≤ C)
    (ho₂ : match o₂ with
      | none => Y₂ = ∅
      | some t => t.IsPartition Y₂ ∧ ∀ S, t.IsSubtreeSet S → ((G.edgeCut S).ncard : ℝ) ≤ C) :
    match BinTree.joinOpt o₁ o₂ with
    | none => Y = ∅
    | some t => t.IsPartition Y ∧ ∀ S, t.IsSubtreeSet S → ((G.edgeCut S).ncard : ℝ) ≤ C := by
  have hjoin := BinTree.joinOpt_spec hdisj (o₁ := o₁) (o₂ := o₂)
    (by cases h1 : o₁ <;> rw [h1] at ho₁; exacts [ho₁, ho₁.1])
    (by cases h2 : o₂ <;> rw [h2] at ho₂; exacts [ho₂, ho₂.1])
  cases hj : BinTree.joinOpt o₁ o₂ with
  | none => rw [hj] at hjoin; rwa [← hunion]
  | some t =>
    rw [hj, hunion] at hjoin
    refine ⟨hjoin.1, fun S hS => ?_⟩
    rcases hjoin.2 S hS with rfl | ⟨t₁, ht₁, hs₁⟩ | ⟨t₂, ht₂, hs₂⟩
    · exact hcutY
    · rw [ht₁] at ho₁; exact ho₁.2 S hs₁
    · rw [ht₂] at ho₂; exact ho₂.2 S hs₂

private noncomputable def stepAlpha : ℕ → ℝ → ℝ
  | 0, α => α
  | k + 1, α => stepAlpha k (α / 2 + 1 / 10000)

/-- Iterate `bisect_subset_zero` `k` times and finish with `BinTree.ofSet` leaf peeling. -/
private theorem exists_binTree_of_subset {V E : Type*} [Finite V] [Finite E] {G : Multigraph V E}
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {q : ℝ} (hq : 0 ≤ q) {R : ℕ} {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    (hstrad : straddleBound ρ₀ ≤ 3 / 20)
    (large : 5 * (vertexOverlap 3 (R + 1) : ℝ) / (1 / 10000) ^ 2 < Nat.card V)
    {β : ℝ} (hβ : 134 / 1000 ≤ β) :
    ∀ (k : ℕ) {α : ℝ} (_hα : α ≤ 11 / 25) (_hpeel : 3 * stepAlpha k α ≤ β) (Y : Set V),
      (Y.ncard : ℝ) ≤ α * Nat.card V → ((G.edgeCut Y).ncard : ℝ) ≤ β * Nat.card V →
      ∃ o : Option (BinTree V),
        match o with
        | none => Y = ∅
        | some t => t.IsPartition Y ∧
            ∀ S, t.IsSubtreeSet S → ((G.edgeCut S).ncard : ℝ) ≤ β * Nat.card V := by
  have hh_pos : (0 : ℝ) < Nat.card V := lt_of_le_of_lt (by positivity) large
  intro k
  induction k with
  | zero =>
    classical
    intro α _ hpeel Y hY _
    dsimp [stepAlpha] at hpeel
    refine ⟨BinTree.ofSet Y, ?_⟩
    have hspec := BinTree.ofSet_spec Y
    cases ho : BinTree.ofSet Y with
    | none => rw [ho] at hspec; exact hspec
    | some t =>
      rw [ho] at hspec
      refine ⟨hspec, fun S hS => ?_⟩
      have hsub : S ⊆ Y := hS.subset_leafSet.trans hspec.2.le
      have hcut_3S : (G.edgeCut S).ncard ≤ 3 * S.ncard := by
        have := Fintype.ofFinite E
        have := Fintype.ofFinite V
        have hsubE : G.edgeCut S ⊆ ⋃ v ∈ S, G.incidenceSet v := fun e he => by
          rw [mem_edgeCut] at he
          by_cases hs : G.src e ∈ S
          · exact mem_biUnion hs (Or.inl rfl)
          · have ht : G.tgt e ∈ S := by tauto
            exact mem_biUnion ht (Or.inr rfl)
        let fs := S.toFinset
        have hsubF : G.edgeCut S ⊆ ↑(fs.biUnion fun v => (G.incidenceSet v).toFinset) := by
          intro e he
          obtain ⟨v, hvS, hvinc⟩ := mem_iUnion₂.mp (hsubE he)
          exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨v, Set.mem_toFinset.mpr hvS,
            Set.mem_toFinset.mpr hvinc⟩)
        refine (ncard_le_ncard hsubF (toFinite _)).trans ?_
        rw [ncard_coe_finset]
        refine Finset.card_biUnion_le.trans ?_
        have hsum3 : (∑ v ∈ fs, (G.incidenceSet v).toFinset.card) = 3 * S.ncard := by
          have hv3 (v : V) : (G.incidenceSet v).toFinset.card = 3 := by
            rw [← Set.ncard_eq_toFinset_card', h3 v]
          simp_rw [hv3]
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm, ← Set.ncard_eq_toFinset_card']
        exact hsum3.le
      have hS_le_Y : (S.ncard : ℝ) ≤ (Y.ncard : ℝ) :=
        Nat.cast_le.mpr (ncard_le_ncard hsub (toFinite Y))
      have hcut_r : ((G.edgeCut S).ncard : ℝ) ≤ 3 * (S.ncard : ℝ) := by exact_mod_cast hcut_3S
      calc ((G.edgeCut S).ncard : ℝ) ≤ 3 * (Y.ncard : ℝ) := by linarith
        _ ≤ 3 * (α * Nat.card V) := by gcongr
        _ = (3 * α) * Nat.card V := by ring
        _ ≤ β * Nat.card V := mul_le_mul_of_nonneg_right hpeel hh_pos.le
  | succ k ih =>
    intro α hα hpeel Y hY hcutY
    obtain ⟨Y₁, Y₂, hdisj, hunion, hY₁, hY₂, hcY₁, hcY₂⟩ :=
      bisect_subset_zero hloop h3 hq hρ₀ hρ (η := 1 / 10000) (by norm_num) large Y
    have hα' : α / 2 + 1 / 10000 ≤ 11 / 25 := by linarith
    have hstrad_nonneg : 0 ≤ straddleBound ρ₀ := by
      unfold straddleBound; have := arccos_nonneg ((1 + 3 * ρ₀) / 4); positivity
    have hcut_step (Z : Set V)
        (hcZ : ((G.edgeCut Z).ncard : ℝ) ≤
          straddleBound ρ₀ * (Y.ncard : ℝ) + 1 / 2 * ((G.edgeCut Y).ncard : ℝ) +
            2 * (1 / 10000) * Nat.card V) :
        ((G.edgeCut Z).ncard : ℝ) ≤ β * Nat.card V := by
      have h1 : straddleBound ρ₀ * (Y.ncard : ℝ) ≤ 3 / 20 * (α * Nat.card V) := by
        calc straddleBound ρ₀ * (Y.ncard : ℝ)
            ≤ 3 / 20 * (Y.ncard : ℝ) := mul_le_mul_of_nonneg_right hstrad (Nat.cast_nonneg _)
          _ ≤ 3 / 20 * (α * Nat.card V) := mul_le_mul_of_nonneg_left hY (by norm_num)
      have h2 : 3 / 20 * (α * Nat.card V) + 1 / 2 * (β * Nat.card V) +
          2 * (1 / 10000) * Nat.card V ≤ β * Nat.card V := by
        have hcoef : 3 / 20 * α + 1 / 2 * β + 2 * (1 / 10000) ≤ β := by linarith
        calc 3 / 20 * (α * (Nat.card V : ℝ)) + 1 / 2 * (β * Nat.card V) +
              2 * (1 / 10000) * Nat.card V
            = (3 / 20 * α + 1 / 2 * β + 2 * (1 / 10000)) * Nat.card V := by ring
          _ ≤ β * Nat.card V := mul_le_mul_of_nonneg_right hcoef hh_pos.le
      linarith
    obtain ⟨o₁, ho₁⟩ := ih hα' hpeel Y₁ (by linarith) (hcut_step Y₁ hcY₁)
    obtain ⟨o₂, ho₂⟩ := ih hα' hpeel Y₂ (by linarith) (hcut_step Y₂ hcY₂)
    exact ⟨BinTree.joinOpt o₁ o₂, joinOpt_isPartition_cut hdisj hunion hcutY ho₁ ho₂⟩

end DeeperLevels

/-! ### Level-zero off-median cut + greedy flips -/

section LevelZero

/-- **Level-zero off-median cut and greedy `1`-vertex flips.** For `t₀ ∈ [-3 / 10, 0]` and
`0 < δ ≤ 1 / 1000`, some sample `ω` followed by greedy flips partitions `V = A* ⊔ R*` so that both
`X ∈ {A*, R*}` satisfy `|X| ≤ 43 / 50 * |V|`, `|G.edgeCut X| ≤ (carvingAt t₀ + δ) |V|`,
`lyap p G X ≤ (carvingAt t₀ + δ / 4) |V|`, and `∀ v ∈ X, |inc(v) ∩ ∂X| ≤ 1`. -/
private theorem exists_levelZero_partition {V E : Type*} [Finite V] [Finite E] {G : Multigraph V E}
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (-3 / 10 : ℝ) 0)
    {δ : ℝ} (hδ : 0 < δ) (hδ_small : δ ≤ 1 / 1000)
    {q : ℝ} (hq : 0 ≤ q) {R : ℕ} {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    (hstrad : straddleBound ρ₀ ≤ gaussianCoefficient + δ / 8)
    (large : 3 * (vertexOverlap 3 R : ℝ) / (δ / 16) ^ 2 < Nat.card V) :
    ∃ A Rset : Set V, Disjoint A Rset ∧ A ∪ Rset = Set.univ ∧
      (A.ncard : ℝ) ≤ 43 / 50 * Nat.card V ∧
      (Rset.ncard : ℝ) ≤ 43 / 50 * Nat.card V ∧
      ((G.edgeCut A).ncard : ℝ) ≤ (carvingAt t₀ + δ) * Nat.card V ∧
      lyap gaussianCoefficient G A ≤ (carvingAt t₀ + δ / 4) * Nat.card V ∧
      lyap gaussianCoefficient G Rset ≤ (carvingAt t₀ + δ / 4) * Nat.card V ∧
      (∀ v ∈ A, (G.incidenceSet v ∩ G.edgeCut A).ncard ≤ 1) ∧
      (∀ v ∈ Rset, (G.incidenceSet v ∩ G.edgeCut Rset).ncard ≤ 1) := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  set h : ℝ := (Nat.card V : ℝ)
  have hh_pos : 0 < h := lt_of_le_of_lt (by positivity) large
  have hdeg : G.MaxDegreeLE 3 := fun v => (h3 v).le
  set η₀ := δ / 16
  have hη₀ : 0 < η₀ := by positivity
  set c : ℝ := η₀ * h
  have hc_pos : 0 < c := by positivity
  set P := Measure.pi fun _ : V => gaussianReal 0 1
  set D := vertexOverlap 3 R
  -- Concentrate `E_{< t₀}` and `S_{t₀}`.
  let Ae : E → Set (V → ℝ) := fun e => {ω | edgeScore G q R ω e < t₀}
  let As : V → Set (V → ℝ) := fun v => straddleEvent G q R t₀ v
  have hAe_dep (e : E) :
      DependsOn (· ∈ Ae e) (closedBall G.toSimpleGraph (G.src e) (R + 1)) :=
    fun _ _ hω => by simp only [Ae, mem_ofPred_eq, edgeScore_congr (Or.inl rfl) hω]
  have hdevE : P.real (deviation Ae c) ≤ (Fintype.card E : ℝ) * D / c ^ 2 :=
    measureReal_deviation_le
      (fun e => measurableSet_lt (measurable_edgeScore q R e) measurable_const)
      (fun e => closedBall G.toSimpleGraph (G.src e) (R + 1)) hAe_dep
      (fun e => card_not_disjoint_closedBall_src_le hdeg R e) hc_pos
  have hdevS : P.real (deviation As c) ≤ (Fintype.card V : ℝ) * D / c ^ 2 :=
    measureReal_deviation_le (fun v => measurableSet_straddleEvent q R t₀ v)
      (fun v => closedBall G.toSimpleGraph v (R + 1)) (fun v => dependsOn_straddleEvent q R t₀ v)
      (fun v => card_not_disjoint_closedBall_le hdeg (by norm_num) R v) hc_pos
  have hE_card : (Fintype.card E : ℝ) = 3 / 2 * h := by
    have hr : ((2 * Nat.card E : ℕ) : ℝ) = ((3 * Nat.card V : ℕ) : ℝ) := by
      exact_mod_cast two_mul_card_edges_eq_cubic hloop h3
    rw [Nat.card_eq_fintype_card (α := E)] at hr
    push_cast at hr; linarith
  have hV_card : (Fintype.card V : ℝ) = h := by rw [← Nat.card_eq_fintype_card]
  rw [hE_card] at hdevE
  rw [hV_card] at hdevS
  obtain ⟨ω, hω⟩ := exists_notMem_of_measureReal_lt_one
    (((measureReal_union_le _ _).trans (add_le_add hdevE hdevS)).trans_lt
      (by calc _ = 5 / 2 * D * h / c ^ 2 := by ring
        _ < 1 := mul_div_mul_sq_lt_one hη₀.ne' hh_pos
          ((by gcongr; norm_num : 5 / 2 * (D : ℝ) / η₀ ^ 2 ≤ _).trans_lt large)))
  simp only [mem_union, not_or] at hω
  obtain ⟨hωE, hωS⟩ := hω
  set score := edgeScore G q R ω
  set A₀ := lowSide G score t₀
  set E_lt := {e : E | score e < t₀}.ncard
  set k₁ := {v : V | v ∉ A₀ ∧ G.EdgeStraddles score t₀ v}.ncard
  set k₂ := {v : V | v ∈ A₀ ∧ G.EdgeStraddles score t₀ v}.ncard
  set S_tot := {v : V | G.EdgeStraddles score t₀ v}.ncard
  have hk_sum : k₁ + k₂ = S_tot := ncard_straddle_split A₀ score t₀
  have hcut_A₀ : (G.edgeCut A₀).ncard ≤ k₁ + k₂ := ncard_edgeCut_lowSide_le h3 score t₀
  have hhalf_edge : 2 * E_lt + k₂ = 3 * A₀.ncard + k₁ :=
    two_mul_ncard_score_lt_eq hloop h3 score t₀
  -- Two-sided deviation on `E_lt` and upper deviation on `S_tot`.
  have hmean_E : ∑ e : E, P.real (Ae e) = 3 / 2 * h * cdf (gaussianReal 0 1) t₀ := by
    have hpe (e : E) : P.real (Ae e) = cdf (gaussianReal 0 1) t₀ :=
      measureReal_inner_lt_eq_cdf (norm_edgeVector hloop hdeg hq (by linarith only [hρ₀]) hρ e) t₀
    simp_rw [hpe]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hE_card]
  have hE_abs : |(E_lt : ℝ) - 3 / 2 * h * cdf (gaussianReal 0 1) t₀| < c := by
    have hnot : ¬c ≤ |∑ e : E, (Ae e).indicator (1 : (V → ℝ) → ℝ) ω - ∑ e : E, P.real (Ae e)| :=
      hωE
    rwa [not_le, ← ncard_eq_sum_indicator, hmean_E] at hnot
  have hexp_le1 : exp (-t₀ ^ 2 / 2) ≤ 1 := exp_le_one_iff.mpr (by nlinarith only)
  have hS_upper : (S_tot : ℝ) ≤ (exp (-t₀ ^ 2 / 2) * gaussianCoefficient + 3 * δ / 16) * h := by
    have hmean_S : ∑ v : V, P.real (As v) ≤ h * (exp (-t₀ ^ 2 / 2) * straddleBound ρ₀) :=
      (Finset.sum_le_sum fun v _ =>
        measureReal_straddleEvent_le_exp_mul hloop h3 hq hρ₀ hρ t₀ v).trans_eq
        (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hV_card])
    have hprod : exp (-t₀ ^ 2 / 2) * straddleBound ρ₀ ≤
        exp (-t₀ ^ 2 / 2) * gaussianCoefficient + δ / 8 := by
      linarith only [mul_le_mul_of_nonneg_left hstrad (exp_pos (-t₀ ^ 2 / 2)).le,
        mul_le_mul_of_nonneg_right hexp_le1 (by positivity : (0 : ℝ) ≤ δ / 8)]
    have hcnt := ncard_lt_of_notMem_deviation hωS
    have h1 : (S_tot : ℝ) < ∑ v : V, P.real (As v) + c := hcnt
    have hc_eq : c = δ / 16 * h := rfl
    linarith only [h1, hmean_S, mul_le_mul_of_nonneg_left hprod hh_pos.le, hc_eq]
  -- Bounds on `A₀` and `A₀ᶜ` before flips.
  set μ := gaussianCoefficient
  have hμ_pos : 0 < μ := gaussianCoefficient_pos
  have hμ_lt : μ < 3 / 20 := gaussianCoefficient_lt_three_twentieths
  have hcdf_half : cdf (gaussianReal 0 1) t₀ ≤ 1 / 2 := by
    have h0 : cdf (gaussianReal 0 1) 0 = 2⁻¹ := cdf_gaussianReal_zero_zero one_ne_zero
    have hm := (strictMono_cdf_gaussianReal 0 one_ne_zero).monotone ht₀.2
    linarith only [h0, hm]
  have hcdf_13_20 : 1 - cdf (gaussianReal 0 1) t₀ ≤ 13 / 20 :=
    one_sub_cdf_le_13_twentieths ht₀.1
  have hk_sum_r : (k₁ : ℝ) + (k₂ : ℝ) = (S_tot : ℝ) := by exact_mod_cast hk_sum
  have hcut_r : ((G.edgeCut A₀).ncard : ℝ) ≤ (k₁ : ℝ) + (k₂ : ℝ) := by exact_mod_cast hcut_A₀
  have hhalf_r : 2 * (E_lt : ℝ) + (k₂ : ℝ) = 3 * (A₀.ncard : ℝ) + (k₁ : ℝ) := by
    exact_mod_cast hhalf_edge
  have hcompl_r : (A₀.ncard : ℝ) + ((A₀ᶜ).ncard : ℝ) = h := by
    rw [← Nat.cast_add, ncard_add_ncard_compl]
  have hk1_0 : 0 ≤ (k₁ : ℝ) := Nat.cast_nonneg _
  have hk2_0 : 0 ≤ (k₂ : ℝ) := Nat.cast_nonneg _
  obtain ⟨hE_lo, hE_hi⟩ := abs_lt.mp hE_abs
  have hc_eq : c = δ / 16 * h := rfl
  have hμ_δ : μ * (δ / 16 * h) ≤ 3 / 20 * (δ / 16 * h) :=
    mul_le_mul_of_nonneg_right hμ_lt.le (by positivity)
  have hcoef_δ : (1 / 2 - 2 / 3 * μ) * (3 * δ / 16 * h) ≤ 1 / 2 * (3 * δ / 16 * h) :=
    mul_le_mul_of_nonneg_right (by linarith only [hμ_pos]) (by positivity)
  have hcarv_r : (μ * (1 - cdf (gaussianReal 0 1) t₀) +
      (1 / 2 - 2 / 3 * μ) * (exp (-t₀ ^ 2 / 2) * μ)) * h ≤ carvingAt t₀ * h :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hh_pos.le
  have hS_upper' : (S_tot : ℝ) ≤ (exp (-t₀ ^ 2 / 2) * μ + 3 * δ / 16) * h := hS_upper
  have h4 : (1 / 2 - 2 / 3 * μ) * (S_tot : ℝ) ≤
      (1 / 2 - 2 / 3 * μ) * (exp (-t₀ ^ 2 / 2) * μ * h) + 1 / 2 * (3 * δ / 16 * h) := by
    have hm := mul_le_mul_of_nonneg_left hS_upper'
      (by linarith only [hμ_lt] : 0 ≤ 1 / 2 - 2 / 3 * μ)
    linarith only [hm, hcoef_δ]
  have hδh_nonneg : 0 ≤ δ * h := mul_nonneg hδ.le hh_pos.le
  have hlyap_side (sCard bCard base kOut kIn : ℝ) (hkOut0 : 0 ≤ kOut)
      (hcut_b : bCard ≤ kOut + kIn) (hksum : kOut + kIn = (S_tot : ℝ))
      (hs_eq : sCard = base + 1 / 3 * kIn - 1 / 3 * kOut)
      (hbase : base ≤ (1 - cdf (gaussianReal 0 1) t₀) * h + δ / 16 * h) :
      μ * sCard + (1 / 2 - μ) * bCard ≤ (carvingAt t₀ + δ / 4) * h := by
    have hcut_m : (1 / 2 - μ) * bCard ≤ (1 / 2 - μ) * (kOut + kIn) :=
      mul_le_mul_of_nonneg_left hcut_b (by linarith only [hμ_lt])
    have hk_m : μ * (1 / 3 * kIn - 1 / 3 * kOut) + (1 / 2 - μ) * (kOut + kIn) ≤
        (1 / 2 - 2 / 3 * μ) * (kOut + kIn) := by
      have hp : 0 ≤ μ * kOut := mul_nonneg hμ_pos.le hkOut0
      linarith only [hp]
    have hbase_m : μ * base ≤
        μ * ((1 - cdf (gaussianReal 0 1) t₀) * h) + 3 / 20 * (δ / 16 * h) := by
      have hm := mul_le_mul_of_nonneg_left hbase hμ_pos.le
      linarith only [hm, hμ_δ]
    have hsplit : μ * sCard = μ * base + μ * (1 / 3 * kIn - 1 / 3 * kOut) := by
      rw [hs_eq]; ring
    rw [hsplit]
    have hm_eq : (1 / 2 - 2 / 3 * μ) * (kOut + kIn) = (1 / 2 - 2 / 3 * μ) * (S_tot : ℝ) := by
      rw [hksum]
    linarith only [hcut_m, hk_m, hm_eq, hbase_m, h4, hcarv_r, hδh_nonneg]
  have hcomm : h * cdf (gaussianReal 0 1) t₀ = cdf (gaussianReal 0 1) t₀ * h := mul_comm _ _
  have hlyap_A₀ : lyap μ G A₀ ≤ (carvingAt t₀ + δ / 4) * h := by
    have hcdf_le : cdf (gaussianReal 0 1) t₀ * h ≤ (1 - cdf (gaussianReal 0 1) t₀) * h :=
      mul_le_mul_of_nonneg_right (by linarith only [hcdf_half]) hh_pos.le
    exact hlyap_side (A₀.ncard : ℝ) ((G.edgeCut A₀).ncard : ℝ) (2 / 3 * (E_lt : ℝ)) (k₁ : ℝ)
      (k₂ : ℝ) hk1_0 hcut_r hk_sum_r (by linarith only [hhalf_r])
      (by linarith only [hE_hi, hc_eq, hcdf_le, hcomm, hδh_nonneg])
  have hlyap_R₀ : lyap μ G A₀ᶜ ≤ (carvingAt t₀ + δ / 4) * h := by
    simp only [lyap, G.edgeCut_compl]
    exact hlyap_side ((A₀ᶜ).ncard : ℝ) ((G.edgeCut A₀).ncard : ℝ) (h - 2 / 3 * (E_lt : ℝ))
      (k₂ : ℝ) (k₁ : ℝ) hk2_0 (by linarith only [hcut_r]) (by linarith only [hk_sum_r])
      (by linarith only [hcompl_r, hhalf_r]) (by linarith only [hE_lo, hc_eq, hcomm, hδh_nonneg])
  have hδh : δ * h ≤ 1 / 1000 * h := mul_le_mul_of_nonneg_right hδ_small hh_pos.le
  have hS_151 : (S_tot : ℝ) ≤ 151 / 1000 * h := by
    linarith only [hS_upper', hδh, mul_le_mul_of_nonneg_right
      (mul_le_mul hexp_le1 hμ_lt.le hμ_pos.le zero_le_one) hh_pos.le]
  have hsum_A₀_b : (A₀.ncard : ℝ) + ((G.edgeCut A₀).ncard : ℝ) ≤ 43 / 50 * h := by
    linarith only [hhalf_r, hk_sum_r, hcut_r, hk1_0, hk2_0, hE_hi, hc_eq, hδh, hS_151,
      mul_le_mul_of_nonneg_left hcdf_half hh_pos.le]
  have hsum_R₀_b : ((A₀ᶜ).ncard : ℝ) + ((G.edgeCut A₀).ncard : ℝ) ≤ 43 / 50 * h := by
    have hcdf_h : (1 - cdf (gaussianReal 0 1) t₀) * h ≤ 13 / 20 * h :=
      mul_le_mul_of_nonneg_right hcdf_13_20 hh_pos.le
    linarith only [hcompl_r, hhalf_r, hk_sum_r, hcut_r, hk1_0, hk2_0, hE_lo, hc_eq, hcdf_h, hδh,
      hS_151]
  have hcut_carv : ((G.edgeCut A₀).ncard : ℝ) ≤ (carvingAt t₀ + δ) * h := by
    have hcarv1 : exp (-t₀ ^ 2 / 2) * μ ≤ carvingAt t₀ := le_max_left _ _
    have hcarv_h := mul_le_mul_of_nonneg_right hcarv1 hh_pos.le
    linarith only [hcut_r, hk_sum_r, hS_upper', hcarv_h, hδh_nonneg]
  -- Apply greedy flips to `A₀`.
  obtain ⟨A, hbA, hLA, hLAc, hsumA, hsumAc, hminA, hminAc⟩ :=
    exists_greedy_flipped hloop h3 hμ_lt.le A₀
  refine ⟨A, Aᶜ, disjoint_compl_right, union_compl_self A, ?_, ?_, ?_,
    hLA.trans hlyap_A₀, hLAc.trans hlyap_R₀, hminA, by simpa only [G.edgeCut_compl] using hminAc⟩
  · have hr : (A.ncard : ℝ) + ((G.edgeCut A).ncard : ℝ) ≤
        (A₀.ncard : ℝ) + ((G.edgeCut A₀).ncard : ℝ) := by exact_mod_cast hsumA
    linarith only [hr, Nat.cast_nonneg (α := ℝ) (G.edgeCut A).ncard, hsum_A₀_b]
  · have hr : ((Aᶜ).ncard : ℝ) + ((G.edgeCut A).ncard : ℝ) ≤
        ((A₀ᶜ).ncard : ℝ) + ((G.edgeCut A₀).ncard : ℝ) := by exact_mod_cast hsumAc
    linarith only [hr, Nat.cast_nonneg (α := ℝ) (G.edgeCut A).ncard, hsum_R₀_b]
  · exact (Nat.cast_le.mpr hbA).trans hcut_carv

end LevelZero

/-! ### Main carving-width and branchwidth theorems -/

/-- **Parametric carving-width bound.** For every threshold `t₀ ∈ [-3 / 10, 0]` and every `ξ > 0`,
all sufficiently large finite loopless cubic multigraphs `G` satisfy
`(G.carvingWidth : ℝ) ≤ (carvingAt t₀ + ξ) * Nat.card V`. -/
theorem exists_carvingWidth_le_carvingAt {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (-3 / 10 : ℝ) 0) {ξ : ℝ}
    (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ (V E : Type*) [Finite V] [Finite E] (G : Multigraph V E), G.Loopless →
      (∀ v, (G.incidenceSet v).ncard = 3) → N₀ < Nat.card V →
        (G.carvingWidth : ℝ) ≤ (carvingAt t₀ + ξ) * Nat.card V := by
  set δ := min ξ (1 / 1000)
  have hδ : 0 < δ := lt_min hξ (by norm_num)
  have hδ_le_ξ : δ ≤ ξ := min_le_left _ _
  have hδ_small : δ ≤ 1 / 1000 := min_le_right _ _
  obtain ⟨q₁, R₁, ρ₁, hq₁, hρ₁, hcorr₁, hstrad₁⟩ :=
    exists_straddle_params (by positivity : 0 < δ / 8)
  have hgap2 : 0 < 3 / 20 - gaussianCoefficient :=
    sub_pos.mpr gaussianCoefficient_lt_three_twentieths
  obtain ⟨q₂, R₂, ρ₂, hq₂, hρ₂, hcorr₂, hstrad₂⟩ := exists_straddle_params hgap2
  have hstrad₂' : straddleBound ρ₂ ≤ 3 / 20 := by linarith
  set M₁ : ℕ := ⌈768 / δ⌉₊ + 2
  have hM₁_2 : 2 ≤ M₁ := by omega
  have hM₁_real : 768 / δ ≤ (M₁ : ℝ) := by
    dsimp [M₁]; push_cast; linarith [Nat.le_ceil (768 / δ)]
  set η₁ := min (δ / 16) (1 / 1000)
  have hη₁ : 0 < η₁ := lt_min (by positivity) (by norm_num)
  have hη₁_δ : η₁ ≤ δ / 16 := min_le_left _ _
  have hη₁_1000 : η₁ ≤ 1 / 1000 := min_le_right _ _
  set N_raw : ℝ :=
    max (3 * (vertexOverlap 3 R₁ : ℝ) / (δ / 16) ^ 2)
      (max (4 * (M₁ : ℝ) ^ 2 * (vertexOverlap 3 R₁ : ℝ) / η₁ ^ 2)
        (5 * (vertexOverlap 3 (R₂ + 1) : ℝ) / (1 / 10000) ^ 2))
  refine ⟨⌈N_raw⌉₊ + 1, fun V E _ _ G hloop h3 hN => ?_⟩
  have hN_gt : N_raw < Nat.card V :=
    (Nat.le_ceil N_raw).trans_lt (by exact_mod_cast (Nat.lt_of_succ_lt hN))
  have hlarge0 : 3 * (vertexOverlap 3 R₁ : ℝ) / (δ / 16) ^ 2 < Nat.card V :=
    (le_max_left _ _).trans_lt hN_gt
  have hlarge1 : 4 * (M₁ : ℝ) ^ 2 * (vertexOverlap 3 R₁ : ℝ) / η₁ ^ 2 < Nat.card V :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hN_gt
  have hlarge2 : 5 * (vertexOverlap 3 (R₂ + 1) : ℝ) / (1 / 10000) ^ 2 < Nat.card V :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hN_gt
  have hV_nonempty : Nonempty V := Finite.card_pos_iff.mp (by omega)
  set β := carvingAt t₀ + δ
  have hβ_ge : 134 / 1000 ≤ β := by linarith [carvingAt_ge_134_of_mem_Icc ht₀]
  have hpeel : 3 * stepAlpha 4 (11 / 25) ≤ β := by
    have : 3 * stepAlpha 4 (11 / 25) ≤ (134 / 1000 : ℝ) := by norm_num [stepAlpha]
    linarith
  -- Step 1: Level-zero off-median cut + greedy flips.
  obtain ⟨A, Rset, hdisjAR, hunionAR, hA_sz, hR_sz, hA_cut, hLA, hLR, hminA, hminR⟩ :=
    exists_levelZero_partition hloop h3 ht₀ hδ hδ_small hq₁ hρ₁ hcorr₁ hstrad₁ hlarge0
  have hR_cut : ((G.edgeCut Rset).ncard : ℝ) ≤ β * Nat.card V := by
    rwa [← (IsCompl.of_eq hdisjAR.eq_bot hunionAR).compl_eq, G.edgeCut_compl]
  -- Step 2: Build carving subtree on each half `X ∈ {A, Rset}` via Depth 1 + Depths 2–5 + peeling.
  have build_half (X : Set V) (hX_sz : (X.ncard : ℝ) ≤ 43 / 50 * Nat.card V)
      (hX_cut : ((G.edgeCut X).ncard : ℝ) ≤ β * Nat.card V)
      (hLX : lyap gaussianCoefficient G X ≤ (carvingAt t₀ + δ / 4) * Nat.card V)
      (hminX : ∀ v ∈ X, (G.incidenceSet v ∩ G.edgeCut X).ncard ≤ 1) :
      ∃ o : Option (BinTree V),
        match o with
        | none => X = ∅
        | some t => t.IsPartition X ∧
            ∀ S, t.IsSubtreeSet S → ((G.edgeCut S).ncard : ℝ) ≤ β * Nat.card V := by
    obtain ⟨X₁, X₂, hdX, huX, h1_sz, h2_sz, h1_cut, h2_cut⟩ :=
      bisect_compressed_zero hloop h3 hq₁ hρ₁ hcorr₁ hδ hstrad₁ hM₁_2 hM₁_real hη₁ hη₁_δ
        hlarge1 X hminX
    have hh_pos : (0 : ℝ) < Nat.card V := by exact_mod_cast (by omega : 0 < Nat.card V)
    have hη_mul : η₁ * (Nat.card V : ℝ) ≤ 1 / 1000 * Nat.card V :=
      mul_le_mul_of_nonneg_right hη₁_1000 hh_pos.le
    have hδN : 0 ≤ δ * (Nat.card V : ℝ) := mul_nonneg hδ.le hh_pos.le
    have hβ_eq : β * (Nat.card V : ℝ) = carvingAt t₀ * Nat.card V + δ * Nat.card V := by
      dsimp [β]; ring
    have hsz1 : (X₁.ncard : ℝ) ≤ 11 / 25 * Nat.card V := by linarith only [h1_sz, hX_sz, hη_mul]
    have hsz2 : (X₂.ncard : ℝ) ≤ 11 / 25 * Nat.card V := by linarith only [h2_sz, hX_sz, hη_mul]
    have hct1 : ((G.edgeCut X₁).ncard : ℝ) ≤ β * Nat.card V := by
      linarith only [h1_cut, hLX, hδN, hβ_eq]
    have hct2 : ((G.edgeCut X₂).ncard : ℝ) ≤ β * Nat.card V := by
      linarith only [h2_cut, hLX, hδN, hβ_eq]
    obtain ⟨o₁, ho₁⟩ := exists_binTree_of_subset hloop h3 hq₂ hρ₂ hcorr₂ hstrad₂' hlarge2
      hβ_ge 4 le_rfl hpeel X₁ hsz1 hct1
    obtain ⟨o₂, ho₂⟩ := exists_binTree_of_subset hloop h3 hq₂ hρ₂ hcorr₂ hstrad₂' hlarge2
      hβ_ge 4 le_rfl hpeel X₂ hsz2 hct2
    exact ⟨BinTree.joinOpt o₁ o₂, joinOpt_isPartition_cut hdX huX hX_cut ho₁ ho₂⟩
  obtain ⟨oA, hoA⟩ := build_half A hA_sz hA_cut hLA hminA
  obtain ⟨oR, hoR⟩ := build_half Rset hR_sz hR_cut hLR hminR
  have hcut_univ : ((G.edgeCut Set.univ).ncard : ℝ) ≤ β * Nat.card V := by
    simp only [Multigraph.edgeCut_univ, ncard_empty, Nat.cast_zero]
    positivity
  have htop_spec := joinOpt_isPartition_cut hdisjAR hunionAR hcut_univ hoA hoR
  cases htop : BinTree.joinOpt oA oR with
  | none =>
    rw [htop] at htop_spec
    exact absurd htop_spec Set.univ_nonempty.ne_empty
  | some t_all =>
    rw [htop] at htop_spec
    set k_cap : ℕ := ⌊β * Nat.card V⌋₊
    have hcw_nat : G.carvingWidth ≤ k_cap :=
      G.carvingWidth_le_of_binTree htop_spec.1 fun S hS => Nat.le_floor (htop_spec.2 S hS)
    calc (G.carvingWidth : ℝ) ≤ (k_cap : ℝ) := Nat.cast_le.mpr hcw_nat
      _ ≤ β * Nat.card V := Nat.floor_le (by positivity)
      _ ≤ (carvingAt t₀ + ξ) * Nat.card V :=
          mul_le_mul_of_nonneg_right (by dsimp [β]; linarith only [hδ_le_ξ]) (Nat.cast_nonneg _)

/-- **Carving-width of cubic multigraphs.** For every `ξ > 0`, all sufficiently large finite
loopless cubic multigraphs `G` (parallel edges allowed) satisfy
`(G.carvingWidth : ℝ) ≤ (carvingCoefficient + ξ) * Nat.card V`. -/
theorem exists_carvingWidth_le_carvingCoefficient {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ (V E : Type*) [Finite V] [Finite E] (G : Multigraph V E), G.Loopless →
      (∀ v, (G.incidenceSet v).ncard = 3) → N₀ < Nat.card V →
        (G.carvingWidth : ℝ) ≤ (carvingCoefficient + ξ) * Nat.card V := by
  obtain ⟨t₀, ht₀, hlt⟩ := exists_mem_Icc_carvingAt_lt (half_pos hξ)
  obtain ⟨N₀, hN₀⟩ := exists_carvingWidth_le_carvingAt ht₀ (half_pos hξ)
  refine ⟨N₀, fun V E _ _ G hloop h3 hN => (hN₀ V E G hloop h3 hN).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

/-- **Explicit rational carving-width bound (`0.137432 < c₃`).** For every `ξ > 0`, all
sufficiently large finite loopless cubic multigraphs `G` satisfy
`(G.carvingWidth : ℝ) ≤ (137432 / 1000000 + ξ) * Nat.card V`. -/
theorem exists_carvingWidth_le_137432 {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ (V E : Type*) [Finite V] [Finite E] (G : Multigraph V E), G.Loopless →
      (∀ v, (G.incidenceSet v).ncard = 3) → N₀ < Nat.card V →
        (G.carvingWidth : ℝ) ≤ (137432 / 1000000 + ξ) * Nat.card V := by
  obtain ⟨N₀, hN₀⟩ := exists_carvingWidth_le_carvingCoefficient hξ
  refine ⟨N₀, fun V E _ _ G hloop h3 hN => (hN₀ V E G hloop h3 hN).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith [carvingCoefficient_le_137432]) (Nat.cast_nonneg _)

/-- **Branchwidth of cubic multigraphs.** For every `ξ > 0`, all sufficiently large finite loopless
cubic multigraphs `G` satisfy `(G.branchwidth : ℝ) ≤ (carvingCoefficient + ξ) * Nat.card V`. -/
theorem exists_branchwidth_le_carvingCoefficient {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ (V E : Type*) [Finite V] [Finite E] (G : Multigraph V E), G.Loopless →
      (∀ v, (G.incidenceSet v).ncard = 3) → N₀ < Nat.card V →
        (G.branchwidth : ℝ) ≤ (carvingCoefficient + ξ) * Nat.card V := by
  obtain ⟨N₀, hN₀⟩ := exists_carvingWidth_le_carvingCoefficient hξ
  exact ⟨N₀, fun V E _ _ G hloop h3 hN =>
    (Nat.cast_le.mpr (G.branchwidth_le_carvingWidth hloop h3)).trans (hN₀ V E G hloop h3 hN)⟩

/-- **Explicit rational branchwidth bound (`0.137432 < c₃`).** For every `ξ > 0`, all sufficiently
large finite loopless cubic multigraphs `G` satisfy
`(G.branchwidth : ℝ) ≤ (137432 / 1000000 + ξ) * Nat.card V`. -/
theorem exists_branchwidth_le_137432 {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ (V E : Type*) [Finite V] [Finite E] (G : Multigraph V E), G.Loopless →
      (∀ v, (G.incidenceSet v).ncard = 3) → N₀ < Nat.card V →
        (G.branchwidth : ℝ) ≤ (137432 / 1000000 + ξ) * Nat.card V := by
  obtain ⟨N₀, hN₀⟩ := exists_carvingWidth_le_137432 hξ
  exact ⟨N₀, fun V E _ _ G hloop h3 hN =>
    (Nat.cast_le.mpr (G.branchwidth_le_carvingWidth hloop h3)).trans (hN₀ V E G hloop h3 hN)⟩

end Cslib.Circuits.Frontier.Carving
