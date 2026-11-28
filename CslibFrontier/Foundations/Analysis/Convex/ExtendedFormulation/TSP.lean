/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.CorrDigraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FinCases

/-!
# Exponential extension-complexity lower bound for TSP polytopes

This module completes the Fiorini–Massar–Pokutta–Tiwary–de Wolf reduction from the correlation
polytope `corrPolytope K (Fin p)` to the symmetric traveling salesman polytope `tspPolytope K V`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.4, Lemma 11 and Theorem 12], combined with
Kaibel–Weltge's `(3 / 2) ^ p` bound on `corrPolytope` [KaibelWeltge2015, Theorem 1].

For `p ≥ 1`, `SplitV (CorrDigraphV p) v₀ pad` has `3 * |CorrDigraphV p| + pad ≤ 69 * p ^ 2 + pad`
vertices, and intersecting `tspPolytope K W` with the zero-weight non-edge exposed face of
`paddedSplitGraph v₀ pad (corrDigraphAdj p hp)` yields a face whose coordinate projection onto the
distinguished reverse edges `(vOut (chain v 1), vIn (chain v 0))` equals `corrPolytope K (Fin p)`
(`extensionComplexity_corrPolytope_le_tspPolytope_splitV`). Transporting along any bijection
`SplitV (CorrDigraphV p) v₀ pad ≃ V` with `p = ⌊√(|V| / 69)⌋` gives
`3 ^ p ≤ 2 ^ p * extensionComplexity (tspPolytope K V)` and `(3 / 2 : F) ^ ⌊√(|V| / 69)⌋ ≤ r` for
every extended formulation of `tspPolytope K V` with `r` inequalities when `|V| ≥ 69`.

## Main definitions

* `tspHardGraph`: the `m`-vertex undirected 3-split correlation graph on `Fin m` (`m ≥ 69`).

## Main results

* `extensionComplexity_corrPolytope_le_tspPolytope_splitV`:
  `xc (corrPolytope K (Fin p)) ≤ xc (tspPolytope K (SplitV (CorrDigraphV p) v₀ pad))`.
* `extensionComplexity_corrPolytope_le_tspHardGraph_face`:
  `xc (corrPolytope K (Fin ⌊√(m / 69)⌋))` is bounded by the exposed `tspHardGraph m` tour face of
  `tspPolytope K (Fin m)` for `69 ≤ m`.
* `three_pow_le_two_pow_mul_extensionComplexity_tspPolytope`:
  for `69 ≤ |V|` and `p = Nat.sqrt (|V| / 69)`,
  `3 ^ p ≤ 2 ^ p * extensionComplexity (tspPolytope K V)`.
* `ceil_three_div_two_pow_le_extensionComplexity_tspPolytope`:
  `⌈(3 / 2) ^ Nat.sqrt (|V| / 69)⌉ ≤ extensionComplexity (tspPolytope K V)`.
* `HasExtendedFormulation.three_div_two_pow_le_of_tspPolytope`:
  for `69 ≤ |V|`, any extended formulation of `tspPolytope K V` with `r` inequalities satisfies
  `(3 / 2 : F) ^ Nat.sqrt (|V| / 69) ≤ r`.
* `three_pow_le_two_pow_mul_extensionComplexity_tspPolytope_fin`,
  `HasExtendedFormulation.three_div_two_pow_le_of_tspPolytope_fin`: `Fin m` (`69 ≤ m`) forms.

## References

* [FioriniMassarPokuttaTiwaryDeWolf2015], Section 3.4 (Lemma 11 and Theorem 12).
* [KaibelWeltge2015], Section 2 (Theorem 1).
-/

public section

section Congruence

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Relabelling the vertices by `e` carries the characteristic vector of a tour `σ₂` of `V₂` to
that of the tour `σ₁` of `V₁` with `σ₂ = e ∘ σ₁`. -/
private theorem funLeft_tspVertex_tourEdgeSet {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    [DecidableEq V₁] [DecidableEq V₂] (e : V₁ ≃ V₂) {σ₁ : Fin (Fintype.card V₁) ≃ V₁}
    {σ₂ : Fin (Fintype.card V₂) ≃ V₂} (hV₁ : 3 ≤ Fintype.card V₁) (hV₂ : 3 ≤ Fintype.card V₂)
    (hcard : Fintype.card V₁ = Fintype.card V₂) (h : ∀ j, σ₂ (finCongr hcard j) = e (σ₁ j)) :
    LinearMap.funLeft K K ⇑(SimpleGraph.Iso.completeGraph e).mapEdgeSet
      (tspVertex K (tourEdgeSet σ₂ hV₂)) = tspVertex K (tourEdgeSet σ₁ hV₁) := by
  have hadd (j : Fin (Fintype.card V₁)) :
      finCongr hcard (j + ⟨1, by omega⟩) = finCongr hcard j + ⟨1, by omega⟩ :=
    Fin.ext (by simp [Fin.val_add, hcard])
  ext ⟨s, hs⟩
  induction s using Sym2.ind with
  | _ u v =>
    refine if_congr ?_ rfl rfl
    change ⟨s(e u, e v), _⟩ ∈ tourEdgeSet σ₂ hV₂ ↔ ⟨s(u, v), hs⟩ ∈ tourEdgeSet σ₁ hV₁
    simp only [tourEdgeSet, Finset.mem_image, Finset.mem_univ, true_and, Subtype.ext_iff]
    refine (finCongr hcard).surjective.exists.trans (exists_congr fun j => ?_)
    rw [← hadd, h, h]
    exact (Sym2.map.injective e.injective).eq_iff (a := s(σ₁ j, σ₁ (j + ⟨1, by omega⟩)))
      (b := s(u, v))

omit [IsStrictOrderedRing K] in
private theorem tspPolytope_funLeft_eq {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    [DecidableEq V₁] [DecidableEq V₂] (e : V₁ ≃ V₂) :
    LinearMap.funLeft K K ⇑(SimpleGraph.Iso.completeGraph e).mapEdgeSet '' tspPolytope K V₂ =
      tspPolytope K V₁ := by
  have hcard : Fintype.card V₁ = Fintype.card V₂ := Fintype.card_congr e
  rw [tspPolytope, LinearMap.image_convexHull, tspPolytope]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_range, Subtype.exists]
  constructor
  · rintro ⟨_, ⟨F, ⟨hV₂, σ₂, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨hcard ▸ hV₂, (finCongr hcard).trans (σ₂.trans e.symm), rfl⟩,
      (funLeft_tspVertex_tourEdgeSet e _ hV₂ hcard fun j => by simp).symm⟩
  · rintro ⟨F, ⟨hV₁, σ₁, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨hcard ▸ hV₁, (finCongr hcard.symm).trans (σ₁.trans e), rfl⟩, rfl⟩,
      funLeft_tspVertex_tourEdgeSet e hV₁ _ hcard fun j => by simp⟩

omit [IsStrictOrderedRing K] in
private theorem extensionComplexity_tspPolytope_congr {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    [DecidableEq V₁] [DecidableEq V₂] (e : V₁ ≃ V₂) :
    extensionComplexity (tspPolytope K V₁) = extensionComplexity (tspPolytope K V₂) :=
  extensionComplexity_eq_of_linearMaps
    (LinearMap.funLeft K K ⇑(SimpleGraph.Iso.completeGraph e).mapEdgeSet)
    (LinearMap.funLeft K K ⇑(SimpleGraph.Iso.completeGraph e.symm).mapEdgeSet)
    (tspPolytope_funLeft_eq e) (tspPolytope_funLeft_eq e.symm)

omit [IsStrictOrderedRing K] in
/-- Reindexing the coordinates by `φ` does not change the extension complexity of the face that
a linear functional cuts out of a set, when the set and the functional are reindexed with it. -/
private theorem extensionComplexity_inter_dotProduct_funLeft {ι₁ ι₂ : Type*} [Fintype ι₁]
    [Fintype ι₂] (φ : ι₁ ≃ ι₂) {P₁ : Set (ι₁ → K)} {P₂ : Set (ι₂ → K)}
    (hP : LinearMap.funLeft K K φ '' P₂ = P₁) {c₁ : ι₁ → K} {c₂ : ι₂ → K}
    (hc : ∀ a, c₂ (φ a) = c₁ a) :
    extensionComplexity (P₁ ∩ {x | c₁ ⬝ᵥ x = 0}) =
      extensionComplexity (P₂ ∩ {y | c₂ ⬝ᵥ y = 0}) := by
  have hdot (y : ι₂ → K) : c₁ ⬝ᵥ LinearMap.funLeft K K φ y = c₂ ⬝ᵥ y := by
    simp only [dotProduct, LinearMap.funLeft_apply, ← hc]
    exact φ.sum_comp fun b => c₂ b * y b
  have h : LinearMap.funLeft K K φ '' (P₂ ∩ {y | c₂ ⬝ᵥ y = 0}) = P₁ ∩ {x | c₁ ⬝ᵥ x = 0} := by
    rw [← hP]
    ext x
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨y, ⟨hy, h0⟩, hx⟩ => ⟨⟨y, hy, hx⟩, hx ▸ (hdot y).trans h0⟩,
      fun ⟨⟨y, hy, hx⟩, h0⟩ => ⟨y, ⟨hy, (hdot y).symm.trans (hx ▸ h0)⟩, hx⟩⟩
  refine extensionComplexity_eq_of_linearMaps _ (LinearMap.funLeft K K φ.symm) h ?_
  rw [← h, Set.image_image]
  exact (Set.image_congr fun y _ => funext fun b => congrArg y (φ.apply_symm_apply b)).trans
    (Set.image_id _)

omit [IsStrictOrderedRing K] in
private theorem extensionComplexity_tspPolytope_inter_map_congr
    {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂] [DecidableEq V₁] [DecidableEq V₂]
    (e : V₁ ≃ V₂) (G : SimpleGraph V₁)
    [DecidableRel G.Adj] [DecidableRel (G.map e.toEmbedding).Adj] :
    let c₁ : ↥(⊤ : SimpleGraph V₁).edgeSet → K := fun a => if a.val ∈ G.edgeSet then 0 else -1
    let c₂ : ↥(⊤ : SimpleGraph V₂).edgeSet → K :=
      fun b => if b.val ∈ (G.map e.toEmbedding).edgeSet then 0 else -1
    extensionComplexity (tspPolytope K V₁ ∩ {x | c₁ ⬝ᵥ x = 0}) =
      extensionComplexity (tspPolytope K V₂ ∩ {x | c₂ ⬝ᵥ x = 0}) := by
  intro c₁ c₂
  refine extensionComplexity_inter_dotProduct_funLeft
    (SimpleGraph.Iso.completeGraph e).mapEdgeSet (tspPolytope_funLeft_eq e) fun ⟨s, hs⟩ => ?_
  induction s using Sym2.ind with
  | _ u v =>
    exact if_congr (SimpleGraph.map_adj_apply (G := G) (f := e.toEmbedding) (a := u) (b := v))
      rfl rfl

end Congruence

section Reduction

private def corrPairVar {p : ℕ} (i j : Fin p) : CorrVar p :=
  if h1 : i < j then .off ⟨i, j, h1⟩
  else if h2 : j < i then .off ⟨j, i, h2⟩
  else .diag i

private def corrPairEdge {p : ℕ} (hp : 1 ≤ p) (v₀ : CorrDigraphV p) (pad : ℕ)
    (i j : Fin p) : ↥(⊤ : SimpleGraph (SplitV (CorrDigraphV p) v₀ pad)).edgeSet :=
  ⟨s(SplitV.vOut (.chain (corrPairVar i j) ⟨1, by
      have := two_le_chainLen hp (corrPairVar i j); omega⟩),
    SplitV.vIn (.chain (corrPairVar i j) ⟨0, by
      have := two_le_chainLen hp (corrPairVar i j); omega⟩)),
    splitV_top_edge_vOut_vIn v₀ pad _ _⟩

private theorem corrPairEdge_mem_iff_tour {p : ℕ} [NeZero p] (hp : 1 ≤ p)
    (v₀ : CorrDigraphV p) (pad : ℕ)
    {τ : Fin (Fintype.card (CorrDigraphV p)) ≃ CorrDigraphV p}
    (b : Finset (Fin p))
    (hdiag : ∀ i : Fin p,
      (∃ t : Fin (Fintype.card (CorrDigraphV p)),
        τ t = .chain (.diag i) ⟨1, by have := two_le_chainLen hp (.diag i); omega⟩ ∧
        τ (t + 1) = .chain (.diag i) ⟨0, by have := two_le_chainLen hp (.diag i); omega⟩) ↔
        i ∈ b)
    (hoff : ∀ e : CorrPairIdx p,
      (∃ t : Fin (Fintype.card (CorrDigraphV p)),
        τ t = .chain (.off e) ⟨1, by have := two_le_chainLen hp (.off e); omega⟩ ∧
        τ (t + 1) = .chain (.off e) ⟨0, by have := two_le_chainLen hp (.off e); omega⟩) ↔
        e.fst ∈ b ∧ e.snd ∈ b)
    {F : Finset ↥(⊤ : SimpleGraph (SplitV (CorrDigraphV p) v₀ pad)).edgeSet}
    (hinter : ∀ u w : CorrDigraphV p,
      ⟨s(SplitV.vOut u, SplitV.vIn w), splitV_top_edge_vOut_vIn v₀ pad u w⟩ ∈ F ↔
        ∃ t, τ t = u ∧ τ (t + 1) = w)
    (i j : Fin p) :
    corrPairEdge hp v₀ pad i j ∈ F ↔ i ∈ b ∧ j ∈ b := by
  -- The reverse first chain edge of a variable is on the tour exactly when the variable is true.
  have hvar (v : CorrVar p) :
      (∃ t, τ t = .chain v ⟨1, by have := two_le_chainLen hp v; omega⟩ ∧
        τ (t + 1) = .chain v ⟨0, by have := two_le_chainLen hp v; omega⟩) ↔
      match v with
      | .diag i => i ∈ b
      | .off e => e.fst ∈ b ∧ e.snd ∈ b := by
    cases v
    exacts [hdiag _, hoff _]
  dsimp only [corrPairEdge]
  rw [hinter, hvar]
  unfold corrPairVar
  split_ifs with h1 h2
  · rfl
  · exact and_comm
  · obtain rfl : i = j := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
    exact and_self_iff.symm

private theorem extensionComplexity_corrPolytope_le_splitV_face
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : ℕ) (hp : 1 ≤ p) (v₀ : CorrDigraphV p) (pad : ℕ)
    [DecidableRel (paddedSplitGraph v₀ pad (corrDigraphAdj p hp)).Adj] :
    let W := SplitV (CorrDigraphV p) v₀ pad
    let c : ↥(⊤ : SimpleGraph W).edgeSet → K :=
      fun e => if e.val ∈ (paddedSplitGraph v₀ pad (corrDigraphAdj p hp)).edgeSet then 0 else -1
    extensionComplexity (corrPolytope K (Fin p)) ≤
      extensionComplexity (tspPolytope K W ∩ {x | c ⬝ᵥ x = 0}) := by
  classical
  intro W c
  have : Nonempty (CorrDigraphV p) := ⟨v₀⟩
  have : NeZero p := ⟨by omega⟩
  let π : (↥(⊤ : SimpleGraph W).edgeSet → K) →ₗ[K] ((Fin p × Fin p) → K) :=
    { toFun := fun x q => x (corrPairEdge hp v₀ pad q.1 q.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hproj : π '' (tspPolytope K W ∩ {x | c ⬝ᵥ x = 0}) = corrPolytope K (Fin p) := by
    rw [tspPolytope_inter_subgraph_eq (K := K) (paddedSplitGraph v₀ pad (corrDigraphAdj p hp)),
      LinearMap.image_convexHull, corrPolytope]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range, Subtype.exists]
    constructor
    · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
      obtain ⟨τ, hτ, hinter⟩ := exists_dirTour_of_paddedSplitTour v₀ pad (corrDigraphAdj p hp)
        (two_le_card_corrDigraphV hp) hF
      obtain ⟨b, hdiag, hoff⟩ := exists_assignment_of_dirTour hp hτ
      exact ⟨b, funext fun ⟨i, j⟩ => if_congr
        (corrPairEdge_mem_iff_tour hp v₀ pad b hdiag hoff hinter i j).symm rfl rfl⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨τ, hτ, hdiag, hoff⟩ := exists_dirTour_of_assignment hp b
      obtain ⟨F, hF, hinter⟩ := paddedSplitTour_of_dirTour v₀ pad (corrDigraphAdj p hp)
        (two_le_card_corrDigraphV hp) τ hτ
      exact ⟨_, ⟨F, hF, rfl⟩, funext fun ⟨i, j⟩ => if_congr
        (corrPairEdge_mem_iff_tour hp v₀ pad b hdiag hoff hinter i j) rfl rfl⟩
  rw [← hproj]
  exact extensionComplexity_image_linearMap_le _ π

/-- `corrPolytope K (Fin p)` is a linear projection of a face of the symmetric TSP polytope on
`SplitV (CorrDigraphV p) v₀ pad` vertices
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.4, Lemma 11]. -/
theorem extensionComplexity_corrPolytope_le_tspPolytope_splitV
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : ℕ) (hp : 1 ≤ p) (v₀ : CorrDigraphV p) (pad : ℕ) :
    extensionComplexity (corrPolytope K (Fin p)) ≤
      extensionComplexity (tspPolytope K (SplitV (CorrDigraphV p) v₀ pad)) := by
  classical
  exact (extensionComplexity_corrPolytope_le_splitV_face p hp v₀ pad).trans
    (extensionComplexity_inter_dotProduct_eq_le _ _ 0)

end Reduction

section LowerBound

private noncomputable def tspSplitEquiv (V : Type*) [Fintype V]
    {n : ℕ} (hn : 69 ≤ n) (hcard : Fintype.card V = n) :
    let p := Nat.sqrt (n / 69)
    let hp : 1 ≤ p := Nat.sqrt_pos.2 (by omega)
    let v₀ : CorrDigraphV p := .gate (.diag ⟨0, hp⟩)
    let pad := n - 3 * Fintype.card (CorrDigraphV p)
    SplitV (CorrDigraphV p) v₀ pad ≃ V := by
  intro p hp v₀ pad
  have hsq : p ^ 2 ≤ n / 69 := Nat.sqrt_le' (n / 69)
  have hcardV : Fintype.card (CorrDigraphV p) ≤ 23 * p ^ 2 := card_corrDigraphV_le hp
  have hle : 3 * Fintype.card (CorrDigraphV p) ≤ n := by omega
  exact Fintype.equivOfCardEq (by rw [card_splitV]; omega)

/-- An explicit `m`-vertex graph (`m ≥ 69`) obtained by transporting the 3-split correlation graph
with padding onto `Fin m` [FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 11 and Theorem 12]. -/
noncomputable def tspHardGraph (m : ℕ) : SimpleGraph (Fin m) :=
  if hm : 69 ≤ m then
    let p := Nat.sqrt (m / 69)
    let hp : 1 ≤ p := Nat.sqrt_pos.2 (by omega)
    let v₀ : CorrDigraphV p := .gate (.diag ⟨0, hp⟩)
    let pad := m - 3 * Fintype.card (CorrDigraphV p)
    let e : SplitV (CorrDigraphV p) v₀ pad ≃ Fin m :=
      tspSplitEquiv (Fin m) hm (Fintype.card_fin m)
    SimpleGraph.map e.toEmbedding (paddedSplitGraph v₀ pad (corrDigraphAdj p hp))
  else ⊥

/-- For `m ≥ 69`, `corrPolytope K (Fin (Nat.sqrt (m / 69)))` has extension complexity at most
that of the Hamiltonian-tour face of `tspPolytope K (Fin m)` supported on `tspHardGraph m`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.4, Lemma 11]. -/
theorem extensionComplexity_corrPolytope_le_tspHardGraph_face
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (m : ℕ) (hm : 69 ≤ m) [DecidableRel (tspHardGraph m).Adj] :
    let c : ↥(⊤ : SimpleGraph (Fin m)).edgeSet → K :=
      fun e => if e.val ∈ (tspHardGraph m).edgeSet then 0 else -1
    extensionComplexity (corrPolytope K (Fin (Nat.sqrt (m / 69)))) ≤
      extensionComplexity (tspPolytope K (Fin m) ∩ {x | c ⬝ᵥ x = 0}) := by
  classical
  intro c
  let p := Nat.sqrt (m / 69)
  have hp : 1 ≤ p := Nat.sqrt_pos.2 (by omega)
  let v₀ : CorrDigraphV p := .gate (.diag ⟨0, hp⟩)
  let pad := m - 3 * Fintype.card (CorrDigraphV p)
  let e : SplitV (CorrDigraphV p) v₀ pad ≃ Fin m :=
    tspSplitEquiv (Fin m) hm (Fintype.card_fin m)
  let G : SimpleGraph (SplitV (CorrDigraphV p) v₀ pad) :=
    paddedSplitGraph v₀ pad (corrDigraphAdj p hp)
  have hmap : tspHardGraph m = G.map e.toEmbedding := by rw [tspHardGraph, dite_eq_left hm]
  have hc_eq : c = fun b => if b.val ∈ (G.map e.toEmbedding).edgeSet then (0 : K) else -1 :=
    funext fun b => if_congr (by rw [hmap]) rfl rfl
  rw [hc_eq, ← extensionComplexity_tspPolytope_inter_map_congr (K := K) e G]
  exact extensionComplexity_corrPolytope_le_splitV_face p hp v₀ pad

/-- The Kaibel–Weltge bound for `corrPolytope K (Fin p)` passes to every set whose extension
complexity is at least that of the correlation polytope. -/
private theorem three_pow_le_two_pow_mul_of_corrPolytope_le
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {ι : Type*} [Fintype ι]
    {P : Set (ι → K)} {p : ℕ} (hp : 1 ≤ p)
    (h : extensionComplexity (corrPolytope K (Fin p)) ≤ extensionComplexity P) :
    ((3 ^ p : ℕ) : ℕ∞) ≤ (2 ^ p : ℕ∞) * extensionComplexity P := by
  have : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  have h1 := three_pow_le_two_pow_mul_extensionComplexity_corrPolytope (K := K) (α := Fin p)
  rw [Fintype.card_fin] at h1
  exact h1.trans (mul_le_mul_right h _)

/-- Exponential `2^{Ω(√|V|)}` lower bound for the symmetric TSP polytope `tspPolytope K V` for any
finite vertex type `V` with `|V| ≥ 69` (`p = ⌊√(|V| / 69)⌋`):
`3 ^ p ≤ 2 ^ p * xc (tspPolytope K V)` in `ℕ∞`
[FioriniMassarPokuttaTiwaryDeWolf2015, Theorem 12]; [KaibelWeltge2015, Theorem 1]. -/
theorem three_pow_le_two_pow_mul_extensionComplexity_tspPolytope
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (V : Type*) [Fintype V] [DecidableEq V] (hV : 69 ≤ Fintype.card V) :
    ((3 ^ Nat.sqrt (Fintype.card V / 69) : ℕ) : ℕ∞) ≤
      (2 ^ Nat.sqrt (Fintype.card V / 69) : ℕ∞) * extensionComplexity (tspPolytope K V) := by
  have hp : 1 ≤ Nat.sqrt (Fintype.card V / 69) := Nat.sqrt_pos.2 (by omega)
  exact three_pow_le_two_pow_mul_of_corrPolytope_le hp
    ((extensionComplexity_corrPolytope_le_tspPolytope_splitV _ hp (.gate (.diag ⟨0, hp⟩))
      _).trans_eq (extensionComplexity_tspPolytope_congr (tspSplitEquiv V hV rfl)))

/-- Integer-ceiling lower bound for `tspPolytope K V` (`|V| ≥ 69`):
`⌈(3 / 2) ^ Nat.sqrt (|V| / 69)⌉ ≤ xc (tspPolytope K V)`. -/
theorem ceil_three_div_two_pow_le_extensionComplexity_tspPolytope
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (V : Type*) [Fintype V] [DecidableEq V] (hV : 69 ≤ Fintype.card V) :
    (((3 ^ Nat.sqrt (Fintype.card V / 69) + 2 ^ Nat.sqrt (Fintype.card V / 69) - 1) /
        2 ^ Nat.sqrt (Fintype.card V / 69) : ℕ) : ℕ∞) ≤
      extensionComplexity (tspPolytope K V) :=
  ceil_three_div_two_pow_le_of_mul_le_extensionComplexity
    (three_pow_le_two_pow_mul_extensionComplexity_tspPolytope V hV)

/-- Field-valued `2^{Ω(√|V|)}` lower bound: any extended formulation of `tspPolytope K V`
(`|V| ≥ 69`) with `r` inequalities satisfies `(3 / 2 : F) ^ Nat.sqrt (|V| / 69) ≤ r`
[FioriniMassarPokuttaTiwaryDeWolf2015, Theorem 12]; [KaibelWeltge2015, Theorem 1]. -/
theorem HasExtendedFormulation.three_div_two_pow_le_of_tspPolytope
    {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {V : Type*} [Fintype V] [DecidableEq V] (hV : 69 ≤ Fintype.card V)
    {r : ℕ} (hr : HasExtendedFormulation (tspPolytope K V) r) :
    (3 / 2 : F) ^ Nat.sqrt (Fintype.card V / 69) ≤ r :=
  hr.three_div_two_pow_le_of_mul_le (three_pow_le_two_pow_mul_extensionComplexity_tspPolytope V hV)

/-- Specialization of `three_pow_le_two_pow_mul_extensionComplexity_tspPolytope` to `Fin m`
(`m ≥ 69`), routed through `tspHardGraph m`. -/
theorem three_pow_le_two_pow_mul_extensionComplexity_tspPolytope_fin
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (m : ℕ) (hm : 69 ≤ m) :
    ((3 ^ Nat.sqrt (m / 69) : ℕ) : ℕ∞) ≤
      (2 ^ Nat.sqrt (m / 69) : ℕ∞) * extensionComplexity (tspPolytope K (Fin m)) := by
  classical
  exact three_pow_le_two_pow_mul_of_corrPolytope_le (Nat.sqrt_pos.2 (by omega))
    ((extensionComplexity_corrPolytope_le_tspHardGraph_face m hm).trans
      (extensionComplexity_inter_dotProduct_eq_le (tspPolytope K (Fin m)) _ 0))

/-- Field-valued `2^{Ω(√m)}` lower bound for `tspPolytope K (Fin m)` (`m ≥ 69`): any extended
formulation with `r` inequalities satisfies `(3 / 2 : F) ^ Nat.sqrt (m / 69) ≤ r`. -/
theorem HasExtendedFormulation.three_div_two_pow_le_of_tspPolytope_fin
    {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {m r : ℕ} (hm : 69 ≤ m) (hr : HasExtendedFormulation (tspPolytope K (Fin m)) r) :
    (3 / 2 : F) ^ Nat.sqrt (m / 69) ≤ r :=
  hr.three_div_two_pow_le_of_mul_le
    (three_pow_le_two_pow_mul_extensionComplexity_tspPolytope_fin m hm)

end LowerBound
