/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.EdmondsKarp
public import CslibFrontier.Computability.Circuit.BipartiteMatching
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators

/-!
# Maximum Bipartite Matching and König's Theorem via Network Flows

Formalizes the reduction of **maximum bipartite matching** and **minimum bipartite vertex cover**
to integral `s`-`t` network flow ([FordFulkerson1962], Chapter II, Sections 4–5, Theorem 4.1;
[CLRS2009], Section 26.3, Lemma 26.9, Theorem 26.10 & Corollary 26.11, pp. 732–735), derives
**König's Theorem** ([Koenig1931], pp. 116–119), bridges to
`Cslib.Circuits.BipartiteMatching.HasPerfectMatching`, and provides a pure executable solver via
`edmondsKarpDense`. For the checked Word-RAM running-time bound (`O((m + r)^5)` instructions), see
`CslibFrontier.Algorithms.WordRAM.EdmondsKarp`.

## Model and source mapping

* **Bipartite graph (`G : L × R → Bool`):** edge indicator on finite left/right vertex types `L` and
  `R`, matching the convention of `Cslib.Circuits.BipartiteMatching` on `V × V → Bool`.
* **Unit-capacity flow network (`bipartiteNetwork G`):** adds `BipartiteVertex.source` and
  `BipartiteVertex.sink` with unit-capacity arcs `.source → .left u`, `.left u → .right v` whenever
  `G (u, v) = true`, and `.right v → .sink` ([CLRS2009], Section 26.3, pp. 732–733).
* **Flows ↔ matchings (`matchingToFlow`, `flowToMatching`):** every matching `M` yields an integral
  flow of value `M.card`, and every feasible integral flow `f` on `bipartiteNetwork G` induces a
  matching of cardinality `f.value.toNat` (`(M.card : ℤ) = f.value`; [CLRS2009], Lemma 26.9,
  pp. 733–734).
* **Cuts ↔ vertex covers & König's Theorem (`vertexCoverToCut`, `cutToVertexCover`,
  `exists_maxMatching_eq_minVertexCover`):** every vertex cover `C` yields an `s`-`t` cut of
  capacity `C.size`, and every `s`-`t` cut `S` yields a cover of size at most `cutCapacity S`.
  Combining with `Network.exists_maxFlow_eq_minCut` proves that maximum matching size equals minimum
  vertex cover size ([Koenig1931], pp. 116–119; [FordFulkerson1962], Chapter II, Section 4,
  Theorem 4.1).
* **Pure executable solver (`bipartiteMatching`, `decidePerfectMatching`):** transports
  `bipartiteNetwork G` onto `Fin (2 + (m + r))`, runs `edmondsKarpDense`, and extracts the
  resulting matching and König cover.

## Main definitions

* `Cslib.Algorithms.Lean.MaxFlow.IsMatching`, `IsMaxMatching`: bipartite matchings and maximum
  matchings.
* `Cslib.Algorithms.Lean.MaxFlow.VertexCover`, `IsVertexCover`, `IsMinVertexCover`: bipartite
  vertex covers and minimum vertex covers.
* `Cslib.Algorithms.Lean.MaxFlow.BipartiteVertex`, `bipartiteNetwork`, `matchingToFlow`,
  `flowToMatching`, `vertexCoverToCut`, `cutToVertexCover`: unit-capacity flow reduction.
* `Cslib.Algorithms.Lean.MaxFlow.BipartiteOutput`, `bipartiteMatching`, `decidePerfectMatching`:
  pure executable solver for maximum bipartite matching, minimum vertex cover, and perfect
  matching decision.

## Main results

* `Cslib.Algorithms.Lean.MaxFlow.card_le_size_of_matching_vertexCover`: weak duality (`M.card ≤
  C.size`).
* `Cslib.Algorithms.Lean.MaxFlow.exists_maxMatching_eq_minVertexCover`: **König's Theorem**.
* `Cslib.Algorithms.Lean.MaxFlow.hasPerfectMatching_iff_exists_matching_card` and
  `hasPerfectMatching_iff_exists_flow_value_card`: characterizations of
  `Cslib.Circuits.BipartiteMatching.HasPerfectMatching`.
* `Cslib.Algorithms.Lean.MaxFlow.bipartiteMatching_correct` and
  `decidePerfectMatching_eq_true_iff`: correctness of the pure executable solver.

## References

* [D. König, *Gráfok és mátrixok*][Koenig1931]
* [L. R. Ford, Jr. and D. R. Fulkerson, *Flows in Networks*][FordFulkerson1962]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow


/-! ### Bipartite matchings and vertex covers -/

section Definitions

variable {L R : Type*}

/-- `M` is a matching in the bipartite graph `G : L × R → Bool` if every pair in `M` is an edge of
`G` and no two edges in `M` share a left endpoint or a right endpoint. -/
@[expose] def IsMatching (G : L × R → Bool) (M : Finset (L × R)) : Prop :=
  (∀ e ∈ M, G e = true) ∧
    (∀ u v₁ v₂, (u, v₁) ∈ M → (u, v₂) ∈ M → v₁ = v₂) ∧
    (∀ u₁ u₂ v, (u₁, v) ∈ M → (u₂, v) ∈ M → u₁ = u₂)

instance instDecidableIsMatching [DecidableEq L] [DecidableEq R] (G : L × R → Bool)
    (M : Finset (L × R)) : Decidable (IsMatching G M) := by
  refine decidable_of_iff
    ((∀ e ∈ M, G e = true) ∧
      (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁.1 = e₂.1 → e₁.2 = e₂.2) ∧
      (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁.2 = e₂.2 → e₁.1 = e₂.1)) ?_
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun u v₁ v₂ m₁ m₂ => h2 (u, v₁) m₁ (u, v₂) m₂ rfl,
      fun u₁ u₂ v m₁ m₂ => h3 (u₁, v) m₁ (u₂, v) m₂ rfl⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · rintro ⟨u₁, v₁⟩ m₁ ⟨u₂, v₂⟩ m₂ (hu : u₁ = u₂)
      subst hu
      exact h2 u₁ v₁ v₂ m₁ m₂
    · rintro ⟨u₁, v₁⟩ m₁ ⟨u₂, v₂⟩ m₂ (hv : v₁ = v₂)
      subst hv
      exact h3 u₁ u₂ v₁ m₁ m₂

/-- `M` is a maximum-cardinality matching in `G`. -/
@[expose] def IsMaxMatching (G : L × R → Bool) (M : Finset (L × R)) : Prop :=
  IsMatching G M ∧ ∀ M' : Finset (L × R), IsMatching G M' → M'.card ≤ M.card

/-- A bipartite vertex cover on `(L, R)`, consisting of chosen `left` and `right` vertex subsets. -/
structure VertexCover (L R : Type*) where
  /-- Chosen left vertices. -/
  left : Finset L
  /-- Chosen right vertices. -/
  right : Finset R

instance instDecidableEqVertexCover [DecidableEq L] [DecidableEq R] :
    DecidableEq (VertexCover L R) :=
  fun a b => decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    (by cases a; cases b; simp)

/-- Total cardinality `|C.left| + |C.right|` of a bipartite vertex cover `C`. -/
@[expose] def VertexCover.size (C : VertexCover L R) : ℕ :=
  C.left.card + C.right.card

/-- `C` is a vertex cover of `G` if every edge `(u, v)` with `G (u, v) = true` has `u ∈ C.left` or
`v ∈ C.right`. -/
@[expose] def IsVertexCover (G : L × R → Bool) (C : VertexCover L R) : Prop :=
  ∀ u v, G (u, v) = true → u ∈ C.left ∨ v ∈ C.right

instance instDecidableIsVertexCover [Fintype L] [Fintype R] [DecidableEq L]
    [DecidableEq R] (G : L × R → Bool) (C : VertexCover L R) :
    Decidable (IsVertexCover G C) := by
  unfold IsVertexCover
  infer_instance

/-- `C` is a minimum-cardinality vertex cover of `G`. -/
@[expose] def IsMinVertexCover (G : L × R → Bool) (C : VertexCover L R) : Prop :=
  IsVertexCover G C ∧ ∀ C' : VertexCover L R, IsVertexCover G C' → C.size ≤ C'.size

end Definitions

/-! ### Unit-capacity flow network for a bipartite graph -/

section FlowReduction

variable {L R : Type*}

/-- Vertices of the unit-capacity `s`-`t` flow network for a bipartite graph on `(L, R)`:
designated `source` and `sink` together with `left u` (`u : L`) and `right v` (`v : R`). -/
inductive BipartiteVertex (L R : Type*)
  | source
  | sink
  | left (u : L)
  | right (v : R)

/-- Canonical equivalence between `BipartiteVertex L R` and `Bool ⊕ (L ⊕ R)`. -/
@[expose] def bipartiteVertexEquiv (L R : Type*) : BipartiteVertex L R ≃ Bool ⊕ (L ⊕ R) where
  toFun
    | .source => .inl false
    | .sink => .inl true
    | .left u => .inr (.inl u)
    | .right v => .inr (.inr v)
  invFun
    | .inl false => .source
    | .inl true => .sink
    | .inr (.inl u) => .left u
    | .inr (.inr v) => .right v
  left_inv x := by cases x <;> rfl
  right_inv y := by rcases y with (_ | _) | (_ | _) <;> rfl

instance instDecidableEqBipartiteVertex [DecidableEq L] [DecidableEq R] :
    DecidableEq (BipartiteVertex L R) :=
  (bipartiteVertexEquiv L R).decidableEq

instance instFintypeBipartiteVertex [Fintype L] [Fintype R] :
    Fintype (BipartiteVertex L R) :=
  Fintype.ofEquiv (Bool ⊕ (L ⊕ R)) (bipartiteVertexEquiv L R).symm

theorem sum_bipartiteVertex {M : Type*} [AddCommMonoid M] [Fintype L] [Fintype R]
    (g : BipartiteVertex L R → M) :
    (∑ x : BipartiteVertex L R, g x) =
      g .source + g .sink + (∑ u : L, g (.left u)) + (∑ v : R, g (.right v)) := by
  rw [← (bipartiteVertexEquiv L R).symm.sum_comp, Fintype.sum_sum_type, Fintype.sum_bool,
    Fintype.sum_sum_type]
  simp only [bipartiteVertexEquiv, Equiv.coe_fn_symm_mk]
  rw [add_comm (g .sink) (g .source), ← add_assoc]

/-- Unit-capacity `s`-`t` network associated with `G : L × R → Bool` ([CLRS2009], Section 26.3,
pp. 732–733): unit arcs `.source → .left u`, `.left u → .right v` when `G (u, v) = true`, and
`.right v → .sink`. -/
@[expose] def bipartiteNetwork (G : L × R → Bool) : Network (BipartiteVertex L R) where
  cap x y :=
    match x, y with
    | .source, .left _ => 1
    | .left u, .right v => if G (u, v) then 1 else 0
    | .right _, .sink => 1
    | _, _ => 0
  s := .source
  t := .sink

theorem bipartiteNetwork_s_ne_t (G : L × R → Bool) :
    (bipartiteNetwork G).s ≠ (bipartiteNetwork G).t := by
  simp [bipartiteNetwork]

section FlowProperties

variable [Fintype L] [Fintype R] {G : L × R → Bool}

private theorem flow_in_source_eq_zero (f : (bipartiteNetwork G).Flow) (x : BipartiteVertex L R) :
    f x .source = 0 := by
  have h := f.le_cap x .source
  cases x <;> simp only [bipartiteNetwork] at h <;> omega

private theorem flow_source_out_eq_sum_left (f : (bipartiteNetwork G).Flow) :
    (∑ y : BipartiteVertex L R, f .source y) = ∑ u : L, f .source (.left u) := by
  rw [sum_bipartiteVertex]
  have hs : f .source .source = 0 := Nat.eq_zero_of_le_zero (f.le_cap .source .source)
  have ht : f .source .sink = 0 := Nat.eq_zero_of_le_zero (f.le_cap .source .sink)
  have hr : (∑ v : R, f .source (.right v)) = 0 :=
    Finset.sum_eq_zero fun v _ => Nat.eq_zero_of_le_zero (f.le_cap .source (.right v))
  omega

theorem bipartiteFlow_value_eq_sum_left (f : (bipartiteNetwork G).Flow) :
    f.value = ∑ u : L, (f .source (.left u) : ℤ) := by
  unfold Network.Flow.value Network.Flow.netOut
  change (∑ y : BipartiteVertex L R, (f .source y : ℤ)) -
      (∑ x : BipartiteVertex L R, (f x .source : ℤ)) = _
  have hin : (∑ x : BipartiteVertex L R, (f x .source : ℤ)) = 0 :=
    Finset.sum_eq_zero fun x _ => by simp [flow_in_source_eq_zero f x]
  have hout : (∑ y : BipartiteVertex L R, (f .source y : ℤ)) =
      ∑ u : L, (f .source (.left u) : ℤ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, flow_source_out_eq_sum_left f]
  omega

theorem bipartiteFlow_left_conserve (f : (bipartiteNetwork G).Flow) (u : L) :
    (∑ v : R, f (.left u) (.right v)) = f .source (.left u) := by
  have hcons := f.conserve (.left u) (by simp [bipartiteNetwork]) (by simp [bipartiteNetwork])
  rw [sum_bipartiteVertex, sum_bipartiteVertex] at hcons
  have h_out_s : f (.left u) .source = 0 := Nat.eq_zero_of_le_zero (f.le_cap (.left u) .source)
  have h_out_t : f (.left u) .sink = 0 := Nat.eq_zero_of_le_zero (f.le_cap (.left u) .sink)
  have h_out_l : (∑ u' : L, f (.left u) (.left u')) = 0 :=
    Finset.sum_eq_zero fun u' _ => Nat.eq_zero_of_le_zero (f.le_cap (.left u) (.left u'))
  have h_in_t : f .sink (.left u) = 0 := Nat.eq_zero_of_le_zero (f.le_cap .sink (.left u))
  have h_in_l : (∑ u' : L, f (.left u') (.left u)) = 0 :=
    Finset.sum_eq_zero fun u' _ => Nat.eq_zero_of_le_zero (f.le_cap (.left u') (.left u))
  have h_in_r : (∑ v : R, f (.right v) (.left u)) = 0 :=
    Finset.sum_eq_zero fun v _ => Nat.eq_zero_of_le_zero (f.le_cap (.right v) (.left u))
  omega

theorem bipartiteFlow_right_conserve (f : (bipartiteNetwork G).Flow) (v : R) :
    (∑ u : L, f (.left u) (.right v)) = f (.right v) .sink := by
  have hcons := f.conserve (.right v) (by simp [bipartiteNetwork]) (by simp [bipartiteNetwork])
  rw [sum_bipartiteVertex, sum_bipartiteVertex] at hcons
  have h_out_s : f (.right v) .source = 0 := Nat.eq_zero_of_le_zero (f.le_cap (.right v) .source)
  have h_out_l : (∑ u : L, f (.right v) (.left u)) = 0 :=
    Finset.sum_eq_zero fun u _ => Nat.eq_zero_of_le_zero (f.le_cap (.right v) (.left u))
  have h_out_r : (∑ v' : R, f (.right v) (.right v')) = 0 :=
    Finset.sum_eq_zero fun v' _ => Nat.eq_zero_of_le_zero (f.le_cap (.right v) (.right v'))
  have h_in_s : f .source (.right v) = 0 := Nat.eq_zero_of_le_zero (f.le_cap .source (.right v))
  have h_in_t : f .sink (.right v) = 0 := Nat.eq_zero_of_le_zero (f.le_cap .sink (.right v))
  have h_in_r : (∑ v' : R, f (.right v') (.right v)) = 0 :=
    Finset.sum_eq_zero fun v' _ => Nat.eq_zero_of_le_zero (f.le_cap (.right v') (.right v))
  omega

/-- Extract a bipartite matching from any feasible integral flow `f` on `bipartiteNetwork G` by
selecting pairs `(u, v)` carrying positive flow ([CLRS2009], Lemma 26.9, p. 733). -/
@[expose] def flowToMatching (f : (bipartiteNetwork G).Flow) : Finset (L × R) :=
  Finset.univ.filter fun e => 0 < f (.left e.1) (.right e.2)

/-- Two positive terms of a sum of naturals that is at most `1` are the same term. Shared by the
left and right uniqueness halves of `isMatching_flowToMatching`. -/
private theorem eq_of_sum_le_one {ι : Type*} [Fintype ι] {g : ι → ℕ} (hg : ∑ i, g i ≤ 1)
    {i j : ι} (hi : 0 < g i) (hj : 0 < g j) : i = j := by
  classical
  by_contra hne
  have hsub : ∑ k ∈ ({i, j} : Finset ι), g k ≤ ∑ k, g k :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_pair hne] at hsub
  omega

theorem isMatching_flowToMatching (f : (bipartiteNetwork G).Flow) :
    IsMatching G (flowToMatching f) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨u, v⟩ he
    simp only [flowToMatching, Finset.mem_filter, Finset.mem_univ, true_and] at he
    have hcap := f.le_cap (.left u) (.right v)
    simp only [bipartiteNetwork] at hcap
    cases hG : G (u, v)
    · rw [hG] at hcap
      simp only [Bool.false_eq_true, ↓reduceIte] at hcap
      omega
    · rfl
  · intro u v₁ v₂ hv₁ hv₂
    simp only [flowToMatching, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
    refine eq_of_sum_le_one (g := fun v => f (.left u) (.right v)) ?_ hv₁ hv₂
    rw [bipartiteFlow_left_conserve f u]
    exact f.le_cap .source (.left u)
  · intro u₁ u₂ v hu₁ hu₂
    simp only [flowToMatching, Finset.mem_filter, Finset.mem_univ, true_and] at hu₁ hu₂
    refine eq_of_sum_le_one (g := fun u => f (.left u) (.right v)) ?_ hu₁ hu₂
    rw [bipartiteFlow_right_conserve f v]
    exact f.le_cap (.right v) .sink

theorem card_flowToMatching_coe (f : (bipartiteNetwork G).Flow) :
    ((flowToMatching f).card : ℤ) = f.value := by
  have h01 : ∀ u : L, ∀ v : R,
      (if 0 < f (.left u) (.right v) then 1 else 0) = f (.left u) (.right v) := by
    intro u v
    have hle : f (.left u) (.right v) ≤ 1 := by
      have hcap := f.le_cap (.left u) (.right v)
      simp only [bipartiteNetwork] at hcap
      split_ifs at hcap <;> omega
    split_ifs <;> omega
  have hcard : (flowToMatching f).card = ∑ u : L, f .source (.left u) := by
    rw [flowToMatching, Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    exact Finset.sum_congr rfl fun u _ =>
      (Finset.sum_congr rfl fun v _ => h01 u v).trans (bipartiteFlow_left_conserve f u)
  rw [hcard, bipartiteFlow_value_eq_sum_left, Nat.cast_sum]

/-- Construct a feasible unit integral flow on `bipartiteNetwork G` of value `M.card` from any
bipartite matching `M` ([CLRS2009], Lemma 26.9, p. 733). -/
@[expose] def matchingToFlow [DecidableEq L] [DecidableEq R] {M : Finset (L × R)}
    (hM : IsMatching G M) : (bipartiteNetwork G).Flow where
  toFun x y :=
    match x, y with
    | .source, .left u => if ∃ v : R, (u, v) ∈ M then 1 else 0
    | .left u, .right v => if (u, v) ∈ M then 1 else 0
    | .right v, .sink => if ∃ u : L, (u, v) ∈ M then 1 else 0
    | _, _ => 0
  le_cap x y := by
    obtain ⟨hM_edge, _, _⟩ := hM
    cases x <;> cases y <;> simp only [bipartiteNetwork]
    all_goals try exact Nat.zero_le _
    · split_ifs <;> omega
    · rename_i u v
      by_cases hmem : (u, v) ∈ M
      · simp [hmem, hM_edge (u, v) hmem]
      · simp [hmem]
    · split_ifs <;> omega
  conserve x hxs hxt := by
    obtain ⟨_, hM_left, hM_right⟩ := hM
    cases x with
    | source => exact absurd rfl hxs
    | sink => exact absurd rfl hxt
    | left u =>
      rw [sum_bipartiteVertex, sum_bipartiteVertex]
      simp only [Nat.zero_add, Finset.sum_const_zero, Nat.add_zero]
      by_cases hex : ∃ v : R, (u, v) ∈ M
      · simp only [hex, ↓reduceIte]
        obtain ⟨v₀, hv₀⟩ := hex
        symm
        rw [Finset.sum_eq_single v₀
          (fun v _ hne => by
            have hnot : (u, v) ∉ M := fun hv => hne (hM_left u v v₀ hv hv₀)
            simp only [hnot, ↓reduceIte])
          (fun h => absurd (Finset.mem_univ v₀) h)]
        simp only [hv₀, ↓reduceIte]
      · simp only [hex, ↓reduceIte]
        symm
        exact Finset.sum_eq_zero fun v _ => by
          have hnot : (u, v) ∉ M := fun hv => hex ⟨v, hv⟩
          simp only [hnot, ↓reduceIte]
    | right v =>
      rw [sum_bipartiteVertex, sum_bipartiteVertex]
      simp only [Nat.zero_add, Finset.sum_const_zero, Nat.add_zero]
      by_cases hex : ∃ u : L, (u, v) ∈ M
      · simp only [hex, ↓reduceIte]
        obtain ⟨u₀, hu₀⟩ := hex
        rw [Finset.sum_eq_single u₀
          (fun u _ hne => by
            have hnot : (u, v) ∉ M := fun hu => hne (hM_right u u₀ v hu hu₀)
            simp only [hnot, ↓reduceIte])
          (fun h => absurd (Finset.mem_univ u₀) h)]
        simp only [hu₀, ↓reduceIte]
      · simp only [hex, ↓reduceIte]
        exact Finset.sum_eq_zero fun u _ => by
          have hnot : (u, v) ∉ M := fun hu => hex ⟨u, hu⟩
          simp only [hnot, ↓reduceIte]

@[simp]
theorem value_matchingToFlow [DecidableEq L] [DecidableEq R] {M : Finset (L × R)}
    (hM : IsMatching G M) : (matchingToFlow hM).value = (M.card : ℤ) := by
  rw [bipartiteFlow_value_eq_sum_left, ← Nat.cast_sum, Nat.cast_inj]
  calc ∑ u : L, (matchingToFlow hM) .source (.left u)
      = ∑ e : L × R, if e ∈ M then 1 else 0 := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
        exact Finset.sum_congr rfl fun u _ => (bipartiteFlow_left_conserve _ u).symm
    _ = M.card := by rw [← Finset.card_filter]; congr 1; ext; simp

end FlowProperties

/-! ### Cuts, vertex covers, and König's Theorem -/

section Koenig

variable [Fintype L] [Fintype R] {G : L × R → Bool}

private theorem bipartiteNetwork_cutCapacity_eq [DecidableEq L] [DecidableEq R]
    {S : Finset (BipartiteVertex L R)} (hS : (bipartiteNetwork G).IsCut S) :
    (bipartiteNetwork G).cutCapacity S =
      (∑ u : L, if .left u ∉ S then 1 else 0) +
        (∑ u : L, ∑ v : R,
          if .left u ∈ S ∧ .right v ∉ S ∧ G (u, v) = true then 1 else 0) +
        (∑ v : R, if .right v ∈ S then 1 else 0) := by
  have hs_in : BipartiteVertex.source ∈ S := hS.1
  have ht_out : BipartiteVertex.sink ∉ S := hS.2
  have hexpand :
      (bipartiteNetwork G).cutCapacity S =
        ∑ x : BipartiteVertex L R, ∑ y : BipartiteVertex L R,
          if x ∈ S ∧ y ∉ S then (bipartiteNetwork G).cap x y else 0 := by
    unfold Network.cutCapacity
    have hmem : S = Finset.univ.filter (fun x : BipartiteVertex L R => x ∈ S) := by ext x; simp
    have hsdiff : Finset.univ \ S = Finset.univ.filter (fun y : BipartiteVertex L R => y ∉ S) := by
      ext y; simp
    rw [hsdiff]
    conv_lhs => rw [hmem]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ S
    · simp [hx, Finset.sum_filter]
    · simp [hx]
  rw [hexpand, sum_bipartiteVertex]
  have h_src :
      (∑ y : BipartiteVertex L R,
          if BipartiteVertex.source ∈ S ∧ y ∉ S then (bipartiteNetwork G).cap .source y else 0) =
        ∑ u : L, if .left u ∉ S then 1 else 0 := by
    rw [sum_bipartiteVertex]
    simp [bipartiteNetwork, hs_in]
  have h_snk :
      (∑ y : BipartiteVertex L R,
          if BipartiteVertex.sink ∈ S ∧ y ∉ S then
            (bipartiteNetwork G).cap .sink y
          else 0) = 0 := by
    simp [ht_out]
  have h_left :
      (∑ u : L, ∑ y : BipartiteVertex L R,
          if BipartiteVertex.left u ∈ S ∧ y ∉ S then
            (bipartiteNetwork G).cap (.left u) y
          else 0) =
        ∑ u : L, ∑ v : R,
          if .left u ∈ S ∧ .right v ∉ S ∧ G (u, v) = true then 1 else 0 := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [sum_bipartiteVertex]
    simp only [bipartiteNetwork, ite_self, Nat.zero_add, Finset.sum_const_zero]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h1 : BipartiteVertex.left u ∈ S <;>
      by_cases h2 : BipartiteVertex.right v ∉ S <;>
      cases G (u, v) <;> simp [h1, h2]
  have h_right :
      (∑ v : R, ∑ y : BipartiteVertex L R,
          if BipartiteVertex.right v ∈ S ∧ y ∉ S then
            (bipartiteNetwork G).cap (.right v) y
          else 0) =
        ∑ v : R, if .right v ∈ S then 1 else 0 := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [sum_bipartiteVertex]
    simp [bipartiteNetwork, ht_out]
  rw [h_src, h_snk, h_left, h_right]
  omega

/-- Boolean membership predicate for `vertexCoverToCut C`. -/
private def vertexCoverCutPred [DecidableEq L] [DecidableEq R]
    (C : VertexCover L R) : BipartiteVertex L R → Bool
  | .source => true
  | .sink => false
  | .left u => decide (u ∉ C.left)
  | .right v => decide (v ∈ C.right)

/-- Turn a bipartite vertex cover `C` into an `s`-`t` cut of `bipartiteNetwork G` of capacity
`C.size` ([FordFulkerson1962], Chapter II, Section 4, Theorem 4.1). -/
def vertexCoverToCut [DecidableEq L] [DecidableEq R]
    (C : VertexCover L R) : Finset (BipartiteVertex L R) :=
  Finset.univ.filter fun x => vertexCoverCutPred C x = true

theorem isCut_vertexCoverToCut [DecidableEq L] [DecidableEq R]
    (C : VertexCover L R) : (bipartiteNetwork G).IsCut (vertexCoverToCut C) := by
  simp [Network.IsCut, bipartiteNetwork, vertexCoverToCut, vertexCoverCutPred]

theorem cutCapacity_vertexCoverToCut [DecidableEq L] [DecidableEq R]
    {C : VertexCover L R} (hC : IsVertexCover G C) :
    (bipartiteNetwork G).cutCapacity (vertexCoverToCut C) = C.size := by
  have hzero : ∀ u v, ¬(BipartiteVertex.left u ∈ vertexCoverToCut C ∧
      BipartiteVertex.right v ∉ vertexCoverToCut C ∧ G (u, v) = true) := by
    rintro u v ⟨hu, hv, hG⟩
    rcases hC u v hG with h | h <;> simp_all [vertexCoverToCut, vertexCoverCutPred]
  simp only [bipartiteNetwork_cutCapacity_eq (isCut_vertexCoverToCut C), hzero, ↓reduceIte,
    Finset.sum_const_zero, add_zero]
  simp [vertexCoverToCut, vertexCoverCutPred, VertexCover.size]

/-- Extract a bipartite vertex cover of size at most `cutCapacity S` from any `s`-`t` cut `S` of
`bipartiteNetwork G`. -/
@[expose] def cutToVertexCover [DecidableEq L] [DecidableEq R]
    (G : L × R → Bool) (S : Finset (BipartiteVertex L R)) : VertexCover L R where
  left := Finset.univ.filter fun u => .left u ∉ S ∨ ∃ v : R, G (u, v) = true ∧ .right v ∉ S
  right := Finset.univ.filter fun v => .right v ∈ S

theorem isVertexCover_cutToVertexCover [DecidableEq L] [DecidableEq R]
    (G : L × R → Bool) (S : Finset (BipartiteVertex L R)) :
    IsVertexCover G (cutToVertexCover G S) := by
  intro u v hG
  by_cases hv : BipartiteVertex.right v ∈ S
  · exact .inr (by simp [cutToVertexCover, hv])
  · left
    simp only [cutToVertexCover, Finset.mem_filter, Finset.mem_univ, true_and]
    exact .inr ⟨v, hG, hv⟩

theorem size_cutToVertexCover_le [DecidableEq L] [DecidableEq R]
    {S : Finset (BipartiteVertex L R)} (hS : (bipartiteNetwork G).IsCut S) :
    (cutToVertexCover G S).size ≤ (bipartiteNetwork G).cutCapacity S := by
  rw [bipartiteNetwork_cutCapacity_eq hS]
  unfold VertexCover.size cutToVertexCover
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have hle_left :
      (∑ u : L, if .left u ∉ S ∨ ∃ v : R, G (u, v) = true ∧ .right v ∉ S then 1 else 0) ≤
        ∑ u : L,
          ((if .left u ∉ S then 1 else 0) +
            ∑ v : R, if .left u ∈ S ∧ .right v ∉ S ∧ G (u, v) = true then 1 else 0) := by
    refine Finset.sum_le_sum fun u _ => ?_
    by_cases hu : BipartiteVertex.left u ∉ S
    · simp [hu]
    · have hu_in : BipartiteVertex.left u ∈ S := Classical.not_not.mp hu
      by_cases hex : ∃ v : R, G (u, v) = true ∧ BipartiteVertex.right v ∉ S
      · simp only [hu, false_or, hex, ↓reduceIte, zero_add]
        obtain ⟨v₀, hG₀, hv₀⟩ := hex
        let term : R → ℕ := fun v =>
          if BipartiteVertex.left u ∈ S ∧ BipartiteVertex.right v ∉ S ∧ G (u, v) = true then 1
          else 0
        have hterm₀ : term v₀ = 1 := by simp [term, hu_in, hv₀, hG₀]
        have hsingle : term v₀ ≤ ∑ v : R, term v :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v₀)
        simpa [term, hterm₀] using hsingle
      · simp [hu, hex]
  omega

end Koenig

section KoenigFinite

variable [Finite L] [Finite R] {G : L × R → Bool}

/-- **Weak duality for bipartite matchings and vertex covers:** every matching `M` in `G` has
cardinality at most the size of every vertex cover `C` of `G`. -/
theorem card_le_size_of_matching_vertexCover {M : Finset (L × R)} (hM : IsMatching G M)
    {C : VertexCover L R} (hC : IsVertexCover G C) :
    M.card ≤ C.size := by
  classical
  cases nonempty_fintype L
  cases nonempty_fintype R
  have hflow := (matchingToFlow hM).value_le_cutCapacity (isCut_vertexCoverToCut (G := G) C)
  rw [value_matchingToFlow hM, cutCapacity_vertexCoverToCut hC] at hflow
  omega

end KoenigFinite

/-- Any maximum flow `f` and minimum cut `S` of equal value on `bipartiteNetwork G` yield a
maximum matching `flowToMatching f` and minimum König vertex cover `cutToVertexCover G S` of
equal size. -/
theorem bipartiteMatching_of_maxFlow_minCut [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R] {G : L × R → Bool}
    {f : (bipartiteNetwork G).Flow} {S : Finset (BipartiteVertex L R)}
    (hS : (bipartiteNetwork G).IsCut S)
    (hval : f.value = ((bipartiteNetwork G).cutCapacity S : ℤ)) :
    IsMaxMatching G (flowToMatching f) ∧
      IsMinVertexCover G (cutToVertexCover G S) ∧
      (flowToMatching f).card = (cutToVertexCover G S).size := by
  have hM := isMatching_flowToMatching f
  have hC := isVertexCover_cutToVertexCover G S
  have hcoe := card_flowToMatching_coe f
  have hC_le := size_cutToVertexCover_le hS
  have hM_le := card_le_size_of_matching_vertexCover hM hC
  refine ⟨⟨hM, fun M' hM' => ?_⟩, ⟨hC, fun C' hC' => ?_⟩, by omega⟩
  · exact (card_le_size_of_matching_vertexCover hM' hC).trans (by omega)
  · exact le_trans (by omega) (card_le_size_of_matching_vertexCover hM hC')

/-- **König's Theorem** ([Koenig1931], pp. 116–119; [FordFulkerson1962], Chapter II, Section 4,
Theorem 4.1): every finite bipartite graph `G : L × R → Bool` admits a maximum matching `M` and a
minimum vertex cover `C` of equal size (`M.card = C.size`). -/
theorem exists_maxMatching_eq_minVertexCover [Finite L] [Finite R] (G : L × R → Bool) :
    ∃ (M : Finset (L × R)) (C : VertexCover L R),
      IsMaxMatching G M ∧ IsMinVertexCover G C ∧ M.card = C.size := by
  classical
  cases nonempty_fintype L
  cases nonempty_fintype R
  obtain ⟨f, S, _, hS_min, hval⟩ :=
    (bipartiteNetwork G).exists_maxFlow_eq_minCut (bipartiteNetwork_s_ne_t G)
  exact ⟨_, _, bipartiteMatching_of_maxFlow_minCut hS_min.1 hval⟩

end FlowReduction

/-! ### Bridge to `Cslib.Circuits.BipartiteMatching.HasPerfectMatching` -/

section PerfectMatchingBridge

variable {V : Type*} [Fintype V]

/-- `HasPerfectMatching G` holds if and only if `G` admits a matching of cardinality
`Fintype.card V`. -/
theorem hasPerfectMatching_iff_exists_matching_card (G : V × V → Bool) :
    Cslib.Circuits.BipartiteMatching.HasPerfectMatching G ↔
      ∃ M : Finset (V × V), IsMatching G M ∧ M.card = Fintype.card V := by
  classical
  constructor
  · rintro ⟨σ, hσ⟩
    have hmem : ∀ {u v}, (u, v) ∈ Finset.univ.image (fun u => (u, σ u)) ↔ σ u = v := by simp
    refine ⟨Finset.univ.image fun u => (u, σ u), ⟨fun e he => ?_,
      fun u v₁ v₂ h₁ h₂ => (hmem.mp h₁).symm.trans (hmem.mp h₂),
      fun u₁ u₂ v h₁ h₂ => σ.injective ((hmem.mp h₁).trans (hmem.mp h₂).symm)⟩, ?_⟩
    · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
      exact hσ u
    · rw [Finset.card_image_of_injective _ fun a b h => (Prod.mk.inj h).1, Finset.card_univ]
  · rintro ⟨M, ⟨hM_edge, hM_left, hM_right⟩, hcard⟩
    have hinj_fst : Set.InjOn Prod.fst (M : Set (V × V)) := by
      intro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ (hu : u₁ = u₂)
      subst hu
      exact Prod.ext rfl (hM_left u₁ v₁ v₂ h₁ h₂)
    have himg_univ : M.image Prod.fst = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        (by simp [Finset.card_image_of_injOn hinj_fst, hcard])
    have hex : ∀ u : V, ∃ v : V, (u, v) ∈ M := fun u => by
      obtain ⟨⟨_, v⟩, hmem, rfl⟩ :=
        Finset.mem_image.mp (by rw [himg_univ]; exact Finset.mem_univ u : u ∈ M.image Prod.fst)
      exact ⟨v, hmem⟩
    choose g hg_mem using hex
    exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp fun u₁ u₂ heq =>
      hM_right u₁ u₂ (g u₁) (hg_mem u₁) (heq ▸ hg_mem u₂)), fun u => hM_edge (u, g u) (hg_mem u)⟩

/-- Flow characterization of `HasPerfectMatching G`: `G : V × V → Bool` has a perfect matching if
and only if `bipartiteNetwork G` admits an integral flow of value `Fintype.card V`. -/
theorem hasPerfectMatching_iff_exists_flow_value_card (G : V × V → Bool) :
    Cslib.Circuits.BipartiteMatching.HasPerfectMatching G ↔
      ∃ f : (bipartiteNetwork G).Flow, f.value = (Fintype.card V : ℤ) := by
  classical
  rw [hasPerfectMatching_iff_exists_matching_card]
  constructor
  · rintro ⟨M, hM, hcard⟩
    exact ⟨matchingToFlow hM, by rw [value_matchingToFlow hM, hcard]⟩
  · rintro ⟨f, hval⟩
    refine ⟨flowToMatching f, isMatching_flowToMatching f, ?_⟩
    have hcoe := card_flowToMatching_coe f
    omega

end PerfectMatchingBridge

/-! ### Pure executable bipartite matching and König cover solver -/

section ExecutableBipartite

/-- Equivalence between `Bool` and `Fin 2` (`false ↦ 0`, `true ↦ 1`). -/
@[expose] def boolEquivFin2 : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := i.val == 1
  left_inv b := by cases b <;> rfl
  right_inv i := by rcases i with ⟨_ | _ | _, hi⟩ <;> [rfl; rfl; omega]

/-- Computable vertex equivalence `BipartiteVertex (Fin m) (Fin r) ≃ Fin (2 + (m + r))`. -/
@[expose] def bipartiteFinEquiv (m r : ℕ) :
    BipartiteVertex (Fin m) (Fin r) ≃ Fin (2 + (m + r)) :=
  (bipartiteVertexEquiv (Fin m) (Fin r)).trans
    ((Equiv.sumCongr boolEquivFin2 finSumFinEquiv).trans finSumFinEquiv)

/-- Reindexed `Fin (2 + (m + r))` flow network for `G : Fin m × Fin r → Bool`. -/
@[expose] def bipartiteFinNetwork {m r : ℕ}
    (G : Fin m × Fin r → Bool) : Network (Fin (2 + (m + r))) :=
  (bipartiteNetwork G).reindex (bipartiteFinEquiv m r)

/-- Output of `bipartiteMatching` on `G : Fin m × Fin r → Bool`. -/
structure BipartiteOutput (m r : ℕ) where
  /-- Maximum-cardinality matching in `G`. -/
  matching : Finset (Fin m × Fin r)
  /-- Minimum-cardinality König vertex cover of `G`. -/
  cover : VertexCover (Fin m) (Fin r)
  /-- Number of shortest-path augmentations performed by Edmonds–Karp. -/
  augmentations : ℕ


/-- Compute a maximum bipartite matching and minimum König vertex cover of
`G : Fin m × Fin r → Bool` via `edmondsKarpDense`. -/
@[expose] def bipartiteMatching {m r : ℕ}
    (G : Fin m × Fin r → Bool) : BipartiteOutput m r :=
  let out := edmondsKarpDense (bipartiteFinNetwork G)
  let f := out.flow.ofReindex (bipartiteFinEquiv m r)
  let S := Network.cutOfReindex (bipartiteFinEquiv m r) out.cut
  { matching := flowToMatching f
    cover := cutToVertexCover G S
    augmentations := out.augmentations }

/-- **Correctness of `bipartiteMatching`:** returns a maximum matching `res.matching` and minimum
vertex cover `res.cover` satisfying König strong duality `res.matching.card = res.cover.size`. -/
theorem bipartiteMatching_correct {m r : ℕ} (G : Fin m × Fin r → Bool) :
    let res := bipartiteMatching G
    IsMaxMatching G res.matching ∧
      IsMinVertexCover G res.cover ∧
      res.matching.card = res.cover.size := by
  have hst : (bipartiteFinNetwork G).s ≠ (bipartiteFinNetwork G).t := fun h =>
    bipartiteNetwork_s_ne_t G ((bipartiteFinEquiv m r).injective h)
  obtain ⟨_, hmin_cut, hval, _, _, _⟩ := edmondsKarpDense_correct (N := bipartiteFinNetwork G) hst
  exact bipartiteMatching_of_maxFlow_minCut (Network.isCut_cutOfReindex _ hmin_cut.1)
    ((Network.Flow.value_ofReindex _ _).trans
      (hval.trans (congrArg _ (Network.cutCapacity_cutOfReindex _ _ _).symm)))

/-- Decide whether `G : Fin n × Fin n → Bool` has a perfect matching via `bipartiteMatching`. -/
@[expose] def decidePerfectMatching {n : ℕ} (G : Fin n × Fin n → Bool) : Bool :=
  decide ((bipartiteMatching G).matching.card = n)

/-- `decidePerfectMatching G` returns `true` if and only if
`Cslib.Circuits.BipartiteMatching.HasPerfectMatching G` holds. -/
theorem decidePerfectMatching_eq_true_iff {n : ℕ} (G : Fin n × Fin n → Bool) :
    decidePerfectMatching G = true ↔
      Cslib.Circuits.BipartiteMatching.HasPerfectMatching G := by
  simp only [decidePerfectMatching, decide_eq_true_iff]
  rw [hasPerfectMatching_iff_exists_matching_card, Fintype.card_fin]
  obtain ⟨hM_max, _, _⟩ := bipartiteMatching_correct G
  refine ⟨fun hcard => ⟨_, hM_max.1, hcard⟩, fun ⟨M, hM, hcard⟩ => ?_⟩
  refine le_antisymm ?_ (hcard.symm.le.trans (hM_max.2 M hM))
  simpa [VertexCover.size] using card_le_size_of_matching_vertexCover hM_max.1
    (C := ⟨Finset.univ, ∅⟩) fun u _ _ => .inl (Finset.mem_univ u)

end ExecutableBipartite

end Cslib.Algorithms.Lean.MaxFlow
