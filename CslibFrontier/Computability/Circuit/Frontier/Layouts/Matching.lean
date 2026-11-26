/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Median
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ordering a cubic multigraph by matched-edge pair insertion

In `CslibFrontier.Computability.Circuit.Frontier.Layouts.Median`, every vertex of a loopless
cubic multigraph is placed at the median of the three scores of its incident edges, yielding a cut
bound of `#(vertices straddling t)` at each threshold `t`.

Keeping a matching `M : Set E` (a set of pairwise vertex-disjoint edges) *unsubdivided* yields a
threshold cost bound `Multigraph.matchingCost` that is pointwise at most the naive straddling count
(`Multigraph.matchingCost_le_edgeStraddles`). Equality holds for the empty matching
(`Multigraph.matchingCost_empty`), while concrete examples exhibit strict savings (e.g.,
`exists_twoVertexCost_lt_starCost_add` and the `K₄` test comparing the two threshold cost bounds
rather than full layout widths). Each unpaired vertex `v` keeps its `median3` key, while each
matched edge `e ∈ M` with endpoints `u = G.src e` and `v = G.tgt e` and outer incident pairs
`G.incidenceSet u \ {e} = {a, b}` and `G.incidenceSet v \ {e} = {c, d}` places `u` and `v` at the
single pair keys `pairKey (score a) (score b) (score c) (score d)` and
`pairKey (score c) (score d) (score a) (score b)`, where
`pairKey a b c d := min (max a b) (max (min a b) (min c d))`.

This single pair of real keys *simultaneously attains the optimal two-vertex cut energy at every
threshold `t`* (`twoVertexEnergy_pairKey`):

* cost `0` when all four outer edge scores lie on the same side of `t` (`(0, 0)` or `(2, 2)`);
* cost `1` when the four outer edge scores straddle `t` and at least one outer pair `{a, b}` or
  `{c, d}` does not straddle `t` (covering the `(1, 0)`, `(0, 1)`, `(2, 1)`, `(1, 2)`, `(2, 0)`,
  and `(0, 2)` splits);
* cost `2` only when both outer pairs straddle `t` (`(1, 1)`).

Decomposing `twoVertexCost` into the two binary events `Multigraph.PairStraddlesAny` (the four outer
edges straddle `t`) and `Multigraph.PairStraddlesBoth` (both outer pairs straddle `t`) avoids any
ordering choice on incident edges, handles parallel edges without requiring a simple graph, and
lets every cut of a threshold layout be bounded pointwise by `Multigraph.matchingCost`. This weak
pointwise bound is always at most the naive straddling count
(`Multigraph.matchingCost_le_edgeStraddles`), with equality possible (e.g., `M = ∅`,
`Multigraph.matchingCost_empty`) and strict improvement in concrete examples where a matched pair
has a `(1, 0)` outer split whose shared edge lands on the minority side
(`exists_twoVertexCost_lt_starCost_add`).

This adapts the deterministic pair-insertion key (`pairKey` / `pairColor`) from the Apache 2.0
companion repository `SamuelSchlesinger/the-frontier-method` (modules `Frontier.Layouts.Pair` and
`Frontier.Layouts.MatchingLayout`) to the loopless cubic `Multigraph` setting used in this library
(allowing parallel edges). It is also the combinatorial layout mechanism underlying the `4.6155n`
matched-edge branch-and-bound bound (`rrwilliams0/circuit-lb-4.6155n`).

## Main definitions

* `Cslib.Circuits.Frontier.pairKey`, `Cslib.Circuits.Frontier.pairColor`: canonical threshold keys
  and optimal Boolean color for a matched edge pair.
* `Cslib.Circuits.Frontier.starEnergy`, `Cslib.Circuits.Frontier.starCost`: single-vertex cubic star
  disagreement energy and optimal cost.
* `Cslib.Circuits.Frontier.twoVertexEnergy`, `Cslib.Circuits.Frontier.twoVertexCost`: two-vertex
  matched-edge energy and optimal cost.
* `Cslib.Circuits.Frontier.Multigraph.IsMatching`: pairwise vertex-disjoint edge set.
* `Cslib.Circuits.Frontier.Multigraph.matchedVertices`: vertices incident to a matching edge.
* `Cslib.Circuits.Frontier.Multigraph.PairStraddlesAny`,
  `Cslib.Circuits.Frontier.Multigraph.PairStraddlesBoth`: binary events whose sum is
  `twoVertexCost` at a matched edge.
* `Cslib.Circuits.Frontier.Multigraph.matchingCost`: exact threshold cost of a matching.
* `Cslib.Circuits.Frontier.Multigraph.matchingKey`: vertex keys combining `median3` and `pairKey`.

## Main results

* `Cslib.Circuits.Frontier.twoVertexEnergy_pairKey`: one pair of keys achieves the optimal
  two-vertex cost simultaneously at every threshold `t`.
* `Cslib.Circuits.Frontier.twoVertexCost_le_starCost_add`,
  `Cslib.Circuits.Frontier.exists_twoVertexCost_lt_starCost_add`: weak pointwise bound showing pair
  cost is at most the sum of the two star costs, with a strict concrete `(1, 0)` example (`1 < 2`).
* `Cslib.Circuits.Frontier.Multigraph.matchingCost_le_edgeStraddles`: weak pointwise bound showing
  matching cost is at most the naive straddling count from `Median` (with equality for `M = ∅`).
* `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_threshold_add_slack_le_matchingCost`,
  `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_threshold_le_matchingCost`: exact cut and
  unmatched-edge slack bounds at every threshold `t`.
* `Cslib.Circuits.Frontier.Multigraph.exists_width_le_of_matching_edgeScore`: deterministic layout
  width bound over any grid of edge-score windows.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

/-! ### Boolean energy and canonical pair keys -/

/-- Boolean disagreement indicator: `1` if `x ≠ y`, `0` otherwise. -/
private def boolDiff (x y : Bool) : ℕ := if x = y then 0 else 1

private theorem boolDiff_slack (x y m : Bool) :
    boolDiff x y + 2 * (if x = true ∧ y = true ∧ m = false then 1 else 0) ≤
      boolDiff x m + boolDiff y m := by
  cases x <;> cases y <;> cases m <;> decide

/-- Optimal Boolean color for the first endpoint of a matched pair with outer colors `(a, b)` at
the first endpoint and `(c, d)` at the second. Swap `(a, b)` and `(c, d)` for the other
endpoint. -/
def pairColor (a b c d : Bool) : Bool :=
  (a && b) || ((a || b) && (c || d))

/-- Canonical real threshold key for the first endpoint of a matched pair with outer edge scores
`a, b` at that endpoint and `c, d` at its mate. Swapping `a ↔ b` or `c ↔ d` leaves it unchanged. -/
def pairKey {α : Type*} [LinearOrder α] (a b c d : α) : α :=
  min (max a b) (max (min a b) (min c d))

theorem pairKey_comm_left {α : Type*} [LinearOrder α] (a b c d : α) :
    pairKey a b c d = pairKey b a c d := by
  simp only [pairKey, max_comm a b, min_comm a b]

theorem pairKey_comm_right {α : Type*} [LinearOrder α] (a b c d : α) :
    pairKey a b c d = pairKey a b d c := by
  simp only [pairKey, min_comm c d]

/-- A pair key is always equal to one of the four outer edge scores. -/
theorem pairKey_mem {α : Type*} [LinearOrder α] (a b c d : α) :
    pairKey a b c d = a ∨ pairKey a b c d = b ∨
      pairKey a b c d = c ∨ pairKey a b c d = d := by
  unfold pairKey
  rcases min_choice (max a b) (max (min a b) (min c d)) with h | h
  · exact h.symm ▸ (max_choice a b).imp id Or.inl
  · rcases max_choice (min a b) (min c d) with h' | h'
    · exact (h.trans h').symm ▸ (min_choice a b).imp id Or.inl
    · exact Or.inr (Or.inr ((h.trans h').symm ▸ min_choice c d))

/-- Disagreement count at a single cubic vertex with three incident edge colors `a, b, c` and
vertex color `x`. -/
def starEnergy (a b c x : Bool) : ℕ :=
  (if x = a then 0 else 1) + (if x = b then 0 else 1) + (if x = c then 0 else 1)

/-- Minimum cut cost of a single cubic vertex: `0` when all three incident edges share a color,
`1` when they straddle. -/
def starCost (a b c : Bool) : ℕ :=
  if a = b ∧ b = c then 0 else 1

/-- Total disagreement count of a matched edge `{u, v}` with outer edge colors `a, b` at `u` and
`c, d` at `v`, when `u` receives color `x` and `v` receives color `y`. -/
def twoVertexEnergy (a b c d x y : Bool) : ℕ :=
  (if x = a then 0 else 1) + (if x = b then 0 else 1) +
    (if x = y then 0 else 1) +
    (if y = c then 0 else 1) + (if y = d then 0 else 1)

/-- Minimum disagreement cost of a matched edge pair over all choices of `(x, y : Bool)`:
`0` when all four outer colors match, `2` when both pairs disagree (`a ≠ b` and `c ≠ d`), and `1`
when the four outer colors are not all equal but at least one pair matches (`a = b` or `c = d`). -/
def twoVertexCost (a b c d : Bool) : ℕ :=
  (if a = b ∧ b = c ∧ c = d then 0 else 1) +
    (if a ≠ b ∧ c ≠ d then 1 else 0)

/-- `median3` thresholds to majority vote at every threshold `t`. -/
theorem decide_median3_lt {α : Type*} [LinearOrder α] (a b c t : α) :
    decide (median3 a b c < t) =
      ((decide (a < t) && decide (b < t)) ||
        (decide (a < t) && decide (c < t)) ||
        (decide (b < t) && decide (c < t))) := by
  by_cases ha : a < t <;> by_cases hb : b < t <;> by_cases hc : c < t <;>
    simp [median3, ha, hb, hc, max_lt_iff, min_lt_iff]

/-- The median of three incident edge scores attains `starCost` at every threshold `t`. -/
theorem starEnergy_median3 {α : Type*} [LinearOrder α] (a b c t : α) :
    starEnergy (decide (a < t)) (decide (b < t)) (decide (c < t))
      (decide (median3 a b c < t)) =
      starCost (decide (a < t)) (decide (b < t)) (decide (c < t)) := by
  rw [decide_median3_lt]
  cases decide (a < t) <;> cases decide (b < t) <;> cases decide (c < t) <;> decide

/-- Thresholding `pairKey` yields `pairColor` simultaneously at every threshold `t`. -/
theorem decide_pairKey_lt {α : Type*} [LinearOrder α] (a b c d t : α) :
    decide (pairKey a b c d < t) =
      pairColor (decide (a < t)) (decide (b < t)) (decide (c < t)) (decide (d < t)) := by
  by_cases ha : a < t <;> by_cases hb : b < t <;>
    by_cases hc : c < t <;> by_cases hd : d < t <;>
    simp [pairKey, pairColor, min_lt_iff, max_lt_iff, ha, hb, hc, hd]

/-- The pair coloring attains `twoVertexCost` and is minimal over all `(x, y : Bool)`. -/
theorem twoVertexEnergy_pairColor (a b c d : Bool) :
    twoVertexEnergy a b c d (pairColor a b c d) (pairColor c d a b) =
      twoVertexCost a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- `twoVertexCost` is the minimum of `twoVertexEnergy` over all vertex colorings `(x, y)`. -/
theorem twoVertexCost_le_twoVertexEnergy (a b c d x y : Bool) :
    twoVertexCost a b c d ≤ twoVertexEnergy a b c d x y := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases x <;> cases y <;> decide

/-- **Simultaneous optimality.** One pair of real keys attains the optimal two-vertex cut cost at
every threshold `t` at once. -/
theorem twoVertexEnergy_pairKey {α : Type*} [LinearOrder α] (a b c d t : α) :
    twoVertexEnergy (decide (a < t)) (decide (b < t)) (decide (c < t)) (decide (d < t))
      (decide (pairKey a b c d < t)) (decide (pairKey c d a b < t)) =
      twoVertexCost (decide (a < t)) (decide (b < t)) (decide (c < t)) (decide (d < t)) := by
  simp only [decide_pairKey_lt, twoVertexEnergy_pairColor]

/-- For every choice of shared-edge color `m`, the pair cost is at most the sum of the two
endpoint star costs. -/
theorem twoVertexCost_le_starCost_add (a b c d m : Bool) :
    twoVertexCost a b c d ≤ starCost a b m + starCost c d m := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases m <;> decide

/-- On a `(1, 0)` outer split whose shared edge receives the minority color (`m = true`), keeping
the matched edge unsubdivided strictly saves `1` over naive median-of-3 edge scores (`1 < 2`). -/
theorem exists_twoVertexCost_lt_starCost_add :
    twoVertexCost true false false false <
      starCost true false true + starCost false false true := by
  decide

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E)

/-! ### Matchings in a multigraph -/

/-- A set of edges `M` is a *matching* when its edges are pairwise vertex-disjoint: no vertex is
incident to two distinct edges in `M`. -/
def IsMatching (M : Set E) : Prop :=
  M.Pairwise fun e f => Disjoint ({G.src e, G.tgt e} : Set V) {G.src f, G.tgt f}

/-- The set of vertices incident to some edge in `M`. -/
def matchedVertices (M : Set E) : Set V :=
  {v | ∃ e ∈ M, e ∈ G.incidenceSet v}

/-- `PairStraddlesAny` holds at a matched edge `e` when the four outer edges at `G.src e` and
`G.tgt e` (excluding `e`) straddle `t`: one scores below `t` and one at least `t`. -/
def PairStraddlesAny {α : Type*} [LinearOrder α] (score : E → α) (t : α) (e : E) : Prop :=
  StraddlesOn score t ((G.incidenceSet (G.src e) \ {e}) ∪ (G.incidenceSet (G.tgt e) \ {e}))

/-- `PairStraddlesBoth` holds at a matched edge `e` when *both* outer pairs
`G.incidenceSet (G.src e) \ {e}` and `G.incidenceSet (G.tgt e) \ {e}` straddle `t`. -/
def PairStraddlesBoth {α : Type*} [LinearOrder α] (score : E → α) (t : α) (e : E) : Prop :=
  StraddlesOn score t (G.incidenceSet (G.src e) \ {e}) ∧
    StraddlesOn score t (G.incidenceSet (G.tgt e) \ {e})

/-- The threshold cost of a matching `M` at threshold `t`: each unpaired straddling vertex pays
`1`, each matched edge whose outer edges straddle `t` pays `1`, and each matched edge whose two
outer pairs *both* straddle `t` pays an additional `1` (matching `twoVertexCost`). -/
noncomputable def matchingCost {α : Type*} [LinearOrder α] (M : Set E) (score : E → α)
    (t : α) : ℕ :=
  {v | v ∉ G.matchedVertices M ∧ G.EdgeStraddles score t v}.ncard +
    {e | e ∈ M ∧ G.PairStraddlesAny score t e}.ncard +
    {e | e ∈ M ∧ G.PairStraddlesBoth score t e}.ncard

theorem isMatching_empty : G.IsMatching (∅ : Set E) := Set.pairwise_empty _

theorem matchedVertices_empty : G.matchedVertices (∅ : Set E) = ∅ := by
  ext v; simp [matchedVertices]

theorem matchingCost_empty {α : Type*} [LinearOrder α] (score : E → α) (t : α) :
    G.matchingCost ∅ score t = {v | G.EdgeStraddles score t v}.ncard := by
  simp [matchingCost, matchedVertices_empty]

theorem pairStraddlesAny_congr {α : Type*} [LinearOrder α] {score score' : E → α} {t : α}
    {e : E} (h : ∀ f ∈ (G.incidenceSet (G.src e) \ {e}) ∪ (G.incidenceSet (G.tgt e) \ {e}),
      score f = score' f) :
    G.PairStraddlesAny score t e ↔ G.PairStraddlesAny score' t e :=
  straddlesOn_congr h

theorem pairStraddlesBoth_congr {α : Type*} [LinearOrder α] {score score' : E → α} {t : α}
    {e : E} (h : ∀ f ∈ (G.incidenceSet (G.src e) \ {e}) ∪ (G.incidenceSet (G.tgt e) \ {e}),
      score f = score' f) :
    G.PairStraddlesBoth score t e ↔ G.PairStraddlesBoth score' t e :=
  and_congr (straddlesOn_congr fun f hf => h f (Or.inl hf))
    (straddlesOn_congr fun f hf => h f (Or.inr hf))

variable {G}

private theorem eq_of_mem_isMatching {M : Set E} (hM : G.IsMatching M) {e f : E}
    (he : e ∈ M) (hf : f ∈ M) {v : V} (hev : e ∈ G.incidenceSet v) (hfv : f ∈ G.incidenceSet v) :
    e = f := by
  by_contra hne
  exact disjoint_left.mp (hM he hf hne)
    (by rcases hev with h | h <;> simp [h] : v ∈ _)
    (by rcases hfv with h | h <;> simp [h])

/-- Mate of a vertex `v` under matching `M` (returning `v` when `v` is unmatched). -/
noncomputable def mate (G : Multigraph V E) (M : Set E) (v : V) : V :=
  letI := Classical.dec
  if h : ∃ e ∈ M, e ∈ G.incidenceSet v then
    if G.src h.choose = v then G.tgt h.choose else G.src h.choose
  else v

private theorem mate_src {M : Set E} (hM : G.IsMatching M)
    {e : E} (he : e ∈ M) : G.mate M (G.src e) = G.tgt e := by
  have hex : ∃ f ∈ M, f ∈ G.incidenceSet (G.src e) := ⟨e, he, Or.inl rfl⟩
  have huniq : hex.choose = e :=
    eq_of_mem_isMatching hM hex.choose_spec.1 he hex.choose_spec.2 (Or.inl rfl)
  simp only [mate, hex, ↓reduceDIte, huniq, ↓reduceIte]

private theorem mate_tgt {M : Set E} (hM : G.IsMatching M) (hloop : G.Loopless)
    {e : E} (he : e ∈ M) : G.mate M (G.tgt e) = G.src e := by
  have hex : ∃ f ∈ M, f ∈ G.incidenceSet (G.tgt e) := ⟨e, he, Or.inr rfl⟩
  have huniq : hex.choose = e :=
    eq_of_mem_isMatching hM hex.choose_spec.1 he hex.choose_spec.2 (Or.inr rfl)
  simp only [mate, hex, ↓reduceDIte, huniq, hloop e, ↓reduceIte]

/-- Canonical threshold key for a vertex of a cubic multigraph under edge scores `score` and
matching `M`: unpaired vertices use `median3` of their three incident edge scores; endpoints of
`e ∈ M` use `pairKey` of their outer pair and their mate's outer pair. -/
noncomputable def matchingKey {α : Type*} [LinearOrder α] [Inhabited α]
    (G : Multigraph V E) (M : Set E) (score : E → α) (v : V) : α :=
  letI := Classical.dec
  if h : ∃ e ∈ M, e ∈ G.incidenceSet v then
    let e := h.choose
    let u := if G.src e = v then G.tgt e else G.src e
    if hs : (G.incidenceSet v \ {e}).ncard = 2 ∧ (G.incidenceSet u \ {e}).ncard = 2 then
      let p₁ := (ncard_eq_two.mp hs.1).choose
      let q₁ := (ncard_eq_two.mp hs.1).choose_spec.choose
      let p₂ := (ncard_eq_two.mp hs.2).choose
      let q₂ := (ncard_eq_two.mp hs.2).choose_spec.choose
      pairKey (score p₁) (score q₁) (score p₂) (score q₂)
    else default
  else if h3 : (G.incidenceSet v).ncard = 3 then
    let e₀ := (ncard_eq_three.mp h3).choose
    let e₁ := (ncard_eq_three.mp h3).choose_spec.choose
    let e₂ := (ncard_eq_three.mp h3).choose_spec.choose_spec.choose
    median3 (score e₀) (score e₁) (score e₂)
  else default

private theorem ncard_sdiff_singleton_eq_two [Finite E] {v : V} {e : E}
    (h3 : (G.incidenceSet v).ncard = 3) (he : e ∈ G.incidenceSet v) :
    (G.incidenceSet v \ {e}).ncard = 2 := by
  have := ncard_sdiff_singleton_add_one he (s := G.incidenceSet v)
  omega

private theorem pairKey_eq_of_eq_pair {α : Type*} [LinearOrder α] (score : E → α)
    {S₁ S₂ : Set E} {a b a' b' c d c' d' : E}
    (h1 : S₁ = {a, b}) (h1' : S₁ = {a', b'}) (hab' : a' ≠ b')
    (h2 : S₂ = {c, d}) (h2' : S₂ = {c', d'}) (hcd' : c' ≠ d') :
    pairKey (score a) (score b) (score c) (score d) =
      pairKey (score a') (score b') (score c') (score d') := by
  have hmem1 {x} (hx : x ∈ ({a', b'} : Set E)) : x = a ∨ x = b := by
    simpa [← h1', h1] using hx
  have hmem2 {x} (hx : x ∈ ({c', d'} : Set E)) : x = c ∨ x = d := by
    simpa [← h2', h2] using hx
  have hcd_case {x y} (hx : x = c ∨ x = d) (hy : y = c ∨ y = d) (hxy : x ≠ y) (u v : α) :
      pairKey u v (score c) (score d) = pairKey u v (score x) (score y) := by
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    exacts [(hxy rfl).elim, rfl, pairKey_comm_right u v (score y) (score x), (hxy rfl).elim]
  rcases hmem1 (Or.inl rfl) with rfl | rfl <;> rcases hmem1 (Or.inr rfl) with rfl | rfl
  · exact (hab' rfl).elim
  · exact hcd_case (hmem2 (Or.inl rfl)) (hmem2 (Or.inr rfl)) hcd' (score a') (score b')
  · rw [pairKey_comm_left (score b') (score a')]
    exact hcd_case (hmem2 (Or.inl rfl)) (hmem2 (Or.inr rfl)) hcd' (score a') (score b')
  · exact (hab' rfl).elim

private theorem matchingKey_endpoint [Finite E] {α : Type*} [LinearOrder α] [Inhabited α]
    {M : Set E} (hM : G.IsMatching M)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (score : E → α)
    {e : E} (he : e ∈ M) {v u : V} (hev : e ∈ G.incidenceSet v) (heu : e ∈ G.incidenceSet u)
    (hopp : (G.src e = v ∧ u = G.tgt e) ∨ (G.src e ≠ v ∧ u = G.src e))
    {a b c d : E}
    (hv : G.incidenceSet v \ {e} = {a, b})
    (hu : G.incidenceSet u \ {e} = {c, d}) :
    G.matchingKey M score v = pairKey (score a) (score b) (score c) (score d) := by
  have hex : ∃ f ∈ M, f ∈ G.incidenceSet v := ⟨e, he, hev⟩
  have huniq : hex.choose = e :=
    eq_of_mem_isMatching hM hex.choose_spec.1 he hex.choose_spec.2 hev
  have hnv := ncard_sdiff_singleton_eq_two (h3 v) hev
  have hnu := ncard_sdiff_singleton_eq_two (h3 u) heu
  classical
  have hmate : (if G.src e = v then G.tgt e else G.src e) = u := by
    rcases hopp with ⟨hs, rfl⟩ | ⟨hs, rfl⟩ <;> simp [hs]
  simp only [matchingKey, hex, ↓reduceDIte, huniq, hmate, hnv, hnu, and_self]
  have hp := (ncard_eq_two.mp hnv).choose_spec.choose_spec
  have hq := (ncard_eq_two.mp hnu).choose_spec.choose_spec
  exact (pairKey_eq_of_eq_pair score hv hp.2 hp.1 hu hq.2 hq.1).symm

/-- At any matched edge `e ∈ M` with outer incident edge pairs `{a, b}` at `G.src e` and `{c, d}`
at `G.tgt e`, `matchingKey` evaluates to `pairKey` of the four outer edge scores. -/
theorem matchingKey_matched [Finite E] {α : Type*} [LinearOrder α] [Inhabited α]
    {M : Set E} (hM : G.IsMatching M) (hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (score : E → α)
    {e a b c d : E} (he : e ∈ M)
    (hsrc : G.incidenceSet (G.src e) \ {e} = {a, b})
    (htgt : G.incidenceSet (G.tgt e) \ {e} = {c, d}) :
    G.matchingKey M score (G.src e) = pairKey (score a) (score b) (score c) (score d) ∧
      G.matchingKey M score (G.tgt e) = pairKey (score c) (score d) (score a) (score b) :=
  ⟨matchingKey_endpoint hM h3 score he (Or.inl rfl) (Or.inr rfl) (Or.inl ⟨rfl, rfl⟩) hsrc htgt,
    matchingKey_endpoint hM h3 score he (Or.inr rfl) (Or.inl rfl)
      (Or.inr ⟨hloop e, rfl⟩) htgt hsrc⟩

private theorem matchingKey_unmatched {α : Type*} [LinearOrder α] [Inhabited α]
    {M : Set E} (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (score : E → α)
    {v : V} (hv : v ∉ G.matchedVertices M) :
    ∃ e₀ e₁ e₂ : E, e₀ ≠ e₁ ∧ e₀ ≠ e₂ ∧ e₁ ≠ e₂ ∧
      G.incidenceSet v = {e₀, e₁, e₂} ∧
      G.matchingKey M score v = median3 (score e₀) (score e₁) (score e₂) := by
  have hnot : ¬∃ e ∈ M, e ∈ G.incidenceSet v := hv
  have hnc := h3 v
  have hspec := (ncard_eq_three.mp hnc).choose_spec.choose_spec.choose_spec
  refine ⟨_, _, _, hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2, ?_⟩
  simp only [matchingKey, hnot, ↓reduceDIte, hnc]

/-- Helper connecting `starCost` to `EdgeStraddles`. -/
private theorem starCost_eq_ite_edgeStraddles {α : Type*} [LinearOrder α]
    (score : E → α) (t : α) {v : V} {e₀ e₁ e₂ : E}
    (hs : G.incidenceSet v = {e₀, e₁, e₂}) :
    starCost (decide (score e₀ < t)) (decide (score e₁ < t)) (decide (score e₂ < t)) =
      letI := Classical.propDecidable
      if G.EdgeStraddles score t v then 1 else 0 := by
  simp only [starCost, EdgeStraddles, StraddlesOn, hs, mem_insert_iff, mem_singleton_iff,
    or_and_right, exists_or, exists_eq_left]
  by_cases h0 : score e₀ < t <;> by_cases h1 : score e₁ < t <;> by_cases h2 : score e₂ < t <;>
    simp [h0, h1, h2, not_lt.mp, not_le.mpr]

/-- Helper expressing `twoVertexCost` in terms of `PairStraddlesAny` and `PairStraddlesBoth`. -/
private theorem twoVertexCost_eq_pairStraddles {α : Type*} [LinearOrder α]
    (score : E → α) (t : α) {e a b c d : E}
    (hsrc : G.incidenceSet (G.src e) \ {e} = {a, b})
    (htgt : G.incidenceSet (G.tgt e) \ {e} = {c, d}) :
    twoVertexCost (decide (score a < t)) (decide (score b < t))
        (decide (score c < t)) (decide (score d < t)) =
      letI := Classical.propDecidable
      (if G.PairStraddlesAny score t e then 1 else 0) +
        (if G.PairStraddlesBoth score t e then 1 else 0) := by
  simp only [twoVertexCost, PairStraddlesAny, PairStraddlesBoth, hsrc, htgt, StraddlesOn,
    mem_union, mem_insert_iff, mem_singleton_iff, or_and_right, exists_or, exists_eq_left]
  by_cases ha : score a < t <;> by_cases hb : score b < t <;>
    by_cases hc : score c < t <;> by_cases hd : score d < t <;>
    simp [ha, hb, hc, hd, not_lt.mp, not_le.mpr]

/-- Extract the two outer incident edges at each endpoint of `e` in a cubic multigraph. -/
private theorem exists_outer_edges [Finite E] (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    (e : E) :
    ∃ a b c d : E, a ≠ b ∧ c ≠ d ∧
      G.incidenceSet (G.src e) \ {e} = {a, b} ∧
      G.incidenceSet (G.tgt e) \ {e} = {c, d} := by
  obtain ⟨a, b, hab, hsrc⟩ :=
    ncard_eq_two.mp (ncard_sdiff_singleton_eq_two (h3 (G.src e)) (Or.inl rfl))
  obtain ⟨c, d, hcd, htgt⟩ :=
    ncard_eq_two.mp (ncard_sdiff_singleton_eq_two (h3 (G.tgt e)) (Or.inr rfl))
  exact ⟨a, b, c, d, hab, hcd, hsrc, htgt⟩

private theorem incidenceSet_eq_triple_of_sdiff {v : V} {e a b : E}
    (he : e ∈ G.incidenceSet v) (hdiff : G.incidenceSet v \ {e} = {a, b}) :
    G.incidenceSet v = {a, b, e} := by
  ext f
  rcases eq_or_ne f e with rfl | hfe
  · simp [he]
  · simpa [hfe] using Set.ext_iff.mp hdiff f

private theorem filter_notMem_incidenceSet_eq_pair [Fintype E] [DecidableEq E] {M : Set E}
    {v : V} [DecidablePred (fun f : E => f ∉ M ∧ f ∈ G.incidenceSet v)] {e a b : E}
    (hM : G.IsMatching M) (heM : e ∈ M) (hev : e ∈ G.incidenceSet v)
    (hdiff : G.incidenceSet v \ {e} = {a, b}) :
    Finset.univ.filter (fun f => f ∉ M ∧ f ∈ G.incidenceSet v) = {a, b} := by
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  have hd : f ∈ G.incidenceSet v \ {e} ↔ f = a ∨ f = b := by simp [hdiff]
  rw [← hd]
  exact ⟨fun ⟨hfM, hfi⟩ => ⟨hfi, fun hfe => hfM (hfe ▸ heM)⟩,
    fun ⟨hfi, hfe⟩ => ⟨fun hfM => hfe (eq_of_mem_isMatching hM hfM heM hfi hev), hfi⟩⟩

private theorem ncard_and_eq_sum_filter {ι : Type*} [Fintype ι] (S P : ι → Prop)
    [DecidablePred S] [DecidablePred P] :
    {x | S x ∧ P x}.ncard = ∑ x ∈ Finset.univ.filter S, if P x then 1 else 0 := by
  have hset : {x | S x ∧ P x} =
      ((Finset.univ.filter fun x => S x ∧ P x) : Set ι) := by
    ext x; simp
  rw [hset, ncard_coe_finset, Finset.card_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : S x <;> by_cases hp : P x <;> simp [hx, hp]

/-- Decompose a sum over all vertices into the unmatched vertices and pairs of matched edge
endpoints. -/
private theorem sum_vertices_eq_unmatched_add_matching [Fintype V] [Fintype E]
    {M : Set E} [DecidablePred (· ∈ M)] [DecidablePred (· ∈ G.matchedVertices M)]
    (hloop : G.Loopless) (hM : G.IsMatching M) (w : V → ℕ) :
    ∑ v : V, w v =
      (∑ v ∈ Finset.univ.filter (· ∉ G.matchedVertices M), w v) +
      ∑ e ∈ Finset.univ.filter (· ∈ M), (w (G.src e) + w (G.tgt e)) := by
  have := Classical.decEq V
  let Mfin : Finset E := Finset.univ.filter (· ∈ M)
  have hbi : Finset.univ.filter (· ∈ G.matchedVertices M) =
      Mfin.biUnion fun e => ({G.src e, G.tgt e} : Finset V) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, matchedVertices, mem_ofPred_eq,
      Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, mem_incidenceSet, Mfin, eq_comm]
  have hdisj : (Mfin : Set E).PairwiseDisjoint
      (fun e => ({G.src e, G.tgt e} : Finset V)) := by
    intro e he f hf hne
    exact Finset.disjoint_left.mpr fun u hu hv => by
      have heM : e ∈ M := by simpa [Mfin] using he
      have hfM : f ∈ M := by simpa [Mfin] using hf
      exact disjoint_left.mp (hM heM hfM hne) (by simpa using hu) (by simpa using hv)
  have hcompl := (Finset.sum_add_sum_compl (Finset.univ.filter (· ∈ G.matchedVertices M))
    w).symm
  have hcf : (Finset.univ.filter (· ∈ G.matchedVertices M))ᶜ =
      Finset.univ.filter (· ∉ G.matchedVertices M) := by ext v; simp
  rw [hcompl, hcf, add_comm, hbi, Finset.sum_biUnion hdisj]
  congr 1
  exact Finset.sum_congr rfl fun e _ => Finset.sum_pair (hloop e)

/-- **Comparison with median edge scores.** For every matching `M` in a loopless cubic multigraph,
`matchingCost M score t` is at most the total number of vertices straddling `t`. Equality holds for
`M = ∅` (`matchingCost_empty`). -/
theorem matchingCost_le_edgeStraddles [Finite V] [Finite E] {α : Type*} [LinearOrder α]
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M : Set E} (hM : G.IsMatching M) (score : E → α) (t : α) :
    G.matchingCost M score t ≤ {v | G.EdgeStraddles score t v}.ncard := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  have htot : {v | G.EdgeStraddles score t v}.ncard =
      ∑ v : V, if G.EdgeStraddles score t v then 1 else 0 := by
    simpa using ncard_and_eq_sum_filter (fun _ : V => True) (G.EdgeStraddles score t)
  rw [matchingCost,
    ncard_and_eq_sum_filter (· ∉ G.matchedVertices M) (G.EdgeStraddles score t),
    ncard_and_eq_sum_filter (· ∈ M) (G.PairStraddlesAny score t),
    ncard_and_eq_sum_filter (· ∈ M) (G.PairStraddlesBoth score t),
    htot, sum_vertices_eq_unmatched_add_matching hloop hM
      (fun v => if G.EdgeStraddles score t v then 1 else 0),
    add_assoc, ← Finset.sum_add_distrib]
  refine Nat.add_le_add_left (Finset.sum_le_sum fun e _ => ?_) _
  obtain ⟨a, b, c, d, _, _, hsrc, htgt⟩ := exists_outer_edges h3 e
  have hinc_s : G.incidenceSet (G.src e) = {a, b, e} :=
    incidenceSet_eq_triple_of_sdiff (Or.inl rfl) hsrc
  have hinc_t : G.incidenceSet (G.tgt e) = {c, d, e} :=
    incidenceSet_eq_triple_of_sdiff (Or.inr rfl) htgt
  rw [← twoVertexCost_eq_pairStraddles score t hsrc htgt,
    ← starCost_eq_ite_edgeStraddles score t hinc_s,
    ← starCost_eq_ite_edgeStraddles score t hinc_t]
  exact twoVertexCost_le_starCost_add _ _ _ _ _

/-- **Refined threshold cut bound.** For every threshold `t`, the cut of
`P₀ = {v | matchingKey G M score v < t}` in a loopless cubic multigraph plus twice the number of
unmatched edges inside `P₀` with `t ≤ score f` is at most `G.matchingCost M score t`. -/
theorem ncard_edgeCut_threshold_add_slack_le_matchingCost [Finite V] [Finite E]
    {α : Type*} [LinearOrder α] [Inhabited α]
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M : Set E} (hM : G.IsMatching M) (score : E → α) (t : α) :
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
  let slack (e : E) : ℕ :=
    if col (G.src e) = true ∧ col (G.tgt e) = true ∧ ecol e = false then 1 else 0
  let Mfin : Finset E := Finset.univ.filter (· ∈ M)
  have hcut : (G.edgeCut P₀).ncard = ∑ e : E, boolDiff (col (G.src e)) (col (G.tgt e)) := by
    have hset : G.edgeCut P₀ = ((Finset.univ.filter (· ∈ G.edgeCut P₀)) : Set E) := by
      ext e; simp
    rw [hset, ncard_coe_finset, Finset.card_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [P₀, col, boolDiff, mem_edgeCut, mem_ofPred_eq]
    by_cases hs : G.matchingKey M score (G.src e) < t <;>
      by_cases ht : G.matchingKey M score (G.tgt e) < t <;>
      simp [hs, ht]
  have hslack : {f | f ∉ M ∧ G.src f ∈ P₀ ∧ G.tgt f ∈ P₀ ∧ t ≤ score f}.ncard =
      ∑ e ∈ Mfinᶜ, slack e := by
    have hset : {f | f ∉ M ∧ G.src f ∈ P₀ ∧ G.tgt f ∈ P₀ ∧ t ≤ score f} =
        ((Mfinᶜ.filter fun e => slack e = 1) : Set E) := by
      ext e
      simp only [mem_ofPred_eq, Finset.coe_filter, Finset.mem_compl, Mfin, Finset.mem_filter,
        Finset.mem_univ, true_and, slack, col, ecol, P₀, decide_eq_true_eq,
        decide_eq_false_iff_not, not_lt]
      split_ifs with h <;> simp [h]
    rw [hset, ncard_coe_finset, Finset.card_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    dsimp only [slack]
    split_ifs <;> omega
  -- Split edges into matched edges `M` (kept directly) and unmatched edges (split across their
  -- endpoint incidences with the slack term).
  have hstep1 : (∑ e : E, boolDiff (col (G.src e)) (col (G.tgt e))) + 2 * ∑ e ∈ Mfinᶜ, slack e ≤
      (∑ e ∈ Mfin, boolDiff (col (G.src e)) (col (G.tgt e))) +
      ∑ e ∈ Mfinᶜ, (boolDiff (col (G.src e)) (ecol e) + boolDiff (col (G.tgt e)) (ecol e)) := by
    rw [← (Finset.sum_add_sum_compl Mfin (fun e => boolDiff (col (G.src e)) (col (G.tgt e)))),
      add_assoc, two_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Nat.add_le_add_left (Finset.sum_le_sum fun e _ => ?_) _
    rw [← two_mul]
    exact boolDiff_slack _ _ (ecol e)
  -- Group the endpoint incidences of unmatched edges by vertex.
  have hgroup :
      ∑ e ∈ Mfinᶜ, (boolDiff (col (G.src e)) (ecol e) + boolDiff (col (G.tgt e)) (ecol e)) =
      ∑ v : V, ∑ e ∈ Finset.univ.filter (fun e => e ∉ M ∧ e ∈ G.incidenceSet v),
        boolDiff (col v) (ecol e) := by
    rw [Finset.sum_comm' (t' := Mfinᶜ) (s' := fun e => {G.src e, G.tgt e}) fun v e => by
      simp [Mfin, mem_incidenceSet, eq_comm]; tauto]
    exact Finset.sum_congr rfl fun e _ =>
      (Finset.sum_pair (f := fun v => boolDiff (col v) (ecol e)) (hloop e)).symm
  -- Split vertex sum into unmatched vertices and matched pairs.
  let vsum (v : V) : ℕ :=
    ∑ e ∈ Finset.univ.filter (fun e => e ∉ M ∧ e ∈ G.incidenceSet v), boolDiff (col v) (ecol e)
  have hvsplit : ∑ v : V, vsum v =
      (∑ v ∈ Finset.univ.filter (· ∉ G.matchedVertices M), vsum v) +
      ∑ e ∈ Mfin, (vsum (G.src e) + vsum (G.tgt e)) :=
    sum_vertices_eq_unmatched_add_matching hloop hM vsum
  -- Evaluate `vsum` at every unpaired vertex (`starCost`).
  have hsingle : ∑ v ∈ Finset.univ.filter (· ∉ G.matchedVertices M), vsum v =
      {v | v ∉ G.matchedVertices M ∧ G.EdgeStraddles score t v}.ncard := by
    rw [ncard_and_eq_sum_filter (· ∉ G.matchedVertices M) (G.EdgeStraddles score t)]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hv' : v ∉ G.matchedVertices M := (Finset.mem_filter.mp hv).2
    obtain ⟨e₀, e₁, e₂, h01, h02, h12, hinc, hkey⟩ := matchingKey_unmatched h3 score hv'
    have hfilt : Finset.univ.filter (fun e => e ∉ M ∧ e ∈ G.incidenceSet v) = {e₀, e₁, e₂} := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hinc, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      exact and_iff_right_of_imp fun h heM => hv' ⟨e, heM, by simp [hinc, h]⟩
    dsimp [vsum]
    rw [hfilt, Finset.sum_insert (by simp [h01, h02]), Finset.sum_insert (by simp [h12]),
      Finset.sum_singleton, ← starCost_eq_ite_edgeStraddles score t hinc, ← starEnergy_median3]
    simp only [starEnergy, boolDiff, ecol, col, hkey, add_assoc]
  -- Evaluate each matched edge pair (`twoVertexCost`).
  have hpair : ∑ e ∈ Mfin, (boolDiff (col (G.src e)) (col (G.tgt e)) +
        (vsum (G.src e) + vsum (G.tgt e))) =
      {e | e ∈ M ∧ G.PairStraddlesAny score t e}.ncard +
        {e | e ∈ M ∧ G.PairStraddlesBoth score t e}.ncard := by
    rw [ncard_and_eq_sum_filter (· ∈ M) (G.PairStraddlesAny score t),
      ncard_and_eq_sum_filter (· ∈ M) (G.PairStraddlesBoth score t),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e he => ?_
    have heM : e ∈ M := (Finset.mem_filter.mp he).2
    obtain ⟨a, b, c, d, hab, hcd, hsrc, htgt⟩ := exists_outer_edges h3 e
    have hfil_s := filter_notMem_incidenceSet_eq_pair hM heM (Or.inl rfl) hsrc
    have hfil_t := filter_notMem_incidenceSet_eq_pair hM heM (Or.inr rfl) htgt
    obtain ⟨hks, hkt⟩ := matchingKey_matched hM hloop h3 score heM hsrc htgt
    dsimp only [vsum]
    rw [hfil_s, Finset.sum_pair hab, hfil_t, Finset.sum_pair hcd,
      ← twoVertexCost_eq_pairStraddles score t hsrc htgt,
      ← twoVertexEnergy_pairKey (score a) (score b) (score c) (score d) t]
    simp only [twoVertexEnergy, col, ecol, boolDiff, hks, hkt]
    omega
  rw [hcut, hslack]
  calc (∑ e : E, boolDiff (col (G.src e)) (col (G.tgt e))) + 2 * ∑ e ∈ Mfinᶜ, slack e
      ≤ (∑ e ∈ Mfin, boolDiff (col (G.src e)) (col (G.tgt e))) +
          ∑ e ∈ Mfinᶜ, (boolDiff (col (G.src e)) (ecol e) + boolDiff (col (G.tgt e)) (ecol e)) :=
        hstep1
    _ = (∑ v ∈ Finset.univ.filter (· ∉ G.matchedVertices M), vsum v) +
          ∑ e ∈ Mfin, (boolDiff (col (G.src e)) (col (G.tgt e)) +
            (vsum (G.src e) + vsum (G.tgt e))) := by
        rw [hgroup]
        change (∑ e ∈ Mfin, boolDiff (col (G.src e)) (col (G.tgt e))) + ∑ v : V, vsum v = _
        rw [hvsplit, Finset.sum_add_distrib, add_left_comm]
        simp only [Finset.sum_add_distrib]
    _ = G.matchingCost M score t := by
        rw [hsingle, hpair, matchingCost, add_assoc]

/-- **Threshold cut bound.** For every threshold `t`, the cut of `{v | matchingKey G M score v < t}`
in a loopless cubic multigraph (parallel edges allowed) is at most `G.matchingCost M score t`. -/
theorem ncard_edgeCut_threshold_le_matchingCost [Finite V] [Finite E]
    {α : Type*} [LinearOrder α] [Inhabited α]
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M : Set E} (hM : G.IsMatching M) (score : E → α) (t : α) :
    (G.edgeCut {v | G.matchingKey M score v < t}).ncard ≤ G.matchingCost M score t :=
  (Nat.le_add_right _ _).trans
    (ncard_edgeCut_threshold_add_slack_le_matchingCost hloop h3 hM score t)

/-! ### Prefix cuts and grid layout bound -/

/-- Every vertex whose `matchingKey` lies in a predicate `p` is either an endpoint or the `M`-mate
of an endpoint of some edge whose score satisfies `p`. Thus each such edge produces at most `4`
vertices. -/
theorem ncard_matchingKey_pred_le [Finite V] [Finite E]
    {α : Type*} [LinearOrder α] [Inhabited α]
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M : Set E} (hM : G.IsMatching M) (score : E → α) (p : α → Prop) :
    {v | p (G.matchingKey M score v)}.ncard ≤ 4 * {e | p (score e)}.ncard := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  let Efin : Finset E := Finset.univ.filter fun e => p (score e)
  let hit (e : E) : Finset V :=
    {G.src e, G.tgt e, G.mate M (G.src e), G.mate M (G.tgt e)}
  have hsub : (Finset.univ.filter fun v => p (G.matchingKey M score v)) ⊆ Efin.biUnion hit := by
    intro v hv
    have hpv : p (G.matchingKey M score v) := (Finset.mem_filter.mp hv).2
    have hmem {u : V} (f : E) (hpf : p (score f)) (hf : u ∈ hit f) : u ∈ Efin.biUnion hit :=
      Finset.mem_biUnion.mpr ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpf⟩, hf⟩
    have hhit {w : V} {f : E} (hf : f ∈ G.incidenceSet w) : w ∈ hit f ∧ G.mate M w ∈ hit f := by
      rcases hf with rfl | rfl <;> simp [hit]
    by_cases hmat : v ∈ G.matchedVertices M
    · obtain ⟨e, heM, hev⟩ := hmat
      obtain ⟨a, b, c, d, _, _, hsrc, htgt⟩ := exists_outer_edges h3 e
      obtain ⟨hks, hkt⟩ := matchingKey_matched hM hloop h3 score heM hsrc htgt
      have hpair {u w : V} {x₁ x₂ y₁ y₂ : E}
          (hu : G.incidenceSet u \ {e} = {x₁, x₂}) (hw : G.incidenceSet w \ {e} = {y₁, y₂})
          (hmate : G.mate M w = u)
          (hp : p (pairKey (score x₁) (score x₂) (score y₁) (score y₂))) :
          u ∈ Efin.biUnion hit := by
        rcases pairKey_mem (score x₁) (score x₂) (score y₁) (score y₂) with h | h | h | h
        · exact hmem x₁ (h ▸ hp) (hhit (hu.symm.subset (mem_insert x₁ _)).1).1
        · exact hmem x₂ (h ▸ hp) (hhit (hu.symm.subset (mem_insert_of_mem _ rfl)).1).1
        · exact hmem y₁ (h ▸ hp) (hmate ▸ (hhit (hw.symm.subset (mem_insert y₁ _)).1).2)
        · exact hmem y₂ (h ▸ hp) (hmate ▸ (hhit (hw.symm.subset (mem_insert_of_mem _ rfl)).1).2)
      rcases hev with rfl | rfl
      · exact hpair hsrc htgt (mate_tgt hM hloop heM) (hks ▸ hpv)
      · exact hpair htgt hsrc (mate_src hM heM) (hkt ▸ hpv)
    · obtain ⟨e₀, e₁, e₂, _, _, _, hinc, hkey⟩ := matchingKey_unmatched h3 score hmat
      rw [hkey] at hpv
      have hmed : median3 (score e₀) (score e₁) (score e₂) = score e₀ ∨
          median3 (score e₀) (score e₁) (score e₂) = score e₁ ∨
          median3 (score e₀) (score e₁) (score e₂) = score e₂ := by
        unfold median3
        rcases max_choice (min (score e₀) (score e₁)) (min (max (score e₀) (score e₁)) (score e₂))
          with h | h
        · rw [h]
          exact (min_choice (score e₀) (score e₁)).imp id Or.inl
        · rw [h]
          rcases min_choice (max (score e₀) (score e₁)) (score e₂) with h' | h'
          · exact h'.symm ▸ (max_choice (score e₀) (score e₁)).imp id Or.inl
          · exact Or.inr (Or.inr h')
      rcases hmed with h | h | h
      · exact hmem e₀ (h ▸ hpv) (hhit (hinc.symm.subset (mem_insert e₀ _))).1
      · exact hmem e₁ (h ▸ hpv) (hhit (hinc.symm.subset (mem_insert_of_mem _ (mem_insert e₁ _)))).1
      · exact hmem e₂ (h ▸ hpv)
          (hhit (hinc.symm.subset (mem_insert_of_mem _ (mem_insert_of_mem _ rfl)))).1
  have h1 : {v | p (G.matchingKey M score v)} =
      ((Finset.univ.filter fun v => p (G.matchingKey M score v)) : Set V) := by ext v; simp
  have h2 : {e | p (score e)} = (Efin : Set E) := by ext e; simp [Efin]
  rw [h1, h2, ncard_coe_finset, ncard_coe_finset]
  calc (Finset.univ.filter fun v => p (G.matchingKey M score v)).card
      ≤ (Efin.biUnion hit).card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ Efin, (hit e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ Efin, 4 := Finset.sum_le_sum fun _ _ => Finset.card_le_four
    _ = 4 * Efin.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- Adding vertices `P \ P₀` to a vertex set `P₀ ⊆ P` increases the edge cut by at most
`3 * (P \ P₀).ncard`. -/
private theorem ncard_edgeCut_le_of_subset [Finite V] [Finite E]
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) {P₀ P : Set V} (hsub : P₀ ⊆ P) :
    (G.edgeCut P).ncard ≤ (G.edgeCut P₀).ncard + 3 * (P \ P₀).ncard := by
  have he : G.edgeCut P ⊆ G.edgeCut P₀ ∪ G.touching (P \ P₀) := by
    intro e heP
    by_cases ht : e ∈ G.touching (P \ P₀)
    · exact Or.inr ht
    · left
      rw [mem_touching, not_or] at ht
      have hsrc : G.src e ∈ P ↔ G.src e ∈ P₀ :=
        ⟨fun h => by_contra fun hn => ht.1 ⟨h, hn⟩, fun h => hsub h⟩
      have htgt : G.tgt e ∈ P ↔ G.tgt e ∈ P₀ :=
        ⟨fun h => by_contra fun hn => ht.2 ⟨h, hn⟩, fun h => hsub h⟩
      simpa [mem_edgeCut, hsrc, htgt] using heP
  exact (ncard_le_ncard he).trans ((ncard_union_le _ _).trans
    (Nat.add_le_add_left (G.ncard_touching_le (fun v => (h3 v).le) _) _))

/-- **Threshold-grid reduction for `matchingKey`-separated sets.** Given any quantity `f : ℝ`
bounded by `((G.edgeCut P).ncard : ℝ)` for a set `P` separated by `m` under `matchingKey`, `f ≤ B`
whenever the lower tail, upper tail, and grid windows are bounded by `B`. -/
theorem le_of_matchingKey_separated_grid [Finite V] [Finite E]
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M : Set E} (hM : G.IsMatching M) (score : E → ℝ)
    {P : Set V} {m : ℝ}
    (hP : ∀ v ∈ P, G.matchingKey M score v ≤ m)
    (hPc : ∀ v ∉ P, m ≤ G.matchingKey M score v)
    {f : ℝ} (hf_cut : f ≤ (G.edgeCut P).ncard)
    {a δ : ℝ} (hδ : 0 < δ) {K : ℕ} {B : ℝ} (cost : ℝ → ℝ)
    (hf_step : ∀ t : ℝ, {v | G.matchingKey M score v < t} ⊆ P →
      f ≤ cost t + 3 * ((P \ {v | G.matchingKey M score v < t}).ncard : ℝ))
    (low : 12 * ({e | score e < a}.ncard : ℝ) ≤ B)
    (high : 12 * ({e | a + K * δ ≤ score e}.ncard : ℝ) ≤ B)
    (mid : ∀ i < K, cost (a + i * δ) +
      12 * ({e | a + i * δ ≤ score e ∧ score e < a + (i + 1) * δ}.ncard : ℝ) ≤ B) :
    f ≤ B := by
  rcases lt_or_ge m a with hlow | hge
  · have hsub : P ⊆ {v | G.matchingKey M score v < a} := fun v hv => (hP v hv).trans_lt hlow
    have hcut : (G.edgeCut P).ncard ≤ 12 * {e | score e < a}.ncard := by
      calc (G.edgeCut P).ncard
          ≤ (G.touching P).ncard := ncard_le_ncard (G.edgeCut_subset_touching P)
        _ ≤ 3 * P.ncard := G.ncard_touching_le (fun v => (h3 v).le) P
        _ ≤ 3 * {v | G.matchingKey M score v < a}.ncard :=
            Nat.mul_le_mul_left 3 (ncard_le_ncard hsub)
        _ ≤ 3 * (4 * {e | score e < a}.ncard) :=
            Nat.mul_le_mul_left 3 (ncard_matchingKey_pred_le hloop h3 hM score (· < a))
        _ = 12 * {e | score e < a}.ncard := by ring
    exact hf_cut.trans ((Nat.cast_le.mpr hcut).trans (by push_cast; exact low))
  set top := a + K * δ
  rcases le_or_gt top m with htop | hlt
  · have hsub : Pᶜ ⊆ {v | top ≤ G.matchingKey M score v} := fun v hv => htop.trans (hPc v hv)
    have hcompl : G.edgeCut P = G.edgeCut Pᶜ := by
      ext e; simp [mem_edgeCut, not_iff_not]
    have hcut : (G.edgeCut P).ncard ≤ 12 * {e | top ≤ score e}.ncard := by
      rw [hcompl]
      calc (G.edgeCut Pᶜ).ncard
          ≤ (G.touching Pᶜ).ncard := ncard_le_ncard (G.edgeCut_subset_touching Pᶜ)
        _ ≤ 3 * Pᶜ.ncard := G.ncard_touching_le (fun v => (h3 v).le) Pᶜ
        _ ≤ 3 * {v | top ≤ G.matchingKey M score v}.ncard :=
            Nat.mul_le_mul_left 3 (ncard_le_ncard hsub)
        _ ≤ 3 * (4 * {e | top ≤ score e}.ncard) :=
            Nat.mul_le_mul_left 3 (ncard_matchingKey_pred_le hloop h3 hM score (top ≤ ·))
        _ = 12 * {e | top ≤ score e}.ncard := by ring
    exact hf_cut.trans ((Nat.cast_le.mpr hcut).trans (by push_cast; exact high))
  obtain ⟨i, hiK, ht, ht'⟩ := exists_grid_index hδ hge hlt
  set t := a + i * δ
  set t' := a + (i + 1) * δ
  set P₀ : Set V := {v | G.matchingKey M score v < t}
  have hP₀ : P₀ ⊆ P := fun v hv =>
    by_contra fun hvn => not_lt.mpr (ht.trans (hPc v hvn)) hv
  have hdiff : P \ P₀ ⊆ {v | t ≤ G.matchingKey M score v ∧ G.matchingKey M score v < t'} :=
    fun v ⟨hv, hvn⟩ => ⟨not_lt.mp hvn, (hP v hv).trans_lt ht'⟩
  have hwin : 3 * (P \ P₀).ncard ≤ 12 * {e | t ≤ score e ∧ score e < t'}.ncard := by
    calc 3 * (P \ P₀).ncard
        ≤ 3 * {v | t ≤ G.matchingKey M score v ∧ G.matchingKey M score v < t'}.ncard :=
          Nat.mul_le_mul_left 3 (ncard_le_ncard hdiff)
      _ ≤ 3 * (4 * {e | t ≤ score e ∧ score e < t'}.ncard) :=
          Nat.mul_le_mul_left 3
            (ncard_matchingKey_pred_le hloop h3 hM score fun x => t ≤ x ∧ x < t')
      _ = 12 * {e | t ≤ score e ∧ score e < t'}.ncard := by ring
  have hwinR : 3 * ((P \ P₀).ncard : ℝ) ≤ 12 * ({e | t ≤ score e ∧ score e < t'}.ncard : ℝ) := by
    exact_mod_cast hwin
  linarith [hf_step t hP₀, mid i hiK]

/-- **Cut bound for a threshold prefix.** For any set `P` separated by a threshold `m` of
`matchingKey`, its cut size is bounded by a lower tail, upper tail, or the matching cost at the
grid threshold below `m` plus `12` times the window edge count. -/
theorem ncard_edgeCut_le_matchingCost_add [Finite V] [Finite E]
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M : Set E} (hM : G.IsMatching M) (score : E → ℝ)
    {P : Set V} {m : ℝ}
    (hP : ∀ v ∈ P, G.matchingKey M score v ≤ m)
    (hPc : ∀ v ∉ P, m ≤ G.matchingKey M score v)
    {a δ : ℝ} (hδ : 0 < δ) {K : ℕ} {B : ℝ}
    (low : 12 * ({e | score e < a}.ncard : ℝ) ≤ B)
    (high : 12 * ({e | a + K * δ ≤ score e}.ncard : ℝ) ≤ B)
    (mid : ∀ i < K, (G.matchingCost M score (a + i * δ) : ℝ) +
      12 * ({e | a + i * δ ≤ score e ∧ score e < a + (i + 1) * δ}.ncard : ℝ) ≤ B) :
    ((G.edgeCut P).ncard : ℝ) ≤ B :=
  le_of_matchingKey_separated_grid hloop h3 hM score hP hPc le_rfl hδ
    (fun t => (G.matchingCost M score t : ℝ))
    (fun t hP₀ => by
      have h1 := (ncard_edgeCut_le_of_subset h3 hP₀).trans
        (Nat.add_le_add_right (ncard_edgeCut_threshold_le_matchingCost hloop h3 hM score t) _)
      exact_mod_cast h1)
    low high mid

/-- **The matched-edge pair-insertion layout.** Given a loopless cubic multigraph (parallel edges
allowed), any matching `M`, any edge scores `score : E → ℝ`, and a grid `a, a + δ, ..., a + K δ`,
sorting vertices by `matchingKey` gives a layout whose width is bounded by the worst tail bound
`12 * tail` and window bound `matchingCost + 12 * window`. -/
theorem exists_width_le_of_matching_edgeScore [Finite V] [Finite E]
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M : Set E} (hM : G.IsMatching M) (score : E → ℝ) {a δ : ℝ} (hδ : 0 < δ) (K : ℕ) {B : ℝ}
    (low : 12 * ({e | score e < a}.ncard : ℝ) ≤ B)
    (high : 12 * ({e | a + K * δ ≤ score e}.ncard : ℝ) ≤ B)
    (mid : ∀ i < K, (G.matchingCost M score (a + i * δ) : ℝ) +
      12 * ({e | a + i * δ ≤ score e ∧ score e < a + (i + 1) * δ}.ncard : ℝ) ≤ B) :
    ∃ π : Layout V, (G.width π : ℝ) ≤ B := by
  obtain ⟨π, hπ⟩ := Layout.exists_threshold (G.matchingKey M score)
  refine ⟨π, G.width_le_of_ncard_frontier_le π (le_trans (by positivity) low) fun t ht => ?_⟩
  obtain ⟨m, hP, hPc⟩ := hπ t ht
  exact ncard_edgeCut_le_matchingCost_add hloop h3 hM score hP hPc hδ low high mid

end Multigraph

end Cslib.Circuits.Frontier
