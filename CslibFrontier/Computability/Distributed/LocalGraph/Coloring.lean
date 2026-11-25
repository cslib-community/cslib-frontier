/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.LocalGraph.Basic
public import CslibFrontier.Computability.Distributed.OrientedCycle.ColeVishkin
public import Mathlib.Data.List.Range
public import Mathlib.Data.Multiset.Sort

/-!
# Deterministic `(Δ + 1)`-Coloring on Bounded-Degree Graphs in the `LOCAL` Model

Deterministic synchronous `LOCAL` vertex-coloring protocols on finite simple graphs
`G : SimpleGraph V` of maximum degree `G.maxDegree ≤ Δ` (steps towards `#7505`, after
[Cole and Vishkin][ColeVishkin1986], [Goldberg, Plotkin and Shannon][GoldbergPlotkinShannon1988],
[Kuhn and Wattenhofer][KuhnWattenhofer2006], [Wattenhofer][Wattenhofer2016] Chapter 1, and
[Hirvonen and Suomela][HirvonenSuomela2020] Chapter 4).

Three reusable building blocks are provided on `BroadcastProtocol` (and hence also on
`PortProtocol` via `BroadcastProtocol.toPortProtocol`):

1. **One-round greedy local-maximum color reduction (`greedyColorReduction Δ`):** following
   [Hirvonen and Suomela][HirvonenSuomela2020], §4.5, Lemma 4.1, p. 69, every node whose current
   color strictly exceeds all neighbor colors recolors itself to the smallest color in
   `{0, …, Δ}` absent from its neighborhood. Each round preserves properness and reduces a palette
   of size `q` to `max (q - 1) (Δ + 1)`, reaching `Δ + 1` colors within `q - (Δ + 1)` rounds from
   any initial proper `q`-coloring (`greedyColorReduction_run`).
2. **Kuhn–Wattenhofer one-round disjoint-block palette compression (`kwCompressProtocol Δ m`):**
   following [Kuhn and Wattenhofer][KuhnWattenhofer2006], §5, Theorem 5.1, p. 12, one broadcast
   round compresses any proper `m`-coloring on a graph of maximum degree `≤ Δ` into
   `kwBound Δ m = ⌈m (Δ + 1) / (Δ + 2)⌉` colors (`kwCompressProtocol_run`), strictly shrinking
   every palette with `Δ + 2 ≤ m` (`kwBound_lt`).
3. **Orientation-decomposed Cole–Vishkin `(Δ + 1)`-coloring (`deltaPlusOneColoring Δ C`):**
   from injective node identifiers below `C`, Round `0` collects and sorts each node's `≤ Δ`
   neighbor identifiers to decompose incident constraints into `Δ` functional out-edge slots;
   the next `Nat.logStar C` rounds run `Cslib.Distributed.OrientedCycle.cvColor` in parallel across
   all `Δ` slots to obtain `Δ` proper `6`-colorings; and `Δ` merging phases of `5 (Δ + 1)` greedy
   reduction rounds fold the slot colorings into a single proper `Fin (Δ + 1)`-coloring within
   `deltaPlusOneRounds Δ C = 1 + Nat.logStar C + 5 * Δ * (Δ + 1)` rounds (`O(log* C + Δ²)`, hence
   `O(Δ log* C + Δ²)`), stabilizing for all later rounds (`deltaPlusOneColoring_isProperColoring`).
   Polynomial cover-free set-system reduction (`O(log* C + Δ log Δ)`) and linear-in-`Δ` coloring
   remain open under `#7505`.

## Main definitions

* `Cslib.Distributed.LocalGraph.firstFreeColor`, `greedyStep`, `greedyColorReduction`: smallest
  available color in `{0, …, Δ}` and one-round greedy local-maximum color reduction.
* `Cslib.Distributed.LocalGraph.kwBound`, `kwCompress`, `kwCompressProtocol`: Kuhn–Wattenhofer
  palette bound `⌈m (Δ + 1) / (Δ + 2)⌉` and one-round disjoint-block compression protocol.
* `Cslib.Distributed.LocalGraph.ColoringState`, `deltaPlusOneRounds`, `deltaPlusOneColoring`:
  local state, round bound `1 + log* C + 5 Δ (Δ + 1)`, and deterministic `(Δ + 1)`-coloring
  `BroadcastProtocol`.

## Main results

* `Cslib.Distributed.LocalGraph.greedyStep_ne_of_adj`, `greedyStep_lt`,
  `greedyColorReduction_run`: properness and `q - r` palette bound of `greedyColorReduction`.
* `Cslib.Distributed.LocalGraph.kwBound_lt`, `kwCompressProtocol_run`: Kuhn–Wattenhofer one-round
  proper compression step from `m` to `kwBound Δ m` colors (after `[KuhnWattenhofer2006]`,
  Theorem 5.1).
* `Cslib.Distributed.LocalGraph.deltaPlusOneRounds_le`,
  `deltaPlusOneColoring_isProperColoring`,
  `deltaPlusOneGraphColoring`: explicit `O(log* C + Δ²)` / `O(Δ log* C + Δ²)` round bound,
  proper `Fin (Δ + 1)`-coloring correctness, and bundled `G.Coloring (Fin (Δ + 1))` constructor
  for `deltaPlusOneColoring Δ C` from unique identifiers below `C`.

## References

* [R. Cole and U. Vishkin, *Deterministic coin tossing with applications to optimal parallel list
  ranking*][ColeVishkin1986]
* [A. V. Goldberg, S. A. Plotkin and G. E. Shannon, *Parallel symmetry-breaking in sparse
  graphs*][GoldbergPlotkinShannon1988]
* [F. Kuhn and R. Wattenhofer, *On the complexity of distributed graph
  coloring*][KuhnWattenhofer2006], §5, Theorem 5.1
* [R. Wattenhofer, *Principles of Distributed Computing*][Wattenhofer2016], Chapter 1
* [J. Hirvonen and J. Suomela, *Distributed Algorithms 2020*][HirvonenSuomela2020], §4.5, Lemma 4.1
-/

public section

namespace Cslib.Distributed.LocalGraph

open Cslib.Distributed.OrientedCycle

/-! ### Smallest unused color and one-round greedy local-maximum reduction -/

/-- The smallest natural number in `{0, …, Δ}` not belonging to `used` (defaulting to `0` when all
`Δ + 1` values lie in `used`, which never occurs when `used.card ≤ Δ`). -/
@[expose] def firstFreeColor (Δ : ℕ) (used : Finset ℕ) : ℕ :=
  ((List.range (Δ + 1)).find? fun c => decide (c ∉ used)).getD 0

/-- `firstFreeColor Δ used` always lies in `{0, …, Δ}`. -/
theorem firstFreeColor_lt (Δ : ℕ) (used : Finset ℕ) : firstFreeColor Δ used < Δ + 1 := by
  unfold firstFreeColor
  cases h : (List.range (Δ + 1)).find? (fun c => decide (c ∉ used)) with
  | none => exact Nat.succ_pos Δ
  | some c => exact List.mem_range.1 (List.mem_of_find?_eq_some h)

/-- Whenever at most `Δ` colors are excluded (`used.card ≤ Δ`), `firstFreeColor Δ used` is absent
from `used`. -/
theorem firstFreeColor_notMem {Δ : ℕ} {used : Finset ℕ} (hcard : used.card ≤ Δ) :
    firstFreeColor Δ used ∉ used := by
  have hex : ∃ c ∈ List.range (Δ + 1), c ∉ used := by
    by_contra! hall
    have hle := Finset.card_le_card (s := Finset.range (Δ + 1)) fun c hc =>
      hall c (List.mem_range.2 (Finset.mem_range.1 hc))
    rw [Finset.card_range] at hle
    omega
  unfold firstFreeColor
  cases h : (List.range (Δ + 1)).find? (fun c => decide (c ∉ used)) with
  | none =>
    obtain ⟨c, hc_mem, hc_not⟩ := hex
    exact absurd (by simpa using List.find?_eq_none.1 h c hc_mem) hc_not
  | some c => simpa using List.find?_some h

/-- One step of greedy local-maximum color reduction ([Hirvonen and Suomela][HirvonenSuomela2020],
§4.5, Lemma 4.1, p. 69): a node whose color strictly exceeds every neighbor's color recolors to
`firstFreeColor Δ nbrs`; all other nodes keep their color. -/
@[expose] def greedyStep (Δ own : ℕ) (nbrs : Finset ℕ) : ℕ :=
  if ∀ b ∈ nbrs, b < own then firstFreeColor Δ nbrs else own

/-- On any graph `H` where every vertex has degree at most `Δ`, applying `greedyStep Δ` to a proper
coloring `f : V → ℕ` preserves properness. -/
theorem greedyStep_ne_of_adj {V : Type*} {H : SimpleGraph V} [H.LocallyFinite]
    {Δ : ℕ} (hdeg : ∀ w, H.degree w ≤ Δ) {f : V → ℕ}
    (hf : ∀ u v, H.Adj u v → f u ≠ f v) {u v : V} (huv : H.Adj u v) :
    greedyStep Δ (f u) ((H.neighborFinset u).image f) ≠
      greedyStep Δ (f v) ((H.neighborFinset v).image f) := by
  have hfu_mem : f u ∈ (H.neighborFinset v).image f :=
    Finset.mem_image.2 ⟨u, (H.mem_neighborFinset v u).2 huv.symm, rfl⟩
  have hfv_mem : f v ∈ (H.neighborFinset u).image f :=
    Finset.mem_image.2 ⟨v, (H.mem_neighborFinset u v).2 huv, rfl⟩
  have hcard : ∀ w, ((H.neighborFinset w).image f).card ≤ Δ := fun w =>
    Finset.card_image_le.trans ((SimpleGraph.card_neighborFinset_eq_degree _ _).trans_le (hdeg w))
  unfold greedyStep
  split_ifs with hau hav
  · exact absurd (hau (f v) hfv_mem) (not_lt_of_gt (hav (f u) hfu_mem))
  · exact fun heq => firstFreeColor_notMem (hcard u) (heq ▸ hfv_mem)
  · exact fun heq => firstFreeColor_notMem (hcard v) (heq.symm ▸ hfu_mem)
  · exact hf u v huv

/-- On any graph `H` where every vertex has degree at most `Δ`, if `f` is proper on `H` and bounded
below `q`, then `greedyStep Δ` produces colors bounded below `max (q - 1) (Δ + 1)`. -/
theorem greedyStep_lt {V : Type*} {H : SimpleGraph V} [H.LocallyFinite]
    {Δ q : ℕ} {f : V → ℕ} (hf : ∀ u v, H.Adj u v → f u ≠ f v) (hq : ∀ w, f w < q) (u : V) :
    greedyStep Δ (f u) ((H.neighborFinset u).image f) < max (q - 1) (Δ + 1) := by
  unfold greedyStep
  split_ifs with hau
  · exact (firstFreeColor_lt Δ _).trans_le (le_max_right _ _)
  · push Not at hau
    obtain ⟨b, hb_mem, hb_le⟩ := hau
    obtain ⟨w, hw_mem, rfl⟩ := Finset.mem_image.1 hb_mem
    have := hf u w ((H.mem_neighborFinset u w).1 hw_mem)
    have := hq w
    omega

/-- One-round greedy local-maximum color reduction as a `BroadcastProtocol`. -/
@[expose] def greedyColorReduction (Δ : ℕ) : BroadcastProtocol ℕ ℕ ℕ ℕ :=
  BroadcastProtocol.fullInfo id (fun _ own ms => greedyStep Δ own ms.toFinset) id

private theorem multiset_map_toFinset_eq_image {V α : Type*} [DecidableEq α]
    (s : Finset V) (f : V → α) :
    (s.val.map f).toFinset = s.image f := by
  ext a
  simp only [Multiset.mem_toFinset, Multiset.mem_map, Finset.mem_val, Finset.mem_image]

/-- Step towards `#7505` (not the cited endpoint, after Lemma 4.1 of
[Hirvonen and Suomela][HirvonenSuomela2020], §4.5, p. 69): running `greedyColorReduction Δ` for `r`
rounds on a finite simple graph `G` with `G.maxDegree ≤ Δ` from a proper `q`-coloring preserves
properness and bounds every output color below `max (q - r) (Δ + 1)`. -/
theorem greedyColorReduction_run {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {Δ q : ℕ} (hΔ : G.maxDegree ≤ Δ)
    {x : V → ℕ} (hx : ∀ u v, G.Adj u v → x u ≠ x v) (hq : ∀ u, x u < q) (r : ℕ) :
    (∀ u v, G.Adj u v → (greedyColorReduction Δ).run G x r u ≠
      (greedyColorReduction Δ).run G x r v) ∧
      ∀ u, (greedyColorReduction Δ).run G x r u < max (q - r) (Δ + 1) := by
  have hdeg : ∀ w, G.degree w ≤ Δ := fun w => (G.degree_le_maxDegree w).trans hΔ
  have hrun_eq : ∀ s u, (greedyColorReduction Δ).run G x s u =
      (greedyColorReduction Δ).state G x s u := fun _ _ => rfl
  simp only [hrun_eq]
  induction r with
  | zero =>
    exact ⟨hx, fun u => (hq u).trans_le (by have := hq u; omega)⟩
  | succ r ih =>
    obtain ⟨ih_ne, ih_lt⟩ := ih
    have hst : ∀ w, (greedyColorReduction Δ).state G x (r + 1) w =
        greedyStep Δ ((greedyColorReduction Δ).state G x r w)
          ((G.neighborFinset w).image ((greedyColorReduction Δ).state G x r)) := fun w => by
      rw [BroadcastProtocol.state_succ]
      dsimp only [greedyColorReduction, BroadcastProtocol.fullInfo]
      rw [multiset_map_toFinset_eq_image]
    refine ⟨fun u v huv => by rw [hst u, hst v]; exact greedyStep_ne_of_adj hdeg ih_ne huv,
      fun u => ?_⟩
    have hlt := greedyStep_lt (Δ := Δ) ih_ne ih_lt u
    rw [hst u]
    omega

/-! ### Kuhn–Wattenhofer one-round disjoint-block palette compression -/

/-- The Kuhn–Wattenhofer one-round target palette size `⌈m (Δ + 1) / (Δ + 2)⌉`
([Kuhn and Wattenhofer][KuhnWattenhofer2006], §5, Theorem 5.1, p. 12). -/
@[expose] def kwBound (Δ m : ℕ) : ℕ :=
  (m * (Δ + 1) + (Δ + 1)) / (Δ + 2)

/-- Helper step towards `#7505` (not the cited endpoint, after Theorem 5.1 of
[Kuhn and Wattenhofer][KuhnWattenhofer2006], §5, p. 12): `q + ⌊q / (Δ + 1)⌋ ≥ m` for
`q = kwBound Δ m`. -/
private theorem le_kwBound_add_div (Δ m : ℕ) :
    m ≤ kwBound Δ m + kwBound Δ m / (Δ + 1) := by
  set q := kwBound Δ m
  have hdiv : (Δ + 2) * q + _ = _ := Nat.div_add_mod (m * (Δ + 1) + (Δ + 1)) (Δ + 2)
  have hmod := Nat.mod_lt (m * (Δ + 1) + (Δ + 1)) (by omega : 0 < Δ + 2)
  have hq_div := Nat.div_add_mod q (Δ + 1)
  have hq_mod : q % (Δ + 1) < Δ + 1 := Nat.mod_lt q (by omega)
  have hsplit : (Δ + 2) * q = (Δ + 1) * q + q := Nat.succ_mul _ _
  have h3 : (Δ + 1) * m < (Δ + 1) * (q + (q / (Δ + 1) + 1)) := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_comm (Δ + 1) m]
    omega
  have h4 : m < q + (q / (Δ + 1) + 1) := Nat.lt_of_mul_lt_mul_left h3
  omega

/-- Whenever `Δ + 2 ≤ m`, `kwBound Δ m` strictly shrinks the palette (`kwBound Δ m < m`) while
remaining at least `Δ + 1`. -/
theorem kwBound_lt {Δ m : ℕ} (hm : Δ + 2 ≤ m) : Δ + 1 ≤ kwBound Δ m ∧ kwBound Δ m < m := by
  unfold kwBound
  have hdiv := Nat.div_add_mod (m * (Δ + 1) + (Δ + 1)) (Δ + 2)
  have hmod := Nat.mod_lt (m * (Δ + 1) + (Δ + 1)) (by omega : 0 < Δ + 2)
  constructor
  · have hlow : (Δ + 2) * (Δ + 1) ≤ m * (Δ + 1) + (Δ + 1) :=
      le_trans (Nat.mul_le_mul_right (Δ + 1) hm) (Nat.le_add_right _ _)
    exact (Nat.le_div_iff_mul_le (by omega)).2 (by rw [Nat.mul_comm]; exact hlow)
  · rw [Nat.div_lt_iff_lt_mul (by omega)]
    calc m * (Δ + 1) + (Δ + 1) < m * (Δ + 1) + m := by omega
      _ = m * (Δ + 2) := by rw [← Nat.mul_succ]

/-- Kuhn–Wattenhofer local compression rule: colors below `q = kwBound Δ m` stay fixed; a high
color `own ≥ q` with `i = own - q` picks the first color in block
`{i (Δ + 1), …, (i + 1)(Δ + 1) - 1}` unused by its neighbors' initial colors. -/
@[expose] def kwCompress (Δ m own : ℕ) (nbrs : Finset ℕ) : ℕ :=
  let q := kwBound Δ m
  if own < q then own
  else
    let i := own - q
    let base := i * (Δ + 1)
    let localUsed := (nbrs.filter fun b => base ≤ b).image fun b => b - base
    base + firstFreeColor Δ localUsed

/-- Kuhn–Wattenhofer one-round palette compression as a `BroadcastProtocol`. -/
@[expose] def kwCompressProtocol (Δ m : ℕ) : BroadcastProtocol ℕ ℕ ℕ ℕ :=
  BroadcastProtocol.fullInfo id (fun _ own ms => kwCompress Δ m own ms.toFinset) id

/-- Step towards `#7505` (not the cited endpoint, after Theorem 5.1 of
[Kuhn and Wattenhofer][KuhnWattenhofer2006], §5, p. 12): in a single broadcast round on any finite
simple graph `G` with `G.maxDegree ≤ Δ`, `kwCompressProtocol Δ m` turns any proper `m`-coloring
into a proper coloring with colors below `kwBound Δ m = ⌈m (Δ + 1) / (Δ + 2)⌉`. -/
theorem kwCompressProtocol_run {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {Δ m : ℕ} (hΔ : G.maxDegree ≤ Δ)
    {x : V → ℕ} (hx : ∀ u v, G.Adj u v → x u ≠ x v) (hm : ∀ u, x u < m) :
    (∀ u v, G.Adj u v → (kwCompressProtocol Δ m).run G x 1 u ≠
      (kwCompressProtocol Δ m).run G x 1 v) ∧
      ∀ u, (kwCompressProtocol Δ m).run G x 1 u < kwBound Δ m := by
  have hrun : ∀ w, (kwCompressProtocol Δ m).run G x 1 w =
      kwCompress Δ m (x w) ((G.neighborFinset w).image x) := fun w => by
    change kwCompress Δ m (x w) (((G.neighborFinset w).val.map x).toFinset) = _
    rw [multiset_map_toFinset_eq_image]
  have hcard_used : ∀ w base,
      ((((G.neighborFinset w).image x).filter fun b => base ≤ b).image fun b => b - base).card ≤
        Δ := fun w _ =>
    Finset.card_image_le.trans
      ((Finset.card_filter_le _ _).trans
        (Finset.card_image_le.trans ((G.degree_le_maxDegree w).trans hΔ)))
  have hnot_nbr : ∀ w base,
      base + firstFreeColor Δ
        ((((G.neighborFinset w).image x).filter fun b => base ≤ b).image fun b => b - base) ∉
        (G.neighborFinset w).image x := by
    intro w base hmem
    exact firstFreeColor_notMem (hcard_used w base) <| Finset.mem_image.2
      ⟨_, Finset.mem_filter.2 ⟨hmem, Nat.le_add_right _ _⟩, Nat.add_sub_cancel_left _ _⟩
  refine ⟨fun u v huv => ?_, fun u => ?_⟩
  · rw [hrun u, hrun v]
    have hne : x u ≠ x v := hx u v huv
    have hxu_in_v : x u ∈ (G.neighborFinset v).image x :=
      Finset.mem_image.2 ⟨u, (G.mem_neighborFinset v u).2 huv.symm, rfl⟩
    have hxv_in_u : x v ∈ (G.neighborFinset u).image x :=
      Finset.mem_image.2 ⟨v, (G.mem_neighborFinset u v).2 huv, rfl⟩
    unfold kwCompress
    dsimp only
    split_ifs with hu hv
    · exact hne
    · exact fun heq => hnot_nbr v ((x v - kwBound Δ m) * (Δ + 1)) (heq ▸ hxu_in_v)
    · exact fun heq => hnot_nbr u ((x u - kwBound Δ m) * (Δ + 1)) (heq.symm ▸ hxv_in_u)
    · intro heq
      have h := congrArg (· / (Δ + 1)) heq
      simp [Nat.mul_comm _ (Δ + 1), Nat.mul_add_div, Nat.div_eq_of_lt (firstFreeColor_lt _ _)] at h
      omega
  · rw [hrun u]
    unfold kwCompress
    dsimp only
    split_ifs with hu
    · exact hu
    · have hi_lt : x u - kwBound Δ m < kwBound Δ m / (Δ + 1) := by
        have := le_kwBound_add_div Δ m; have := hm u; omega
      refine (Nat.add_lt_add_left (firstFreeColor_lt _ _) _).trans_le ?_
      rw [← Nat.add_one_mul]
      exact (Nat.mul_le_mul_right (Δ + 1) hi_lt).trans (Nat.div_mul_le_self _ _)

/-! ### Orientation-decomposed Cole–Vishkin `(Δ + 1)`-coloring in `O(log* C + Δ²)` rounds -/

/-- Local node state for `deltaPlusOneColoring Δ C`. -/
structure ColoringState (Δ : ℕ) where
  /-- Node's permanent initial identifier. -/
  uid : ℕ
  /-- Sorted list of neighbor UIDs recorded in Round `0` (length `= G.degree u ≤ Δ`). -/
  nbrUIDs : List ℕ
  /-- Per-slot Cole–Vishkin color across the `Δ` functional out-edge orientations. -/
  slotColor : Fin Δ → ℕ
  /-- Merged color maintained across the `Δ` greedy orientation-merging phases. -/
  mergedColor : ℕ
  deriving @[expose] DecidableEq

/-- Round bound for `deltaPlusOneColoring Δ C`: `1` discovery round, `Nat.logStar C` parallel
Cole–Vishkin rounds, and `Δ` merging phases of `5 (Δ + 1)` greedy reduction rounds each. -/
@[expose] def deltaPlusOneRounds (Δ C : ℕ) : ℕ :=
  1 + Nat.logStar C + 5 * Δ * (Δ + 1)

/-- Explicit `O(Δ log* C + Δ²)` bound: for `1 ≤ Δ`, `deltaPlusOneRounds Δ C` is bounded by
`Δ * Nat.logStar C + 10 * Δ ^ 2 + 1` (and in fact equals `1 + Nat.logStar C + 5 * Δ * (Δ + 1)`). -/
theorem deltaPlusOneRounds_le {Δ : ℕ} (hΔ : 1 ≤ Δ) (C : ℕ) :
    deltaPlusOneRounds Δ C ≤ Δ * Nat.logStar C + 10 * Δ ^ 2 + 1 := by
  unfold deltaPlusOneRounds
  have h1 : Nat.logStar C ≤ Δ * Nat.logStar C := Nat.le_mul_of_pos_left _ hΔ
  have h2 : Δ ≤ Δ * Δ := Nat.le_mul_self Δ
  rw [Nat.pow_two, Nat.mul_assoc, Nat.mul_add, Nat.mul_one]
  omega

/-- Deterministic `(Δ + 1)`-coloring step function at round `r`. -/
@[expose] def deltaPlusOneStep (Δ C r : ℕ) (s : ColoringState Δ)
    (msgs : Multiset (ColoringState Δ)) : ColoringState Δ :=
  let K := Nat.logStar C
  let L := 5 * (Δ + 1)
  if r = 0 then
    { s with nbrUIDs := (msgs.map ColoringState.uid).sort (· ≤ ·) }
  else if hrK : r < 1 + K then
    { s with
      slotColor := fun i =>
        match s.nbrUIDs[i.val]? with
        | none => cvColor (s.slotColor i) (if s.slotColor i = 0 then 1 else 0)
        | some tid =>
          let target :=
            ((msgs.filterMap fun m : ColoringState Δ =>
              if m.uid = tid then some (m.slotColor i) else none).sort (· ≤ ·)).headD 0
          cvColor (s.slotColor i) target }
  else if hphase : r < 1 + K + Δ * L then
    let offset := r - (1 + K)
    let k := offset / L
    let j := offset % L
    have hk : k < Δ := by
      dsimp only [k, offset, K, L] at hrK hphase ⊢
      exact (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    let kFin : Fin Δ := ⟨k, hk⟩
    let valOf : ColoringState Δ → ℕ :=
      if j = 0 then fun m => 6 * m.mergedColor + m.slotColor kFin
      else ColoringState.mergedColor
    let activeMsgs := msgs.filterMap fun m : ColoringState Δ =>
      if m.uid ∈ s.nbrUIDs.take (k + 1) ∨ s.uid ∈ m.nbrUIDs.take (k + 1) then
        some (valOf m)
      else none
    { s with mergedColor := greedyStep Δ (valOf s) activeMsgs.toFinset }
  else
    s

/-- Deterministic synchronous `LOCAL` `(Δ + 1)`-coloring protocol (`BroadcastProtocol`) from
injective node identifiers below `C` on graphs of maximum degree `≤ Δ`. -/
@[expose] def deltaPlusOneColoring (Δ C : ℕ) :
    BroadcastProtocol ℕ (ColoringState Δ) (ColoringState Δ) (Fin (Δ + 1)) :=
  BroadcastProtocol.fullInfo
    (fun x => { uid := x, nbrUIDs := [], slotColor := fun _ => x, mergedColor := 0 })
    (deltaPlusOneStep Δ C)
    (fun s => Fin.clamp s.mergedColor Δ)

section Correctness

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem deltaPlusOneColoring_state_succ (Δ C : ℕ) (x : V → ℕ) (r : ℕ) (u : V) :
    (deltaPlusOneColoring Δ C).state G x (r + 1) u =
      deltaPlusOneStep Δ C r ((deltaPlusOneColoring Δ C).state G x r u)
        ((G.neighborFinset u).val.map ((deltaPlusOneColoring Δ C).state G x r)) := rfl

private theorem deltaPlusOneColoring_run_eq (Δ C : ℕ) (x : V → ℕ) (r : ℕ) (u : V) :
    (deltaPlusOneColoring Δ C).run G x r u =
      Fin.clamp (((deltaPlusOneColoring Δ C).state G x r u).mergedColor) Δ := rfl

/-- Canonical sorted neighbor UID list of `u` under `x`. -/
private def nbrList (x : V → ℕ) (u : V) : List ℕ :=
  ((G.neighborFinset u).val.map x).sort (· ≤ ·)

private theorem length_nbrList (x : V → ℕ) (u : V) :
    (nbrList G x u).length = G.degree u := by
  simp only [nbrList, Multiset.length_sort, Multiset.card_map, ← Finset.card_def,
    SimpleGraph.card_neighborFinset_eq_degree]

private theorem mem_nbrList_iff {x : V → ℕ} (hx : Function.Injective x) {u w : V} :
    x w ∈ nbrList G x u ↔ G.Adj u w := by
  simp only [nbrList, Multiset.mem_sort, Multiset.mem_map, Finset.mem_val,
    SimpleGraph.mem_neighborFinset]
  exact ⟨fun ⟨z, hz, hzx⟩ => hx hzx ▸ hz, fun huw => ⟨w, huw, rfl⟩⟩

/-- Symmetric partial graph `G_at k` formed by edges appearing among the first `k` sorted neighbor
slots of either endpoint. -/
private def partialGraph (x : V → ℕ) (k : ℕ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ (x v ∈ (nbrList G x u).take k ∨ x u ∈ (nbrList G x v).take k)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

private instance (x : V → ℕ) (k : ℕ) : DecidableRel (partialGraph G x k).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

private instance (x : V → ℕ) (k : ℕ) : (partialGraph G x k).LocallyFinite :=
  inferInstance

private theorem partialGraph_degree_le (x : V → ℕ) (k : ℕ) (u : V) :
    (partialGraph G x k).degree u ≤ G.degree u := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_le_card fun w hw => ?_
  exact (SimpleGraph.mem_neighborFinset _ _ _).2
    ((SimpleGraph.mem_neighborFinset _ _ _).1 hw).1

private theorem partialGraph_zero_not_adj (x : V → ℕ) (u v : V) :
    ¬ (partialGraph G x 0).Adj u v := by
  simp [partialGraph]

private theorem partialGraph_eq_self {Δ : ℕ} (hΔ : G.maxDegree ≤ Δ) {x : V → ℕ}
    (hx : Function.Injective x) {u v : V} :
    (partialGraph G x Δ).Adj u v ↔ G.Adj u v := by
  refine ⟨fun h => h.1, fun huv => ⟨huv, Or.inl ?_⟩⟩
  have hlen : (nbrList G x u).length ≤ Δ :=
    (length_nbrList G x u).trans_le ((G.degree_le_maxDegree u).trans hΔ)
  rw [List.take_of_length_le hlen]
  exact (mem_nbrList_iff G hx).2 huv

private theorem state_uid (Δ C : ℕ) (x : V → ℕ) (r : ℕ) (u : V) :
    ((deltaPlusOneColoring Δ C).state G x r u).uid = x u := by
  induction r generalizing u with
  | zero => rfl
  | succ r ih =>
    rw [deltaPlusOneColoring_state_succ]
    dsimp only [deltaPlusOneStep]
    split_ifs <;> exact ih u

private theorem state_nbrUIDs_of_pos (Δ C : ℕ) (x : V → ℕ) {r : ℕ} (hr : 1 ≤ r) (u : V) :
    ((deltaPlusOneColoring Δ C).state G x r u).nbrUIDs = nbrList G x u := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hr
  clear hr
  induction t generalizing u with
  | zero =>
    change ((deltaPlusOneColoring Δ C).state G x (0 + 1) u).nbrUIDs = nbrList G x u
    rw [deltaPlusOneColoring_state_succ]
    simp only [deltaPlusOneStep, nbrList, ↓reduceIte, Multiset.map_map]; rfl
  | succ t ih =>
    have hpos : 1 + t ≠ 0 := by omega
    rw [← Nat.add_assoc, deltaPlusOneColoring_state_succ]
    simp only [deltaPlusOneStep, hpos, ↓reduceIte]
    split_ifs <;> exact ih u

private theorem two_le_iterate_cvBound {C : ℕ} (hC : 2 ≤ C) (s : ℕ) :
    2 ≤ cvBound^[s] C := by
  induction s with
  | zero => exact hC
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    exact Nat.le_mul_of_pos_right 2 (Nat.clog_pos one_lt_two (by omega))

private theorem multiset_filterMap_eq_zero {α β : Type*} {m : Multiset α} {f : α → Option β}
    (h : ∀ a ∈ m, f a = none) : m.filterMap f = 0 :=
  Multiset.eq_zero_of_forall_notMem fun b hb => by
    obtain ⟨a, ha, hfa⟩ := (Multiset.mem_filterMap _ _).1 hb
    simp [h a ha] at hfa

private theorem filterMap_unique_neighbor {Δ C : ℕ} {x : V → ℕ} (hx : Function.Injective x)
    (r : ℕ) (u w : V) (huw : G.Adj u w) (i : Fin Δ) :
    ((((G.neighborFinset u).val.map ((deltaPlusOneColoring Δ C).state G x r)).filterMap
      fun m : ColoringState Δ =>
        if m.uid = x w then some (m.slotColor i) else none).sort (· ≤ ·)).headD 0 =
      ((deltaPlusOneColoring Δ C).state G x r w).slotColor i := by
  classical
  have hmem : w ∈ (G.neighborFinset u).val := (G.mem_neighborFinset u w).2 huw
  have hnodup : (G.neighborFinset u).val.Nodup := (G.neighborFinset u).nodup
  rw [← Multiset.cons_erase hmem] at hnodup ⊢
  obtain ⟨hw_not, _⟩ := Multiset.nodup_cons.1 hnodup
  rw [Multiset.map_cons, Multiset.filterMap_cons, state_uid G Δ C x r w]
  simp only [↓reduceIte, Option.map_some, Option.getD_some]
  have hzero : ((((G.neighborFinset u).val.erase w).map
      ((deltaPlusOneColoring Δ C).state G x r)).filterMap fun m : ColoringState Δ =>
        if m.uid = x w then some (m.slotColor i) else none) = 0 := by
    refine multiset_filterMap_eq_zero fun m hm => ?_
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hm
    have hzw : z ≠ w := fun h => hw_not (h ▸ hz)
    rw [state_uid G Δ C x r z]
    simp only [hx.eq_iff.not.2 hzw, ↓reduceIte]
  rw [hzero, add_zero, Multiset.sort_singleton]
  rfl

/-- After Round `0` and `s ≤ Nat.logStar C` Cole–Vishkin rounds, every slot coloring is proper on
its directed out-edges, bounded by `cvBound^[s] C` when `2 ≤ C` (or `< C` when `s = 0`), and
`mergedColor = 0`. -/
private theorem state_cv_phase {Δ C : ℕ} {x : V → ℕ} (hx : Function.Injective x)
    (hC : ∀ u, x u < C) {s : ℕ} (hs : s ≤ Nat.logStar C) :
    (∀ (i : Fin Δ) (u w : V), G.Adj u w → (nbrList G x u)[i.val]? = some (x w) →
      ((deltaPlusOneColoring Δ C).state G x (1 + s) u).slotColor i ≠
        ((deltaPlusOneColoring Δ C).state G x (1 + s) w).slotColor i) ∧
    (∀ (i : Fin Δ) (u : V),
      ((deltaPlusOneColoring Δ C).state G x (1 + s) u).slotColor i <
        if s = 0 then C else cvBound^[s] C) ∧
    ∀ u : V, ((deltaPlusOneColoring Δ C).state G x (1 + s) u).mergedColor = 0 := by
  induction s with
  | zero =>
    exact ⟨fun i u w huw _ heq => G.ne_of_adj huw (hx heq), fun i u => hC u, fun _ => rfl⟩
  | succ s ih =>
    have hC2 : 2 ≤ C := by
      by_contra; have := Nat.logStar_of_le_one (n := C) (by omega); omega
    obtain ⟨ih_ne, ih_lt, ih_m⟩ := ih (by omega)
    have ih_lt' : ∀ (i : Fin Δ) (u : V),
        ((deltaPlusOneColoring Δ C).state G x (1 + s) u).slotColor i < cvBound^[s] C :=
      fun i u => by cases s <;> simpa using ih_lt i u
    have hnz : 1 + s ≠ 0 := by omega
    have hlt : 1 + s < 1 + Nat.logStar C := by omega
    have hstep_eq : ∀ (i : Fin Δ) (u : V),
        ((deltaPlusOneColoring Δ C).state G x (1 + (s + 1)) u).slotColor i =
          match (nbrList G x u)[i.val]? with
          | none =>
            let a := ((deltaPlusOneColoring Δ C).state G x (1 + s) u).slotColor i
            cvColor a (if a = 0 then 1 else 0)
          | some tid =>
            let target :=
              ((((G.neighborFinset u).val.map
                ((deltaPlusOneColoring Δ C).state G x (1 + s))).filterMap fun m =>
                  if m.uid = tid then some (m.slotColor i) else none).sort (· ≤ ·)).headD 0
            cvColor (((deltaPlusOneColoring Δ C).state G x (1 + s) u).slotColor i) target := by
      intro i u
      rw [← Nat.add_assoc, deltaPlusOneColoring_state_succ]
      dsimp only [deltaPlusOneStep]
      simp only [hnz, ↓reduceIte, hlt, ↓reduceDIte]
      rw [state_nbrUIDs_of_pos G Δ C x (by omega : 1 ≤ 1 + s) u]
    have hm_succ : ∀ u, ((deltaPlusOneColoring Δ C).state G x (1 + (s + 1)) u).mergedColor = 0 := by
      intro u
      rw [← Nat.add_assoc, deltaPlusOneColoring_state_succ]
      dsimp only [deltaPlusOneStep]
      simp only [hnz, ↓reduceIte, hlt, ↓reduceDIte]
      exact ih_m u
    refine ⟨fun i u w huw hout => ?_, fun i u => ?_, hm_succ⟩
    · rw [hstep_eq i u, hout]
      dsimp only
      rw [filterMap_unique_neighbor G hx (1 + s) u w huw i, hstep_eq i w]
      cases (nbrList G x w)[i.val]? <;> exact cvColor_ne (ih_ne i u w huw hout)
    · simp only [Nat.succ_ne_zero, ↓reduceIte, Function.iterate_succ_apply']
      rw [hstep_eq i u]
      have h2B : 2 ≤ cvBound^[s] C := two_le_iterate_cvBound hC2 s
      cases hopt : (nbrList G x u)[i.val]? with
      | none =>
        dsimp only
        have ha := ih_lt' i u
        exact cvColor_lt (by split_ifs <;> omega) ha (by split_ifs <;> omega)
      | some tid =>
        obtain ⟨w, hw_mem, rfl⟩ :=
          Multiset.mem_map.1 ((Multiset.mem_sort _).1 (List.mem_of_getElem? hopt))
        have huw : G.Adj u w := (G.mem_neighborFinset u w).1 hw_mem
        dsimp only
        rw [filterMap_unique_neighbor G hx (1 + s) u w huw i]
        exact cvColor_lt (ih_ne i u w huw hopt) (ih_lt' i u) (ih_lt' i w)

/-- After `1 + Nat.logStar C` rounds, all `Δ` slot colorings stay fixed for all subsequent rounds,
take values `< 6`, and properly color their respective out-edges. -/
private theorem slotColor_after_cv {Δ C : ℕ} {x : V → ℕ} (hx : Function.Injective x)
    (hC : ∀ u, x u < C) :
    (∀ t u, ((deltaPlusOneColoring Δ C).state G x (1 + Nat.logStar C + t) u).slotColor =
      ((deltaPlusOneColoring Δ C).state G x (1 + Nat.logStar C) u).slotColor) ∧
    (∀ (i : Fin Δ) (u w : V), G.Adj u w → (nbrList G x u)[i.val]? = some (x w) →
      ((deltaPlusOneColoring Δ C).state G x (1 + Nat.logStar C) u).slotColor i ≠
        ((deltaPlusOneColoring Δ C).state G x (1 + Nat.logStar C) w).slotColor i) ∧
    ∀ (i : Fin Δ) (u : V),
      ((deltaPlusOneColoring Δ C).state G x (1 + Nat.logStar C) u).slotColor i < 6 := by
  obtain ⟨hcv_ne, hcv_lt, _⟩ := state_cv_phase G hx hC le_rfl
  refine ⟨?_, hcv_ne, fun i u => ?_⟩
  · intro t u
    induction t generalizing u with
    | zero => rfl
    | succ t ih =>
      have hnz : 1 + Nat.logStar C + t ≠ 0 := by omega
      have hnlt : ¬ 1 + Nat.logStar C + t < 1 + Nat.logStar C := by omega
      rw [← Nat.add_assoc, deltaPlusOneColoring_state_succ]
      simp only [deltaPlusOneStep, hnz, ↓reduceIte, hnlt, ↓reduceDIte]
      split_ifs <;> exact ih u
  · have h := hcv_lt i u
    split_ifs at h with hs0
    · have : C ≤ 1 := by by_contra; have := Nat.logStar_of_two_le (n := C) (by omega); omega
      omega
    · exact lt_of_lt_of_le h (iterate_cvBound_logStar_le C)

private theorem getElem?_eq_some_of_mem_take_succ {α : Type*} {l : List α} {k : ℕ} {a : α}
    (hmem : a ∈ l.take (k + 1)) (hnot : a ∉ l.take k) : l[k]? = some a := by
  rw [List.take_add_one, List.mem_append] at hmem
  simpa [hnot] using hmem

/-- Adding slot `k` turns a proper `(Δ + 1)`-coloring of `partialGraph G x k` into a proper
`6 (Δ + 1)`-coloring of `partialGraph G x (k + 1)`. -/
private theorem combined_proper_partialGraph {x : V → ℕ} {k : ℕ} {mc : V → ℕ} {sc : V → ℕ}
    (hmc_prop : ∀ u v, (partialGraph G x k).Adj u v → mc u ≠ mc v)
    (hsc_lt : ∀ u, sc u < 6)
    (hsc_ne : ∀ u w, G.Adj u w → (nbrList G x u)[k]? = some (x w) → sc u ≠ sc w)
    {u v : V} (huv : (partialGraph G x (k + 1)).Adj u v) :
    6 * mc u + sc u ≠ 6 * mc v + sc v := by
  have hsu := hsc_lt u
  have hsv := hsc_lt v
  by_cases hprev : (partialGraph G x k).Adj u v
  · have hne := hmc_prop u v hprev
    omega
  · obtain ⟨hn1, hn2⟩ := not_or.1 fun h => hprev ⟨huv.1, h⟩
    rcases huv.2 with hu | hv
    · have := hsc_ne u v huv.1 (getElem?_eq_some_of_mem_take_succ hu hn1); omega
    · have := hsc_ne v u huv.1.symm (getElem?_eq_some_of_mem_take_succ hv hn2); omega

private theorem activeMsgs_toFinset_eq {Δ C : ℕ} (x : V → ℕ) {r : ℕ} (hr : 1 ≤ r)
    (k : ℕ) (valOf : ColoringState Δ → ℕ) (u : V) :
    ((((G.neighborFinset u).val.map ((deltaPlusOneColoring Δ C).state G x r)).filterMap fun m =>
      if m.uid ∈ ((deltaPlusOneColoring Δ C).state G x r u).nbrUIDs.take (k + 1) ∨
          ((deltaPlusOneColoring Δ C).state G x r u).uid ∈ m.nbrUIDs.take (k + 1) then
        some (valOf m)
      else none)).toFinset =
      ((partialGraph G x (k + 1)).neighborFinset u).image
        (fun w => valOf ((deltaPlusOneColoring Δ C).state G x r w)) := by
  ext c
  simp only [Multiset.mem_toFinset, Multiset.mem_filterMap, Multiset.mem_map, Finset.mem_val,
    SimpleGraph.mem_neighborFinset, Finset.mem_image, exists_exists_and_eq_and, state_uid,
    state_nbrUIDs_of_pos G Δ C x hr, Option.ite_none_right_eq_some, Option.some.injEq]
  exact exists_congr fun _ => and_assoc.symm

/-- Inductive invariant across the `Δ` greedy orientation-merging phases: after `k` completed
phases (`0 ≤ k ≤ Δ`), `mergedColor` is a proper `(Δ + 1)`-coloring of `partialGraph G x k`. -/
private theorem state_merge_phases {Δ C : ℕ} (hΔ : G.maxDegree ≤ Δ) {x : V → ℕ}
    (hx : Function.Injective x) (hC : ∀ u, x u < C) {k : ℕ} (hk : k ≤ Δ) :
    (∀ u v, (partialGraph G x k).Adj u v →
      ((deltaPlusOneColoring Δ C).state G x
        (1 + Nat.logStar C + k * (5 * (Δ + 1))) u).mergedColor ≠
        ((deltaPlusOneColoring Δ C).state G x
          (1 + Nat.logStar C + k * (5 * (Δ + 1))) v).mergedColor) ∧
    ∀ u, ((deltaPlusOneColoring Δ C).state G x
      (1 + Nat.logStar C + k * (5 * (Δ + 1))) u).mergedColor < Δ + 1 := by
  obtain ⟨hslot_const, hslot_ne, hslot_lt⟩ := slotColor_after_cv G (Δ := Δ) hx hC
  obtain ⟨_, _, hm0⟩ := state_cv_phase G (Δ := Δ) hx hC le_rfl
  have hdeg_part : ∀ m w, (partialGraph G x m).degree w ≤ Δ := fun m w =>
    (partialGraph_degree_le G x m w).trans ((G.degree_le_maxDegree w).trans hΔ)
  induction k with
  | zero =>
    refine ⟨fun u v huv => absurd huv (partialGraph_zero_not_adj G x u v), fun u => ?_⟩
    simp only [Nat.zero_mul, Nat.add_zero]
    rw [hm0 u]
    exact Nat.succ_pos Δ
  | succ k ih =>
    obtain ⟨ih_prop, ih_lt⟩ := ih (by omega)
    have hk_lt : k < Δ := by omega
    let kFin : Fin Δ := ⟨k, hk_lt⟩
    let fj (j : ℕ) (w : V) : ℕ :=
      let st := (deltaPlusOneColoring Δ C).state G x (1 + Nat.logStar C + k * (5 * (Δ + 1)) + j) w
      if j = 0 then
        6 * st.mergedColor +
          ((deltaPlusOneColoring Δ C).state G x (1 + Nat.logStar C) w).slotColor kFin
      else st.mergedColor
    have hinv : ∀ j ≤ 5 * (Δ + 1),
        (∀ u v, (partialGraph G x (k + 1)).Adj u v → fj j u ≠ fj j v) ∧
          ∀ w, fj j w < 6 * (Δ + 1) - j := by
      intro j hj
      induction j with
      | zero =>
        refine ⟨fun u v huv => ?_, fun w => ?_⟩
        · exact combined_proper_partialGraph G ih_prop (hslot_lt kFin) (hslot_ne kFin) huv
        · have hm := ih_lt w; have hs := hslot_lt kFin w
          dsimp only [fj]; simp only [↓reduceIte, Nat.add_zero]; omega
      | succ j ihj =>
        obtain ⟨hfj_prop, hfj_lt⟩ := ihj (by omega)
        have hj : j < 5 * (Δ + 1) := hj
        set r := 1 + Nat.logStar C + k * (5 * (Δ + 1)) + j
        have hstep : ∀ w, fj (j + 1) w =
            greedyStep Δ (fj j w) (((partialGraph G x (k + 1)).neighborFinset w).image (fj j)) := by
          intro w
          have hfj : fj (j + 1) w = ((deltaPlusOneColoring Δ C).state G x
              (1 + Nat.logStar C + k * (5 * (Δ + 1)) + (j + 1)) w).mergedColor := by
            simp only [fj, Nat.succ_ne_zero, ↓reduceIte]
          rw [hfj, show 1 + Nat.logStar C + k * (5 * (Δ + 1)) + (j + 1) = r + 1 by omega]
          have hnz : r ≠ 0 := by omega
          have hnlt : ¬ r < 1 + Nat.logStar C := by omega
          have hphase : r < 1 + Nat.logStar C + Δ * (5 * (Δ + 1)) := by
            have := Nat.mul_le_mul_right (5 * (Δ + 1)) hk; rw [Nat.add_one_mul] at this; omega
          have hsub : r - (1 + Nat.logStar C) = j + k * (5 * (Δ + 1)) := by omega
          have hdiv : (r - (1 + Nat.logStar C)) / (5 * (Δ + 1)) = k := by
            rw [hsub, Nat.add_mul_div_right _ _ (by omega : 0 < 5 * (Δ + 1)),
              Nat.div_eq_of_lt hj, Nat.zero_add]
          have hmod : (r - (1 + Nat.logStar C)) % (5 * (Δ + 1)) = j := by
            rw [hsub, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
          have hk_r : (r - (1 + Nat.logStar C)) / (5 * (Δ + 1)) < Δ := hdiv ▸ hk_lt
          rw [deltaPlusOneColoring_state_succ]
          dsimp only [deltaPlusOneStep]
          simp only [hnz, ↓reduceIte, hnlt, hphase, ↓reduceDIte]
          rw [activeMsgs_toFinset_eq G (Δ := Δ) (C := C) x (by omega : 1 ≤ r)
            ((r - (1 + Nat.logStar C)) / (5 * (Δ + 1))) _ w]
          have hval_eq : ∀ z,
              (if (r - (1 + Nat.logStar C)) % (5 * (Δ + 1)) = 0 then
                fun m : ColoringState Δ =>
                  6 * m.mergedColor +
                    m.slotColor ⟨(r - (1 + Nat.logStar C)) / (5 * (Δ + 1)), hk_r⟩
               else ColoringState.mergedColor)
                ((deltaPlusOneColoring Δ C).state G x r z) = fj j z := by
            intro z
            simp only [hmod]
            by_cases hj0 : j = 0
            · subst hj0
              dsimp only [r, fj]
              simp only [↓reduceIte, Nat.add_zero]
              rw [hslot_const]
              congr 2
              exact Fin.ext hdiv
            · simp only [fj, hj0, ↓reduceIte]; rfl
          rw [hval_eq w, Finset.image_congr (fun z _ => hval_eq z), hdiv]
        refine ⟨fun u v huv => ?_, fun u => ?_⟩
        · rw [hstep u, hstep v]
          exact greedyStep_ne_of_adj (hdeg_part (k + 1)) hfj_prop huv
        · have hlt := greedyStep_lt (Δ := Δ) (f := fj j) hfj_prop hfj_lt u
          rw [hstep u]
          omega
    obtain ⟨hL_prop, hL_lt⟩ := hinv _ le_rfl
    simp only [fj, show 5 * (Δ + 1) ≠ 0 by omega, ↓reduceIte] at hL_prop hL_lt
    rw [Nat.add_one_mul, ← Nat.add_assoc]
    exact ⟨hL_prop, fun u => by have := hL_lt u; omega⟩

/-- After `deltaPlusOneRounds Δ C` rounds, every node's state remains permanently fixed. -/
theorem deltaPlusOneColoring_state_add (Δ C : ℕ) (x : V → ℕ) (t : ℕ) (u : V) :
    (deltaPlusOneColoring Δ C).state G x (deltaPlusOneRounds Δ C + t) u =
      (deltaPlusOneColoring Δ C).state G x (deltaPlusOneRounds Δ C) u := by
  induction t generalizing u with
  | zero => rfl
  | succ t ih =>
    have hnz : deltaPlusOneRounds Δ C + t ≠ 0 := by unfold deltaPlusOneRounds; omega
    have hnlt1 : ¬ deltaPlusOneRounds Δ C + t < 1 + Nat.logStar C := by
      unfold deltaPlusOneRounds; omega
    have hnlt2 : ¬ deltaPlusOneRounds Δ C + t < 1 + Nat.logStar C + Δ * (5 * (Δ + 1)) := by
      unfold deltaPlusOneRounds; rw [Nat.mul_comm 5 Δ, Nat.mul_assoc]; omega
    rw [← Nat.add_assoc, deltaPlusOneColoring_state_succ]
    dsimp only [deltaPlusOneStep]
    simp only [hnz, ↓reduceIte, hnlt1, hnlt2, ↓reduceDIte]
    exact ih u

/-- Step towards `#7505` (not the cited endpoint, after [Cole and Vishkin][ColeVishkin1986],
[Goldberg, Plotkin and Shannon][GoldbergPlotkinShannon1988], and
[Hirvonen and Suomela][HirvonenSuomela2020], §4.5): on any finite simple graph `G` with
`G.maxDegree ≤ Δ` and injective node identifiers `x : V → ℕ` bounded below `C`,
`deltaPlusOneColoring Δ C` outputs a proper `Fin (Δ + 1)`-coloring (`G.IsProperColoring`) in every
round `r ≥ deltaPlusOneRounds Δ C` (`= 1 + Nat.logStar C + 5 * Δ * (Δ + 1)`). -/
theorem deltaPlusOneColoring_isProperColoring {Δ C : ℕ} (hΔ : G.maxDegree ≤ Δ)
    {x : V → ℕ} (hx : Function.Injective x) (hC : ∀ u, x u < C)
    {r : ℕ} (hr : deltaPlusOneRounds Δ C ≤ r) :
    G.IsProperColoring ((deltaPlusOneColoring Δ C).run G x r) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hr
  obtain ⟨hprop, hlt⟩ := state_merge_phases G (C := C) hΔ hx hC le_rfl
  have hR : 1 + Nat.logStar C + Δ * (5 * (Δ + 1)) = deltaPlusOneRounds Δ C := by
    unfold deltaPlusOneRounds; rw [Nat.mul_comm 5 Δ, Nat.mul_assoc]
  rw [hR] at hprop hlt
  rw [SimpleGraph.isProperColoring_iff]
  intro u v huv heq
  have hval := congrArg Fin.val heq
  rw [deltaPlusOneColoring_run_eq, deltaPlusOneColoring_run_eq,
    deltaPlusOneColoring_state_add G Δ C x t u, deltaPlusOneColoring_state_add G Δ C x t v,
    Fin.coe_clamp, Fin.coe_clamp, Nat.min_eq_left (Nat.le_of_lt_succ (hlt u)),
    Nat.min_eq_left (Nat.le_of_lt_succ (hlt v))] at hval
  exact hprop u v ((partialGraph_eq_self G hΔ hx).2 huv) hval

/-- Construct a `SimpleGraph.Coloring` directly from `deltaPlusOneColoring Δ C` after
`r ≥ deltaPlusOneRounds Δ C` synchronous `LOCAL` rounds. -/
@[expose] def deltaPlusOneGraphColoring {Δ C : ℕ} (hΔ : G.maxDegree ≤ Δ)
    {x : V → ℕ} (hx : Function.Injective x) (hC : ∀ u, x u < C)
    {r : ℕ} (hr : deltaPlusOneRounds Δ C ≤ r) :
    G.Coloring (Fin (Δ + 1)) :=
  SimpleGraph.Coloring.mk ((deltaPlusOneColoring Δ C).run G x r) fun {_ _} huv =>
    (SimpleGraph.isProperColoring_iff G).1
      (deltaPlusOneColoring_isProperColoring G hΔ hx hC hr) _ _ huv

end Correctness

end Cslib.Distributed.LocalGraph
