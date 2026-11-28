/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.CFI
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.WeisfeilerLeman
public import CslibFrontier.Foundations.ModelTheory.Graph
public import CslibFrontier.Logics.FirstOrder.FiniteVariable.BijectiveGame
import CslibFrontier.Logics.FirstOrder.FiniteVariable.ColorRefinement
import CslibFrontier.Logics.FirstOrder.FiniteVariable.WeisfeilerLeman

/-!
# Cai–Fürer–Immerman separation of `C^{k+1}` and `k`-WL from graph isomorphism

For every `k : ℕ`, the uncolored Cai–Fürer–Immerman graphs `SimpleGraph.cfiEven k` and
`SimpleGraph.cfiOdd k` over `K_{2k + 4}` (`CslibFrontier.Foundations.Combinatorics.SimpleGraph.CFI`)
are finite, nonempty, and non-isomorphic (`SimpleGraph.isEmpty_iso_cfiEven_cfiOdd`), yet
indistinguishable by `(k + 1)`-variable counting logic `C^{k+1}`, `(k + 1)`-variable first-order
logic `FO^{k+1}`, and `k`-dimensional Weisfeiler–Leman (`k`-WL) ([CaiFurerImmerman1992], Section 6).

* **Back-and-forth invariant for `d + 1` pebbles over `K_m` (`2d + 4 ≤ m`).** A position `(S, a, b)`
  between `cfiGraph m 0` and `cfiGraph m (Pi.single u₀ 1)` satisfies `cfiInvariant` when there exist
  a twisted base vertex `u : Fin m` avoiding `⋃_{i ∈ S} (a i).support` and a graph isomorphism
  `φ : cfiGraph m (Pi.single u 1) ≃g cfiGraph m (Pi.single u₀ 1)` carrying `(a i).castAway u` to
  `b i` for every `i ∈ S`. When Spoiler moves pebble `j`, the remaining `≤ d` pebbles cover at most
  `2d` base vertices, leaving at least `(2d + 4) - (2d + 1) = 3` untouched vertices outside
  `insert u T`. Choosing two distinct untouched vertices `w ≠ w'`, Duplicator plays the bijection
  `(cfiBaseEquiv u w _).trans φ.toEquiv`:
  * if `u ∉ c.support`, the twist stays at `u`;
  * if `u ∈ c.support` and `w ∉ c.support`, `cfiSingleFlipIso` shifts the twist along `s(u, w)` to
    `w`;
  * if both `u, w ∈ c.support`, then `w' ∉ c.support` (`CFIVertex.notMem_support_of_mem_mem_ne`) and
    `cfiSingleFlipIso` shifts the twist along `s(u, w')` to `w'`.
* **Logical and `k`-WL consequences.** Specializing `m = 2k + 4` gives Duplicator's win in the
  infinite `(k + 1)`-pebble bijective game on `cfiEven k` and `cfiOdd k`
  (`bijPebbleWinsForever_cfiEven_cfiOdd`), hence agreement on all `C^{k+1}` and `FO^{k+1}` sentences
  (`realize_countingFormula_cfiEven_iff_cfiOdd`, `realize_formula_cfiEven_iff_cfiOdd`) and equality
  of `d`-WL histograms in every round for all `d ≤ k` (`wlHistogram_cfiEven_eq_cfiOdd_of_le`,
  `wlHistogram_cfiEven_eq_cfiOdd`). Using complete base graphs `K_{2k + 4}` yields graphs of size
  exponential in `k` rather than the `O(k)`-vertex expander construction of [CaiFurerImmerman1992].

## Main results

* `Cslib.Logic.FO.bijPebbleWinsForever_cfiGraph_zero_single`,
  `Cslib.Logic.FO.bijPebbleWinsForever_cfiEven_cfiOdd_of_le`,
  `Cslib.Logic.FO.bijPebbleWinsForever_cfiEven_cfiOdd`,
  `Cslib.Logic.FO.bijPebbleWins_cfiEven_cfiOdd`,
  `Cslib.Logic.FO.pebbleWinsForever_cfiEven_cfiOdd`: Duplicator wins the `(k + 1)`-pebble bijective
  and ordinary pebble games on `cfiEven k` and `cfiOdd k`.
* `Cslib.Logic.FO.realize_countingFormula_cfiEven_iff_cfiOdd`,
  `Cslib.Logic.FO.realize_formula_cfiEven_iff_cfiOdd`: `cfiEven k` and `cfiOdd k` satisfy the same
  `C^{k+1}` and `FO^{k+1}` sentences.
* `Cslib.Logic.FO.wlHistogram_cfiGraph_eq`, `Cslib.Logic.FO.wlHistogram_cfiEven_eq_cfiOdd_of_le`,
  `Cslib.Logic.FO.wlHistogram_cfiEven_eq_cfiOdd`, `Cslib.Logic.FO.colorHistogram_cfiEven_eq_cfiOdd`:
  `k`-WL (and `1`-WL color refinement for `1 ≤ k`) cannot distinguish `cfiEven k` from `cfiOdd k`.
* `Cslib.Logic.FO.bijPebbleWinsForever_cfiGraph_empty`,
  `Cslib.Logic.FO.realize_countingFormula_cfiGraph_iff`: any two twist functions on `K_m` (`2d + 4 ≤
  m`) yield `(d + 1)`-pebble bijectively equivalent and `C^{d+1}`-equivalent CFI graphs.
* `Cslib.Logic.FO.exists_nonisomorphic_wlHistogram_eq`: for every `k : ℕ`, there exist two
  non-isomorphic simple graphs on the same finite nonempty vertex type that agree on `k`-WL in every
  round and on every `C^{k+1}` sentence.

## References

* [J.-Y. Cai, M. Fürer, N. Immerman, *An optimal lower bound on the number of variables for graph
  identification*][CaiFurerImmerman1992], Section 6.
-/

public section

open FirstOrder Language Structure SimpleGraph

namespace Cslib.Logic.FO

/-! ### Back-and-forth invariant for the bijective pebble game on CFI graphs -/

section Invariant

private theorem cfiZeroAway {m : ℕ} (u : Fin m) :
    ∀ v ≠ u, (0 : Fin m → ZMod 2) v = (Pi.single u 1 : Fin m → ZMod 2) v :=
  fun v hv => by simp only [Pi.zero_apply, Pi.single_eq_of_ne hv]

private theorem castAway_congr {m : ℕ} {f g : Fin m → ZMod 2} {u : Fin m}
    {hfg : ∀ v ≠ u, f v = g v} {x y : CFIVertex m f} (hxy : x = y)
    (hx : u ∉ x.support) (hy : u ∉ y.support) :
    x.castAway u hfg hx = y.castAway u hfg hy := by
  subst hxy
  rfl

private def cfiInvariant {d m : ℕ} (u₀ : Fin m) (S : Set (Fin (d + 1)))
    (a : Fin (d + 1) → CFIVertex m 0) (b : Fin (d + 1) → CFIVertex m (Pi.single u₀ 1)) : Prop :=
  ∃ (u : Fin m) (φ : cfiGraph m (Pi.single u 1) ≃g cfiGraph m (Pi.single u₀ 1)),
    (∀ i ∈ S, u ∉ (a i).support) ∧
      ∀ i ∈ S, ∀ hi : u ∉ (a i).support, b i = φ ((a i).castAway u (cfiZeroAway u) hi)

private theorem isBijPebbleBackAndForth_cfiInvariant {d m : ℕ} (hm : 2 * d + 4 ≤ m) (u₀ : Fin m) :
    (letI := (cfiGraph m 0).structure; letI := (cfiGraph m (Pi.single u₀ 1)).structure
      IsBijPebbleBackAndForth Language.graph (cfiInvariant (d := d) u₀)) := by
  let := (cfiGraph m 0).structure
  let := (cfiGraph m (Pi.single u₀ 1)).structure
  refine ⟨fun {S a b} hI => ?_, fun {S a b} hI j => ?_⟩
  · obtain ⟨u, φ, hsupp, hmap⟩ := hI
    refine partialIsoOn_graph_iff.2 fun i hiS j hjS => ?_
    rw [hmap i hiS (hsupp i hiS), hmap j hjS (hsupp j hjS), φ.injective.eq_iff,
      CFIVertex.castAway_inj, φ.map_adj_iff, cfiGraph_adj_castAway_iff]
    exact ⟨Iff.rfl, Iff.rfl⟩
  · obtain ⟨u, φ, hsupp, hmap⟩ := hI
    let T : Finset (Fin m) := (Finset.univ.erase j).biUnion fun i => (a i).support
    have hcard_T : T.card ≤ 2 * d := by
      refine Finset.card_biUnion_le.trans ?_
      refine (Finset.sum_le_card_nsmul _ _ 2 fun i _ => (a i).card_support_le_two).trans ?_
      simp [Finset.card_erase_of_mem (Finset.mem_univ j), Nat.mul_comm]
    have hgt : 1 < (Finset.univ \ insert u T).card := by
      have := Finset.card_insert_le u T
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨w, hw_mem, w', hw'_mem, hww'⟩ := Finset.one_lt_card.1 hgt
    obtain ⟨⟨hwu, hwT⟩, hw'u, hw'T⟩ : (w ≠ u ∧ w ∉ T) ∧ w' ≠ u ∧ w' ∉ T := by
      simpa [not_or] using And.intro hw_mem hw'_mem
    have hother {z : Fin m} (hz : z ∉ T) (i : Fin (d + 1)) (hij : i ≠ j) : z ∉ (a i).support :=
      fun hzi => hz (Finset.mem_biUnion.2 ⟨i, Finset.mem_erase.2 ⟨hij, Finset.mem_univ i⟩, hzi⟩)
    let response := (cfiBaseEquiv u w hwu).trans φ.toEquiv
    refine ⟨response, fun c => ?_⟩
    -- the support condition for the updated position
    have hsupp' {u' : Fin m} (hc : u' ∉ c.support) (ho : ∀ i ∈ S, i ≠ j → u' ∉ (a i).support) :
        ∀ i ∈ insert j S, u' ∉ (Function.update a j c i).support := fun i hiS => by
      rcases eq_or_ne i j with rfl | hij
      · rwa [Function.update_self]
      · rw [Function.update_of_ne hij]
        exact ho i (Set.mem_of_mem_insert_of_ne hiS hij) hij
    -- Moving the twist to a fresh vertex needs a check at the new pebble.
    -- The cast-away flip law handles every other placed pebble.
    have moveTwist {u' : Fin m} (hu' : u' ≠ u) (hT : u' ∉ T) (hc : u' ∉ c.support)
        (hnew : cfiSingleFlipIso hu'.symm (c.castAway u' (cfiZeroAway u') hc) =
          cfiBaseEquiv u w hwu c) :
        cfiInvariant u₀ (insert j S) (Function.update a j c)
          (Function.update b j (response c)) := by
      refine ⟨u', (cfiSingleFlipIso hu'.symm).trans φ, hsupp' hc fun i _ hij => hother hT i hij,
        fun i hiS hi => ?_⟩
      rcases eq_or_ne i j with rfl | hij
      · rw [Function.update_self, RelIso.trans_apply,
          castAway_congr (Function.update_self i c a) hi hc]
        exact congrArg φ hnew.symm
      · have hiS' : i ∈ S := Set.mem_of_mem_insert_of_ne hiS hij
        have hui : u ∉ (a i).support := hsupp i hiS'
        rw [Function.update_of_ne hij, RelIso.trans_apply,
          castAway_congr (Function.update_of_ne hij c a) hi (hother hT i hij), hmap i hiS' hui]
        exact congrArg φ (cfiSingleFlipIso_castAway_of_notMem hu'.symm (cfiZeroAway u')
          (cfiZeroAway u) (a i) hui (hother hT i hij)).symm
    by_cases huc : u ∈ c.support
    · by_cases hwc : w ∈ c.support
      · have hw'c : w' ∉ c.support :=
          c.notMem_support_of_mem_mem_ne huc hwc hwu.symm hw'u hww'.symm
        exact moveTwist hw'u hw'T hw'c
          (cfiSingleFlipIso_castAway_eq_cfiBaseEquiv_of_mem hwu.symm hw'u.symm
            hww' (cfiZeroAway w') c huc hwc hw'c)
      · exact moveTwist hwu hwT hwc
          (cfiSingleFlipIso_castAway_eq_cfiBaseEquiv hwu.symm (cfiZeroAway w) c hwc)
    · refine ⟨u, φ, hsupp' huc fun i hiS _ => hsupp i hiS, fun i hiS hi => ?_⟩
      rcases eq_or_ne i j with rfl | hij
      · rw [Function.update_self,
          castAway_congr (Function.update_self i c a) hi huc]
        exact congrArg φ (cfiBaseEquiv_eq_castAway hwu (cfiZeroAway u) c huc)
      · have hiS' : i ∈ S := Set.mem_of_mem_insert_of_ne hiS hij
        rw [Function.update_of_ne hij,
          castAway_congr (Function.update_of_ne hij c a) hi (hsupp i hiS')]
        exact hmap i hiS' (hsupp i hiS')

end Invariant

/-! ### Bijective pebble game, counting logic, and `k`-WL on CFI graphs -/

section MainResults

/-- Whenever `2 * d + 4 ≤ m`, Duplicator wins the infinite `(d + 1)`-pebble bijective game from `∅`
between `cfiGraph m 0` and `cfiGraph m (Pi.single u₀ 1)`. -/
theorem bijPebbleWinsForever_cfiGraph_zero_single {d m : ℕ} (hm : 2 * d + 4 ≤ m) (u₀ : Fin m)
    (a : Fin (d + 1) → CFIVertex m 0) (b : Fin (d + 1) → CFIVertex m (Pi.single u₀ 1)) :
    (letI := (cfiGraph m 0).structure; letI := (cfiGraph m (Pi.single u₀ 1)).structure
      BijPebbleWinsForever Language.graph ∅ a b) := by
  let := (cfiGraph m 0).structure
  let := (cfiGraph m (Pi.single u₀ 1)).structure
  exact (isBijPebbleBackAndForth_cfiInvariant hm u₀).bijPebbleWinsForever
    ⟨u₀, SimpleGraph.Iso.refl, fun _ hi => False.elim hi, fun _ hi => False.elim hi⟩

/-- For every `d ≤ k`, Duplicator wins the infinite `(d + 1)`-pebble bijective game from `∅` between
`cfiEven k` and `cfiOdd k`. -/
theorem bijPebbleWinsForever_cfiEven_cfiOdd_of_le {d k : ℕ} (hd : d ≤ k)
    (a : Fin (d + 1) → CFIVertex (2 * k + 4) 0)
    (b : Fin (d + 1) → CFIVertex (2 * k + 4) (Pi.single 0 1)) :
    (letI := (cfiEven k).structure; letI := (cfiOdd k).structure
      BijPebbleWinsForever Language.graph ∅ a b) :=
  bijPebbleWinsForever_cfiGraph_zero_single (by omega) 0 a b

/-- **Cai–Fürer–Immerman pebble-game lower bound** ([CaiFurerImmerman1992], Section 6): Duplicator
wins the infinite `(k + 1)`-pebble bijective game from `∅` between `cfiEven k` and `cfiOdd k`. -/
theorem bijPebbleWinsForever_cfiEven_cfiOdd (k : ℕ)
    (a : Fin (k + 1) → CFIVertex (2 * k + 4) 0)
    (b : Fin (k + 1) → CFIVertex (2 * k + 4) (Pi.single 0 1)) :
    (letI := (cfiEven k).structure; letI := (cfiOdd k).structure
      BijPebbleWinsForever Language.graph ∅ a b) :=
  bijPebbleWinsForever_cfiEven_cfiOdd_of_le le_rfl a b

/-- Finite-round form of `bijPebbleWinsForever_cfiEven_cfiOdd`: Duplicator wins every `n`-round
`(k + 1)`-pebble bijective game from `∅` between `cfiEven k` and `cfiOdd k`. -/
theorem bijPebbleWins_cfiEven_cfiOdd (k n : ℕ)
    (a : Fin (k + 1) → CFIVertex (2 * k + 4) 0)
    (b : Fin (k + 1) → CFIVertex (2 * k + 4) (Pi.single 0 1)) :
    (letI := (cfiEven k).structure; letI := (cfiOdd k).structure
      BijPebbleWins Language.graph n ∅ a b) := by
  let := (cfiEven k).structure
  let := (cfiOdd k).structure
  exact (bijPebbleWinsForever_cfiEven_cfiOdd k a b).bijPebbleWins n

/-- Duplicator wins the infinite ordinary `(k + 1)`-pebble game from `∅` between `cfiEven k` and
`cfiOdd k`. -/
theorem pebbleWinsForever_cfiEven_cfiOdd (k : ℕ)
    (a : Fin (k + 1) → CFIVertex (2 * k + 4) 0)
    (b : Fin (k + 1) → CFIVertex (2 * k + 4) (Pi.single 0 1)) :
    (letI := (cfiEven k).structure; letI := (cfiOdd k).structure
      PebbleWinsForever Language.graph ∅ a b) := by
  let := (cfiEven k).structure
  let := (cfiOdd k).structure
  exact (bijPebbleWinsForever_cfiEven_cfiOdd k a b).pebbleWinsForever

/-- **Cai–Fürer–Immerman `C^{k+1}` lower bound** ([CaiFurerImmerman1992], Section 6): the
non-isomorphic graphs `cfiEven k` and `cfiOdd k` satisfy the same `(k + 1)`-variable counting
sentences. -/
theorem realize_countingFormula_cfiEven_iff_cfiOdd {k : ℕ}
    {φ : FiniteVariable.CountingFormula Language.graph (k + 1)} (hφ : φ.freeVars = ∅)
    (a : Fin (k + 1) → CFIVertex (2 * k + 4) 0)
    (b : Fin (k + 1) → CFIVertex (2 * k + 4) (Pi.single 0 1)) :
    (letI := (cfiEven k).structure; φ.Realize a) ↔
      (letI := (cfiOdd k).structure; φ.Realize b) := by
  let := (cfiEven k).structure
  let := (cfiOdd k).structure
  exact (bijPebbleWinsForever_cfiEven_cfiOdd k a b).realize_iff (by simp [hφ])

/-- The non-isomorphic graphs `cfiEven k` and `cfiOdd k` satisfy the same `(k + 1)`-variable
first-order sentences (`FO^{k+1}`). -/
theorem realize_formula_cfiEven_iff_cfiOdd {k : ℕ}
    {φ : FiniteVariable.Formula Language.graph (k + 1)} (hφ : φ.freeVars = ∅)
    (a : Fin (k + 1) → CFIVertex (2 * k + 4) 0)
    (b : Fin (k + 1) → CFIVertex (2 * k + 4) (Pi.single 0 1)) :
    (letI := (cfiEven k).structure; φ.Realize a) ↔
      (letI := (cfiOdd k).structure; φ.Realize b) := by
  let := (cfiEven k).structure
  let := (cfiOdd k).structure
  exact (pebbleWinsForever_cfiEven_cfiOdd k a b).realize_iff (by simp [hφ])

private theorem wlHistogram_cfiGraph_eq_zero {d m : ℕ} (hm : 2 * d + 4 ≤ m)
    (f : Fin m → ZMod 2) (n : ℕ) :
    (cfiGraph m f).wlHistogram d n = (cfiGraph m 0).wlHistogram d n := by
  obtain ⟨x₀⟩ := CFIVertex.nonempty_of_two_le (by omega) (0 : Fin m → ZMod 2)
  let u₀ : Fin m := ⟨0, by omega⟩
  obtain ⟨x₁⟩ := CFIVertex.nonempty_of_two_le (by omega) (Pi.single u₀ 1)
  have h01 : (cfiGraph m 0).wlHistogram d n = (cfiGraph m (Pi.single u₀ 1)).wlHistogram d n :=
    (bijPebbleWinsForever_graph_empty_iff_wlHistogram_eq (a := fun _ : Fin (d + 1) => x₀)
      (b := fun _ : Fin (d + 1) => x₁)).1
      (bijPebbleWinsForever_cfiGraph_zero_single hm u₀ _ _) n
  by_cases hsum0 : ∑ v, f v = 0
  · obtain ⟨e⟩ := (nonempty_iso_cfiGraph_iff_sum_eq (by omega)).2
      (show ∑ v, f v = ∑ v, (0 : Fin m → ZMod 2) v by simp [hsum0])
    exact (e.wlHistogram_eq d n).symm
  · obtain ⟨e⟩ := (nonempty_iso_cfiGraph_iff_sum_eq (by omega)).2
      ((Fin.eq_one_of_ne_zero _ hsum0).trans (Fintype.sum_pi_single' u₀ (1 : ZMod 2)).symm)
    exact (e.wlHistogram_eq d n).symm.trans h01.symm

/-- Whenever `2 * d + 4 ≤ m`, any two twist functions `f, g : Fin m → ZMod 2` produce CFI graphs
with identical `d`-WL histograms in every round `n`. -/
theorem wlHistogram_cfiGraph_eq {d m : ℕ} (hm : 2 * d + 4 ≤ m) (f g : Fin m → ZMod 2) (n : ℕ) :
    (cfiGraph m f).wlHistogram d n = (cfiGraph m g).wlHistogram d n :=
  (wlHistogram_cfiGraph_eq_zero hm f n).trans (wlHistogram_cfiGraph_eq_zero hm g n).symm

/-- For every `d ≤ k` and every round `n`, `cfiEven k` and `cfiOdd k` have the same `d`-WL
histogram. -/
theorem wlHistogram_cfiEven_eq_cfiOdd_of_le {d k : ℕ} (hd : d ≤ k) (n : ℕ) :
    (cfiEven k).wlHistogram d n = (cfiOdd k).wlHistogram d n :=
  wlHistogram_cfiGraph_eq (by omega) _ _ n

/-- **Cai–Fürer–Immerman `k`-WL lower bound** ([CaiFurerImmerman1992], Section 6): for every
dimension `k` and round `n`, `cfiEven k` and `cfiOdd k` have the same `k`-WL histogram while being
non-isomorphic (`SimpleGraph.not_nonempty_iso_cfiEven_cfiOdd k`). -/
theorem wlHistogram_cfiEven_eq_cfiOdd (k n : ℕ) :
    (cfiEven k).wlHistogram k n = (cfiOdd k).wlHistogram k n :=
  wlHistogram_cfiEven_eq_cfiOdd_of_le le_rfl n

/-- When `1 ≤ k`, `1`-dimensional color refinement (`SimpleGraph.colorHistogram`) agrees on
`cfiEven k` and `cfiOdd k` in every round `n`. -/
theorem colorHistogram_cfiEven_eq_cfiOdd {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (cfiEven k).colorHistogram (fun _ => ()) n = (cfiOdd k).colorHistogram (fun _ => ()) n :=
  forall_wlHistogram_one_eq_iff.1 (wlHistogram_cfiEven_eq_cfiOdd_of_le hk) n

/-- Whenever `2 * d + 4 ≤ m`, Duplicator wins the infinite `(d + 1)`-pebble bijective game from `∅`
between `cfiGraph m f` and `cfiGraph m g` for arbitrary twist functions `f, g : Fin m → ZMod 2`. -/
theorem bijPebbleWinsForever_cfiGraph_empty {d m : ℕ} (hm : 2 * d + 4 ≤ m)
    {f g : Fin m → ZMod 2} (a : Fin (d + 1) → CFIVertex m f) (b : Fin (d + 1) → CFIVertex m g) :
    (letI := (cfiGraph m f).structure; letI := (cfiGraph m g).structure
      BijPebbleWinsForever Language.graph ∅ a b) :=
  bijPebbleWinsForever_graph_empty_iff_wlHistogram_eq.2 (wlHistogram_cfiGraph_eq hm f g)

/-- Whenever `2 * d + 4 ≤ m`, `cfiGraph m f` and `cfiGraph m g` satisfy the same `C^{d+1}`
sentences for arbitrary twist functions `f, g : Fin m → ZMod 2`. -/
theorem realize_countingFormula_cfiGraph_iff {d m : ℕ} (hm : 2 * d + 4 ≤ m)
    {f g : Fin m → ZMod 2} {φ : FiniteVariable.CountingFormula Language.graph (d + 1)}
    (hφ : φ.freeVars = ∅) (a : Fin (d + 1) → CFIVertex m f) (b : Fin (d + 1) → CFIVertex m g) :
    (letI := (cfiGraph m f).structure; φ.Realize a) ↔
      (letI := (cfiGraph m g).structure; φ.Realize b) :=
  realize_countingFormula_iff_of_wlHistogram_eq (wlHistogram_cfiGraph_eq hm f g φ.quantifierRank)
    le_rfl hφ a b

/-- **Cai–Fürer–Immerman separation of `k`-WL and `C^{k+1}` from graph isomorphism.** For every
`k : ℕ`, there exist two non-isomorphic simple graphs on the same finite nonempty vertex type whose
`k`-WL histograms agree in every round and which satisfy the same `C^{k+1}` sentences. -/
theorem exists_nonisomorphic_wlHistogram_eq (k : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V) (G H : SimpleGraph V),
      IsEmpty (G ≃g H) ∧
        (∀ n, G.wlHistogram k n = H.wlHistogram k n) ∧
        ∀ φ : FiniteVariable.CountingFormula Language.graph (k + 1),
          φ.freeVars = ∅ →
            ∀ a b : Fin (k + 1) → V,
              ((letI := G.structure; φ.Realize a) ↔ (letI := H.structure; φ.Realize b)) := by
  have h10 : (⟨1, by omega⟩ : Fin (2 * k + 4)) ≠ 0 :=
    fun h => Nat.one_ne_zero (congrArg Fin.val h)
  let e : CFIVertex (2 * k + 4) 0 ≃ CFIVertex (2 * k + 4) (Pi.single 0 1) :=
    cfiBaseEquiv 0 ⟨1, by omega⟩ h10
  let H : SimpleGraph (CFIVertex (2 * k + 4) 0) := (cfiOdd k).comap e
  let φH : H ≃g cfiOdd k := { toEquiv := e, map_rel_iff' := Iff.rfl }
  have hH_wl : ∀ n, (cfiEven k).wlHistogram k n = H.wlHistogram k n :=
    fun n => (wlHistogram_cfiEven_eq_cfiOdd k n).trans (φH.wlHistogram_eq k n)
  exact ⟨CFIVertex (2 * k + 4) 0, inferInstance, inferInstance, cfiEven k, H,
    ⟨fun ψ => (isEmpty_iso_cfiEven_cfiOdd k).false (ψ.trans φH)⟩, hH_wl,
    forall_realize_countingFormula_empty_iff_wlHistogram_eq.2 hH_wl⟩

end MainResults

end Cslib.Logic.FO
