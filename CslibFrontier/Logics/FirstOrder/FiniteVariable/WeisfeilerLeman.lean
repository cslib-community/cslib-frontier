/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.WeisfeilerLeman
public import CslibFrontier.Foundations.ModelTheory.Graph
public import CslibFrontier.Logics.FirstOrder.FiniteVariable.BijectiveGame
import CslibFrontier.Foundations.Data.Fintype.FiberEquiv
import CslibFrontier.Logics.FirstOrder.FiniteVariable.ColorRefinement
import CslibFrontier.Logics.FirstOrder.FiniteVariable.CountingHintikka
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Tactic.FinCases

/-!
# The Cai–Fürer–Immerman equivalence: `k`-WL and `C^{k+1}`

On finite simple graphs, `k`-dimensional Weisfeiler–Leman (`SimpleGraph.wlColoring`,
`SimpleGraph.wlHistogram`) characterizes equivalence in the `(k + 1)`-variable counting logic
`C^{k+1}` (`Cslib.Logic.FO.FiniteVariable.CountingFormula Language.graph (k + 1)`) via Hella's
bijective `(k + 1)`-pebble game ([CaiFurerImmerman1992], Section 5, Theorem 5.2).

* **Tuple equivalence (`k` free variables).** Placing a `k`-tuple `u : Fin k → V` on the first `k`
  pebbles `Set.range Fin.castSucc ⊆ Fin (k + 1)` leaves pebble `Fin.last k` as the auxiliary pebble
  used to scan vertices `v : V`. When all `k + 1` pebbles are placed (`Fin.snoc u v`), moving pebble
  `i.castSucc` is related by `Equiv.swap i.castSucc (Fin.last k)` (`bijPebbleWins_comp_equiv_iff`)
  to moving `Fin.last k` from `Function.update u i v`. Consequently, Duplicator wins the `n`-round
  bijective `(k + 1)`-pebble game from `(Set.range Fin.castSucc, Fin.snoc u v₀, Fin.snoc w w₀)` if
  and only if `G.wlColoring n u = H.wlColoring n w` (`bijPebbleWins_graph_range_castSucc_iff`), with
  no round shift and for every `k : ℕ`. Through `bijPebbleWins_iff_forall_realize_iff`, `u` and `w`
  have the same round-`n` `k`-WL color iff they satisfy the same `C^{k+1}` formulas of quantifier
  rank at most `n` in the first `k` variables (`forall_realize_countingFormula_castSucc_le_iff`),
  and across all quantifier ranks iff their colors agree in round `|V| ^ k + |W| ^ k`
  (`forall_realize_countingFormula_castSucc_iff_card_pow_add`).
* **Sentence equivalence (`freeVars = ∅`).** Equal round-`n` `k`-WL histograms allow matching any
  chosen `k`-tuple of `G` with one of `H` of the same color and lifting the pebbles, giving a win in
  the `n`-round game from `∅` (`bijPebbleWins_graph_empty_of_wlHistogram_eq`). Conversely, winning
  `n + k` rounds from `∅` places `k` pebbles fiberwise to build a color-preserving bijection
  `(Fin k → V) ≃ (Fin k → W)` (`wlHistogram_eq_of_bijPebbleWins_graph_empty`). Over all rounds, two
  nonempty finite graphs satisfy the same `C^{k+1}` sentences iff their `k`-WL histograms agree in
  every round (`forall_realize_countingFormula_empty_iff_wlHistogram_eq`), iff they agree in round
  `|V| ^ k + |W| ^ k` (`forall_realize_countingFormula_empty_iff_wlHistogram_card_pow_add`).
* **Compatibility at `k = 1`.** Specializing `k = 1` recovers the Immerman–Lander vertex and
  histogram characterizations in terms of `SimpleGraph.refinementColoring` and
  `SimpleGraph.colorHistogram` (`wlColoring_one_succ_eq_iff`, `forall_wlColoring_one_eq_iff`,
  `forall_wlHistogram_one_eq_iff`).

## Main results

* `Cslib.Logic.FO.partialIsoOn_graph_univ_iff_tupleAtom`,
  `Cslib.Logic.FO.partialIsoOn_graph_range_castSucc_iff_tupleAtom`: partial isomorphisms on simple
  graphs vs `SimpleGraph.tupleAtom`.
* `Cslib.Logic.FO.bijPebbleWins_graph_univ_snoc_iff`,
  `Cslib.Logic.FO.bijPebbleWins_graph_range_castSucc_iff`,
  `Cslib.Logic.FO.bijPebbleWinsForever_graph_range_castSucc_iff`: round-by-round and infinite-game
  equivalences between `k`-WL tuple colors and the bijective `(k + 1)`-pebble game.
* `Cslib.Logic.FO.bijPebbleWins_graph_empty_of_wlHistogram_eq`,
  `Cslib.Logic.FO.wlHistogram_eq_of_bijPebbleWins_graph_empty`,
  `Cslib.Logic.FO.bijPebbleWinsForever_graph_empty_iff_wlHistogram_eq`: `k`-WL histograms and the
  bijective `(k + 1)`-pebble game from `∅`.
* `Cslib.Logic.FO.forall_realize_countingFormula_castSucc_le_iff`,
  `Cslib.Logic.FO.forall_realize_countingFormula_castSucc_iff`,
  `Cslib.Logic.FO.forall_realize_countingFormula_castSucc_iff_card_pow_add`: **Cai–Fürer–Immerman
  theorem, tuple form** (`C^{k+1}` formulas in `k` free variables vs `k`-WL colors).
* `Cslib.Logic.FO.realize_countingFormula_le_one_iff_of_card_eq`,
  `Cslib.Logic.FO.realize_countingFormula_iff_of_wlHistogram_eq`,
  `Cslib.Logic.FO.wlHistogram_eq_of_forall_realize_countingFormula_empty_le`,
  `Cslib.Logic.FO.forall_realize_countingFormula_empty_iff_wlHistogram_eq`,
  `Cslib.Logic.FO.forall_realize_countingFormula_empty_iff_wlHistogram_card_pow_add`:
  **Cai–Fürer–Immerman theorem, sentence form** (`C^{k+1}` sentences vs `k`-WL histograms).
* `Cslib.Logic.FO.wlColoring_one_succ_eq_iff`, `Cslib.Logic.FO.forall_wlColoring_one_eq_iff`,
  `Cslib.Logic.FO.forall_wlHistogram_one_eq_iff`: compatibility of `1`-WL with
  `SimpleGraph.refinementColoring` and `SimpleGraph.colorHistogram`.

## References

* [J.-Y. Cai, M. Fürer, N. Immerman, *An optimal lower bound on the number of variables for graph
  identification*][CaiFurerImmerman1992], Section 5, Theorem 5.2.
-/

public section

open FirstOrder Language Structure SimpleGraph

namespace Cslib.Logic.FO

section GraphPartialIso

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- When all pebbles are placed, a partial isomorphism on simple graphs is equality of
`SimpleGraph.tupleAtom`. -/
theorem partialIsoOn_graph_univ_iff_tupleAtom {m : ℕ} {a : Fin m → V} {b : Fin m → W} :
    (letI := G.structure; letI := H.structure; PartialIsoOn Language.graph Set.univ a b) ↔
      G.tupleAtom a = H.tupleAtom b := by
  rw [partialIsoOn_graph_iff, tupleAtom_eq_iff]
  simp only [Set.mem_univ, forall_const]

/-- On `Set.range Fin.castSucc`, a partial isomorphism between `Fin.snoc u v₀` and `Fin.snoc w w₀`
is equality of `SimpleGraph.tupleAtom` on `u` and `w`. -/
theorem partialIsoOn_graph_range_castSucc_iff_tupleAtom {k : ℕ} {u : Fin k → V} {w : Fin k → W}
    {v₀ : V} {w₀ : W} :
    (letI := G.structure; letI := H.structure
      PartialIsoOn Language.graph (Set.range Fin.castSucc) (Fin.snoc u v₀) (Fin.snoc w w₀)) ↔
      G.tupleAtom u = H.tupleAtom w := by
  rw [partialIsoOn_graph_iff, tupleAtom_eq_iff]
  simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, Fin.snoc_castSucc]

end GraphPartialIso

/-! ### Tuple and pebble index combinatorics -/

section TupleHelpers

private theorem insert_last_range_castSucc (k : ℕ) :
    insert (Fin.last k) (Set.range (Fin.castSucc : Fin k → Fin (k + 1))) = Set.univ := by
  ext j
  simp only [Set.mem_insert_iff, Set.mem_range, Set.mem_univ, iff_true]
  exact Fin.lastCases (Or.inl rfl) (fun i => Or.inr ⟨i, rfl⟩) j

private theorem insert_castSucc_range_castSucc {k : ℕ} (i : Fin k) :
    insert i.castSucc (Set.range (Fin.castSucc : Fin k → Fin (k + 1))) =
      Set.range Fin.castSucc :=
  Set.insert_eq_of_mem ⟨i, rfl⟩

private theorem snoc_comp_swap_castSucc_last {α : Type*} {k : ℕ} (u : Fin k → α) (v : α)
    (i : Fin k) :
    Fin.snoc u v ∘ Equiv.swap i.castSucc (Fin.last k) =
      Fin.snoc (Function.update u i v) (u i) := by
  ext j
  refine Fin.lastCases (by simp) (fun r => ?_) j
  rcases eq_or_ne r i with rfl | hri
  · simp
  · simp [Equiv.swap_apply_of_ne_of_ne ((Fin.castSucc_injective k).ne hri) r.castSucc_ne_last, hri]

private theorem update_snoc_castSucc_comp_swap {α : Type*} {k : ℕ} (u : Fin k → α) (v c : α)
    (i : Fin k) :
    Function.update (Fin.snoc u v) i.castSucc c ∘ Equiv.swap i.castSucc (Fin.last k) =
      Fin.snoc (Function.update u i v) c := by
  rw [← Fin.snoc_update, snoc_comp_swap_castSucc_last, Function.update_idem, Function.update_self]

end TupleHelpers

/-! ### Bijective `(k + 1)`-pebble game and `k`-WL -/

section GameEquiv

variable {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ}

private theorem exists_equiv_stepProfile_iff (v₀ : V) (n : ℕ) (u : Fin k → V) (w : Fin k → W) :
    (∃ f : V ≃ W, ∀ c,
      G.wlColoring n u = H.wlColoring n w ∧
        G.wlStepProfile (G.wlColoring n) u c = H.wlStepProfile (H.wlColoring n) w (f c)) ↔
      G.wlColoring (n + 1) u = H.wlColoring (n + 1) w := by
  rw [wlColoring_succ_eq_iff, ← Equiv.exists_apply_eq_iff_map_univ_eq]
  exact ⟨fun ⟨f, hf⟩ => ⟨(hf v₀).1, f, fun c => (hf c).2.symm⟩,
    fun ⟨huw, f, hf⟩ => ⟨f, fun c => ⟨huw, (hf c).symm⟩⟩⟩

/-- With all `k + 1` pebbles placed on `Fin.snoc u v` and `Fin.snoc w z`, Duplicator wins the
`n`-round bijective game iff `u` and `w` have the same round-`n` `k`-WL color and `(u, v)` and
`(w, z)` have the same round-`n` step profile. -/
theorem bijPebbleWins_graph_univ_snoc_iff (n : ℕ) (u : Fin k → V) (w : Fin k → W) (v : V)
    (z : W) :
    (letI := G.structure; letI := H.structure
      BijPebbleWins Language.graph n Set.univ (Fin.snoc u v) (Fin.snoc w z)) ↔
      G.wlColoring n u = H.wlColoring n w ∧
        G.wlStepProfile (G.wlColoring n) u v = H.wlStepProfile (H.wlColoring n) w z := by
  let := G.structure; let := H.structure
  induction n generalizing u w v z with
  | zero =>
    rw [bijPebbleWins_zero, partialIsoOn_graph_univ_iff_tupleAtom, wlStepProfile_eq_iff,
      wlColoring_zero, wlColoring_zero]
    refine ⟨fun hatom => ⟨?_, hatom, fun i => ?_⟩, fun ⟨_, hatom, _⟩ => hatom⟩
    · exact (show G.tupleAtom u = H.tupleAtom w by
        simpa only [Fin.snoc_comp_castSucc] using tupleAtom_comp_eq hatom Fin.castSucc)
    · have hswap := tupleAtom_comp_eq hatom (Equiv.swap i.castSucc (Fin.last k) ∘ Fin.castSucc)
      rwa [← Function.comp_assoc, ← Function.comp_assoc, snoc_comp_swap_castSucc_last,
        snoc_comp_swap_castSucc_last, Fin.snoc_comp_castSucc, Fin.snoc_comp_castSucc] at hswap
  | succ n ih =>
    have hreidx (i : Fin k) (c : V) (d : W) :
        BijPebbleWins Language.graph n Set.univ (Function.update (Fin.snoc u v) i.castSucc c)
          (Function.update (Fin.snoc w z) i.castSucc d) ↔
        BijPebbleWins Language.graph n Set.univ (Fin.snoc (Function.update u i v) c)
          (Fin.snoc (Function.update w i z) d) := by
      rw [← bijPebbleWins_comp_equiv_iff (Equiv.swap i.castSucc (Fin.last k)), Set.preimage_univ,
        update_snoc_castSucc_comp_swap, update_snoc_castSucc_comp_swap]
    rw [bijPebbleWins_succ, partialIsoOn_graph_univ_iff_tupleAtom, Fin.forall_iff_castSucc]
    simp only [Set.insert_eq_of_mem (Set.mem_univ _), Fin.update_snoc_last, hreidx, ih,
      exists_equiv_stepProfile_iff v]
    simp only [wlStepProfile_eq_iff]
    tauto

/-- **Bijective `(k + 1)`-pebble game and `k`-WL tuple colors.** With the first `k` pebbles placed
on `u : Fin k → V` and `w : Fin k → W`, Duplicator wins the `n`-round bijective `(k + 1)`-pebble
game on simple graphs if and only if `u` and `w` receive the same `k`-WL color in round `n`. -/
theorem bijPebbleWins_graph_range_castSucc_iff (n : ℕ) (u : Fin k → V) (w : Fin k → W)
    (v₀ : V) (w₀ : W) :
    (letI := G.structure; letI := H.structure
      BijPebbleWins Language.graph n (Set.range Fin.castSucc)
        (Fin.snoc u v₀) (Fin.snoc w w₀)) ↔
      G.wlColoring n u = H.wlColoring n w := by
  let := G.structure; let := H.structure
  induction n generalizing u w with
  | zero =>
    rw [bijPebbleWins_zero, partialIsoOn_graph_range_castSucc_iff_tupleAtom, wlColoring_zero,
      wlColoring_zero]
    exact Iff.rfl
  | succ n ih =>
    rw [bijPebbleWins_succ, partialIsoOn_graph_range_castSucc_iff_tupleAtom,
      Fin.forall_iff_castSucc]
    simp only [insert_last_range_castSucc, Fin.update_snoc_last, bijPebbleWins_graph_univ_snoc_iff,
      exists_equiv_stepProfile_iff v₀ n u w, insert_castSucc_range_castSucc, ← Fin.snoc_update, ih]
    refine ⟨fun ⟨_, hlast, _⟩ => hlast, fun hcol => ?_⟩
    obtain ⟨_, hmset⟩ := wlColoring_succ_eq_iff.1 hcol
    obtain ⟨f, hf⟩ := Equiv.exists_apply_eq_iff_map_univ_eq.2 hmset
    refine ⟨?_, hcol, fun i => ⟨f, fun c => (wlStepProfile_eq_iff.1 (hf c).symm).2 i⟩⟩
    rw [← wlColoring_zero, ← wlColoring_zero]
    exact wlColoring_eq_of_le (Nat.zero_le (n + 1)) hcol

/-- Duplicator wins the infinite bijective `(k + 1)`-pebble game from `(Set.range Fin.castSucc,
Fin.snoc u v₀, Fin.snoc w w₀)` if and only if `u` and `w` receive the same `k`-WL color in every
round. -/
theorem bijPebbleWinsForever_graph_range_castSucc_iff {u : Fin k → V} {w : Fin k → W}
    {v₀ : V} {w₀ : W} :
    (letI := G.structure; letI := H.structure
      BijPebbleWinsForever Language.graph (Set.range Fin.castSucc)
        (Fin.snoc u v₀) (Fin.snoc w w₀)) ↔
      ∀ n, G.wlColoring n u = H.wlColoring n w := by
  let := G.structure; let := H.structure
  exact bijPebbleWinsForever_iff_forall_bijPebbleWins.trans
    (forall_congr' fun n => bijPebbleWins_graph_range_castSucc_iff n u w v₀ w₀)

/-! ### Prefix placement and `k`-WL histograms -/

private def prefixPebbles (k m : ℕ) : Set (Fin (k + 1)) :=
  {j : Fin (k + 1) | j.val < m}

private def extendPrefix {α : Type*} (k : ℕ) {m : ℕ} (t : Fin m → α) (a₀ : α) :
    Fin (k + 1) → α :=
  fun j => if hj : j.val < m then t ⟨j.val, hj⟩ else a₀

private def snocCongrEquiv {α β : Type*} {m : ℕ} (F : (Fin m → α) ≃ (Fin m → β))
    (g : (Fin m → α) → (α ≃ β)) : (Fin (m + 1) → α) ≃ (Fin (m + 1) → β) where
  toFun t := Fin.snoc (F (Fin.init t)) (g (Fin.init t) (t (Fin.last m)))
  invFun s := Fin.snoc (F.symm (Fin.init s)) ((g (F.symm (Fin.init s))).symm (s (Fin.last m)))
  left_inv t := by
    simp only [Fin.init_snoc, Fin.snoc_last, F.symm_apply_apply, Equiv.symm_apply_apply,
      Fin.snoc_init_self]
  right_inv s := by
    simp only [Fin.init_snoc, Fin.snoc_last, F.apply_symm_apply, Equiv.apply_symm_apply,
      Fin.snoc_init_self]

private theorem prefixPebbles_zero (k : ℕ) : prefixPebbles k 0 = ∅ := by
  ext j
  simp only [prefixPebbles, Set.mem_ofPred_eq, Nat.not_lt_zero, Set.mem_empty_iff_false]

private theorem prefixPebbles_self (k : ℕ) :
    prefixPebbles k k = Set.range (Fin.castSucc : Fin k → Fin (k + 1)) := by
  ext j
  simp only [prefixPebbles, Set.mem_ofPred_eq, Set.mem_range]
  refine Fin.lastCases ?_ (fun i => iff_of_true i.isLt ⟨i, rfl⟩) j
  simp [Fin.castSucc_ne_last]

private theorem insert_prefixPebbles {k m : ℕ} (hm : m < k) :
    insert (⟨m, by omega⟩ : Fin (k + 1)) (prefixPebbles k m) = prefixPebbles k (m + 1) := by
  ext j
  simp only [Set.mem_insert_iff, prefixPebbles, Set.mem_ofPred_eq, Fin.ext_iff]
  omega

private theorem extendPrefix_self {α : Type*} {k : ℕ} (u : Fin k → α) (a₀ : α) :
    extendPrefix k u a₀ = Fin.snoc u a₀ := by
  ext j
  refine Fin.lastCases ?_ ?_ j
  · simp only [extendPrefix, Fin.val_last, lt_self_iff_false, ↓reduceDIte, Fin.snoc_last]
  · intro i
    simp only [extendPrefix, Fin.val_castSucc, i.isLt, ↓reduceDIte, Fin.eta, Fin.snoc_castSucc]

private theorem eqOn_update_extendPrefix {α : Type*} {k m : ℕ} (hm : m < k) (t : Fin m → α)
    (a₀ c : α) :
    Set.EqOn (Function.update (extendPrefix k t a₀) ⟨m, Nat.lt_succ_of_lt hm⟩ c)
      (extendPrefix k (Fin.snoc t c) a₀) (prefixPebbles k (m + 1)) := by
  intro j hj
  simp only [prefixPebbles, Set.mem_ofPred_eq] at hj
  by_cases hjm : j.val = m
  · have hj_eq : j = ⟨m, Nat.lt_succ_of_lt hm⟩ := Fin.ext hjm
    rw [hj_eq]
    simp only [Function.update_self, extendPrefix, Nat.lt_succ_self, ↓reduceDIte]
    change c = (Fin.snoc t c : Fin (m + 1) → α) (Fin.last m)
    rw [Fin.snoc_last]
  · have hne : j ≠ ⟨m, Nat.lt_succ_of_lt hm⟩ := fun h => hjm (congrArg Fin.val h)
    have hlt : j.val < m := by omega
    simp only [Function.update_of_ne hne, extendPrefix, hlt, hj, ↓reduceDIte]
    change t ⟨j.val, hlt⟩ = (Fin.snoc t c : Fin (m + 1) → α) (⟨j.val, hlt⟩ : Fin m).castSucc
    rw [Fin.snoc_castSucc]

/-- If `G` and `H` have the same round-`n` `k`-WL histogram, then Duplicator wins the `n`-round
bijective `(k + 1)`-pebble game from `∅`. -/
theorem bijPebbleWins_graph_empty_of_wlHistogram_eq {n : ℕ}
    (h : G.wlHistogram k n = H.wlHistogram k n) (a : Fin (k + 1) → V) (b : Fin (k + 1) → W) :
    (letI := G.structure; letI := H.structure; BijPebbleWins Language.graph n ∅ a b) := by
  let u₀ : Fin k → V := fun _ => a 0
  obtain ⟨w₀, hw₀⟩ := mem_wlHistogram.1 (h ▸ mem_wlHistogram.2 ⟨u₀, rfl⟩ :
    G.wlColoring n u₀ ∈ H.wlHistogram k n)
  have hcast := (bijPebbleWins_graph_range_castSucc_iff n u₀ w₀ (a 0) (b 0)).2 hw₀.symm
  let := G.structure
  let := H.structure
  exact bijPebbleWins_congr (Set.eqOn_empty _ _) (Set.eqOn_empty _ _)
    (hcast.of_subset (Set.empty_subset _))

/-- If Duplicator wins `n + k` rounds of the bijective `(k + 1)`-pebble game from `∅`, then `G` and
`H` have the same round-`n` `k`-WL histogram. -/
theorem wlHistogram_eq_of_bijPebbleWins_graph_empty {n : ℕ} {a : Fin (k + 1) → V}
    {b : Fin (k + 1) → W}
    (h : (letI := G.structure; letI := H.structure
      BijPebbleWins Language.graph (n + k) ∅ a b)) :
    G.wlHistogram k n = H.wlHistogram k n := by
  let := G.structure
  let := H.structure
  have hprefix : ∀ m ≤ k, ∃ F : (Fin m → V) ≃ (Fin m → W), ∀ t : Fin m → V,
      BijPebbleWins Language.graph (n + (k - m)) (prefixPebbles k m)
        (extendPrefix k t (a 0)) (extendPrefix k (F t) (b 0)) := by
    intro m hm
    induction m with
    | zero =>
      refine ⟨Equiv.ofUnique _ _, fun t => ?_⟩
      rw [Nat.sub_zero, prefixPebbles_zero]
      exact bijPebbleWins_congr (Set.eqOn_empty _ _) (Set.eqOn_empty _ _) h
    | succ m ih =>
      obtain ⟨F, hF⟩ := ih (Nat.le_of_succ_le hm)
      have hm_lt : m < k := hm
      have hmove : ∀ t : Fin m → V, ∃ f : V ≃ W, ∀ c : V,
          BijPebbleWins Language.graph (n + (k - (m + 1))) (prefixPebbles k (m + 1))
            (extendPrefix k (Fin.snoc t c) (a 0))
            (extendPrefix k (Fin.snoc (F t) (f c)) (b 0)) := by
        intro t
        have ht := hF t
        rw [show n + (k - m) = n + (k - (m + 1)) + 1 by omega] at ht
        obtain ⟨f, hf⟩ := ht.move ⟨m, by omega⟩
        refine ⟨f, fun c => bijPebbleWins_congr (eqOn_update_extendPrefix hm_lt t (a 0) c)
          (eqOn_update_extendPrefix hm_lt (F t) (b 0) (f c)) ?_⟩
        rw [← insert_prefixPebbles hm_lt]
        exact hf c
      choose g hg using hmove
      refine ⟨snocCongrEquiv F g, fun t' => ?_⟩
      have ht' := hg (Fin.init t') (t' (Fin.last m))
      rwa [Fin.snoc_init_self] at ht'
  obtain ⟨F, hF⟩ := hprefix k le_rfl
  rw [wlHistogram_eq, wlHistogram_eq]
  refine Equiv.exists_apply_eq_iff_map_univ_eq.1
    ⟨F, fun u => ((bijPebbleWins_graph_range_castSucc_iff n u (F u) (a 0) (b 0)).1 ?_).symm⟩
  simpa only [Nat.sub_self, Nat.add_zero, prefixPebbles_self, extendPrefix_self] using hF u

/-- With no pebbles placed, Duplicator wins the infinite bijective `(k + 1)`-pebble game on simple
graphs if and only if their `k`-WL histograms agree in every round. -/
theorem bijPebbleWinsForever_graph_empty_iff_wlHistogram_eq {a : Fin (k + 1) → V}
    {b : Fin (k + 1) → W} :
    (letI := G.structure; letI := H.structure
      BijPebbleWinsForever Language.graph ∅ a b) ↔
      ∀ n, G.wlHistogram k n = H.wlHistogram k n := by
  let := G.structure; let := H.structure
  rw [bijPebbleWinsForever_iff_forall_bijPebbleWins]
  exact ⟨fun h n => wlHistogram_eq_of_bijPebbleWins_graph_empty (h (n + k)),
    fun h n => bijPebbleWins_graph_empty_of_wlHistogram_eq (h n) a b⟩

end GameEquiv

/-! ### The Cai–Fürer–Immerman theorem (`k`-WL and `C^{k+1}`) -/

section CaiFurerImmerman

variable {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ}

/-- **Cai–Fürer–Immerman theorem, bounded-rank tuple form** ([CaiFurerImmerman1992], Section 5,
Theorem 5.2). Two `k`-tuples `u` of `G` and `w` of `H` satisfy the same `C^{k+1}` formulas of
quantifier rank at most `n` in the first `k` variables `Set.range Fin.castSucc` if and only if
`u` and `w` receive the same `k`-WL color in round `n`. -/
theorem forall_realize_countingFormula_castSucc_le_iff {n : ℕ} {u : Fin k → V} {w : Fin k → W}
    {v₀ : V} {w₀ : W} :
    (∀ φ : FiniteVariable.CountingFormula Language.graph (k + 1),
      φ.quantifierRank ≤ n → ↑φ.freeVars ⊆ Set.range (Fin.castSucc : Fin k → Fin (k + 1)) →
        ((letI := G.structure; φ.Realize (Fin.snoc u v₀)) ↔
          (letI := H.structure; φ.Realize (Fin.snoc w w₀)))) ↔
      G.wlColoring n u = H.wlColoring n w := by
  let := G.structure; let := H.structure
  rw [← bijPebbleWins_iff_forall_realize_iff, bijPebbleWins_graph_range_castSucc_iff]

/-- **Cai–Fürer–Immerman theorem, tuple form** ([CaiFurerImmerman1992], Section 5, Theorem 5.2).
Two `k`-tuples `u` of `G` and `w` of `H` satisfy the same `C^{k+1}` formulas in the first `k`
variables if and only if they receive the same `k`-WL color in every round. -/
theorem forall_realize_countingFormula_castSucc_iff {u : Fin k → V} {w : Fin k → W}
    {v₀ : V} {w₀ : W} :
    (∀ φ : FiniteVariable.CountingFormula Language.graph (k + 1),
      ↑φ.freeVars ⊆ Set.range (Fin.castSucc : Fin k → Fin (k + 1)) →
        ((letI := G.structure; φ.Realize (Fin.snoc u v₀)) ↔
          (letI := H.structure; φ.Realize (Fin.snoc w w₀)))) ↔
      ∀ n, G.wlColoring n u = H.wlColoring n w := by
  let := G.structure; let := H.structure
  rw [← bijPebbleWinsForever_iff_forall_realize_iff, bijPebbleWinsForever_graph_range_castSucc_iff]

/-- **Cai–Fürer–Immerman theorem, stabilized tuple form.** Two `k`-tuples `u` of `G` and `w` of `H`
satisfy the same `C^{k+1}` formulas in the first `k` variables if and only if they receive the same
`k`-WL color in round `|V| ^ k + |W| ^ k`. -/
theorem forall_realize_countingFormula_castSucc_iff_card_pow_add {u : Fin k → V} {w : Fin k → W}
    {v₀ : V} {w₀ : W} :
    (∀ φ : FiniteVariable.CountingFormula Language.graph (k + 1),
      ↑φ.freeVars ⊆ Set.range (Fin.castSucc : Fin k → Fin (k + 1)) →
        ((letI := G.structure; φ.Realize (Fin.snoc u v₀)) ↔
          (letI := H.structure; φ.Realize (Fin.snoc w w₀)))) ↔
      G.wlColoring (Fintype.card V ^ k + Fintype.card W ^ k) u =
        H.wlColoring (Fintype.card V ^ k + Fintype.card W ^ k) w := by
  rw [forall_realize_countingFormula_castSucc_iff, forall_wlColoring_eq_iff]

/-- Any two finite simple graphs of equal vertex count agree on all `C^{k+1}` sentences of
quantifier rank at most `1`, because every singleton placement on loopless graphs is a partial
isomorphism. -/
theorem realize_countingFormula_le_one_iff_of_card_eq (h : Fintype.card V = Fintype.card W)
    {φ : FiniteVariable.CountingFormula Language.graph (k + 1)}
    (hr : φ.quantifierRank ≤ 1) (hφ : φ.freeVars = ∅)
    (a : Fin (k + 1) → V) (b : Fin (k + 1) → W) :
    (letI := G.structure; φ.Realize a) ↔ (letI := H.structure; φ.Realize b) := by
  let := G.structure; let := H.structure
  have hwin : BijPebbleWins Language.graph 1 ∅ a b := by
    rw [bijPebbleWins_succ]
    refine ⟨partialIsoOn_empty a b, fun j => ⟨Fintype.equivOfCardEq h, fun c => ?_⟩⟩
    rw [bijPebbleWins_zero]
    exact partialIsoOn_graph_iff.2 fun x hx y hy => by
      simp only [Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at hx hy
      subst hx hy
      simp only [Function.update_self]
      exact ⟨trivial, iff_of_false G.irrefl H.irrefl⟩
  exact hwin.realize_iff hr (by simp only [hφ, Finset.coe_empty, Set.empty_subset])

/-- If `G` and `H` have the same round-`n` `k`-WL histogram, then they agree on every `C^{k+1}`
sentence of quantifier rank at most `n` under any assignments. -/
theorem realize_countingFormula_iff_of_wlHistogram_eq {n : ℕ}
    (h : G.wlHistogram k n = H.wlHistogram k n)
    {φ : FiniteVariable.CountingFormula Language.graph (k + 1)}
    (hr : φ.quantifierRank ≤ n) (hφ : φ.freeVars = ∅)
    (a : Fin (k + 1) → V) (b : Fin (k + 1) → W) :
    (letI := G.structure; φ.Realize a) ↔ (letI := H.structure; φ.Realize b) := by
  let := G.structure; let := H.structure
  exact (bijPebbleWins_graph_empty_of_wlHistogram_eq h a b).realize_iff hr
    (by simp only [hφ, Finset.coe_empty, Set.empty_subset])

/-- If two nonempty finite simple graphs agree on all `C^{k+1}` sentences of quantifier rank at most
`n + k`, then their round-`n` `k`-WL histograms agree. -/
theorem wlHistogram_eq_of_forall_realize_countingFormula_empty_le [Nonempty V] [Nonempty W]
    {n : ℕ}
    (h : ∀ φ : FiniteVariable.CountingFormula Language.graph (k + 1),
      φ.quantifierRank ≤ n + k → φ.freeVars = ∅ →
        ∀ (a : Fin (k + 1) → V) (b : Fin (k + 1) → W),
          ((letI := G.structure; φ.Realize a) ↔ (letI := H.structure; φ.Realize b))) :
    G.wlHistogram k n = H.wlHistogram k n := by
  obtain ⟨v₀⟩ := ‹Nonempty V›
  obtain ⟨w₀⟩ := ‹Nonempty W›
  let a : Fin (k + 1) → V := fun _ => v₀
  let b : Fin (k + 1) → W := fun _ => w₀
  refine wlHistogram_eq_of_bijPebbleWins_graph_empty (a := a) (b := b) ?_
  let := G.structure
  let := H.structure
  exact bijPebbleWins_of_forall_realize_iff fun φ hr hS =>
    h φ hr (Finset.coe_eq_empty.1 (Set.Subset.antisymm hS (Set.empty_subset _))) a b

/-- **Cai–Fürer–Immerman theorem, sentence form** ([CaiFurerImmerman1992], Section 5, Theorem 5.2).
Two nonempty finite simple graphs satisfy the same `C^{k+1}` sentences if and only if their `k`-WL
histograms agree in every round. Nonemptiness is needed because `GenFormula.Realize` takes a
total assignment `Fin (k + 1) → V`, which does not exist when `V` or `W` is empty. -/
theorem forall_realize_countingFormula_empty_iff_wlHistogram_eq [Nonempty V] [Nonempty W] :
    (∀ φ : FiniteVariable.CountingFormula Language.graph (k + 1),
      φ.freeVars = ∅ →
        ∀ (a : Fin (k + 1) → V) (b : Fin (k + 1) → W),
          ((letI := G.structure; φ.Realize a) ↔ (letI := H.structure; φ.Realize b))) ↔
      ∀ n, G.wlHistogram k n = H.wlHistogram k n := by
  refine ⟨fun h n => wlHistogram_eq_of_forall_realize_countingFormula_empty_le
    (fun φ _ hφ => h φ hφ),
    fun h φ hφ a b => realize_countingFormula_iff_of_wlHistogram_eq (h φ.quantifierRank)
      le_rfl hφ a b⟩

/-- **Cai–Fürer–Immerman theorem, stabilized sentence form.** Two nonempty finite simple graphs
satisfy the same `C^{k+1}` sentences if and only if their `k`-WL histograms agree in round
`|V| ^ k + |W| ^ k`. -/
theorem forall_realize_countingFormula_empty_iff_wlHistogram_card_pow_add
    [Nonempty V] [Nonempty W] :
    (∀ φ : FiniteVariable.CountingFormula Language.graph (k + 1),
      φ.freeVars = ∅ →
        ∀ (a : Fin (k + 1) → V) (b : Fin (k + 1) → W),
          ((letI := G.structure; φ.Realize a) ↔ (letI := H.structure; φ.Realize b))) ↔
      G.wlHistogram k (Fintype.card V ^ k + Fintype.card W ^ k) =
        H.wlHistogram k (Fintype.card V ^ k + Fintype.card W ^ k) := by
  rw [forall_realize_countingFormula_empty_iff_wlHistogram_eq, forall_wlHistogram_eq_iff]

end CaiFurerImmerman

/-! ### Compatibility of `1`-WL with `SimpleGraph.refinementColoring` -/

section OneDimensional

variable {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} [G.LocallyFinite]
  {H : SimpleGraph W} [H.LocallyFinite]

private theorem range_castSucc_one :
    Set.range (Fin.castSucc : Fin 1 → Fin 2) = ({0} : Set (Fin 2)) := by
  ext j
  fin_cases j <;> simp

private theorem snoc_singleton {α : Type*} (v : α) :
    Fin.snoc (![v] : Fin 1 → α) v = fun _ : Fin 2 => v := by
  ext j
  fin_cases j <;> rfl

/-- At dimension `k = 1`, round `n + 1` of `1`-WL agrees on `![v]` and `![w]` if and only if `v` and
`w` have the same round-`(n + 1)` vertex refinement color and `G` and `H` have the same round-`n`
vertex color histogram. -/
theorem wlColoring_one_succ_eq_iff {n : ℕ} {v : V} {w : W} :
    G.wlColoring (n + 1) ![v] = H.wlColoring (n + 1) ![w] ↔
      G.refinementColoring (fun _ => ()) (n + 1) v =
          H.refinementColoring (fun _ => ()) (n + 1) w ∧
        G.colorHistogram (fun _ => ()) n = H.colorHistogram (fun _ => ()) n := by
  rw [← bijPebbleWins_graph_range_castSucc_iff (n + 1) ![v] ![w] v w, range_castSucc_one,
    snoc_singleton, snoc_singleton, bijPebbleWins_graph_singleton_iff]

/-- At dimension `k = 1`, `![v]` and `![w]` receive the same `1`-WL color in every round if and only
if `v` and `w` receive the same vertex refinement color in every round and `G` and `H` have the same
vertex color histogram in every round. -/
theorem forall_wlColoring_one_eq_iff {v : V} {w : W} :
    (∀ n, G.wlColoring n ![v] = H.wlColoring n ![w]) ↔
      (∀ n, G.refinementColoring (fun _ => ()) n v =
          H.refinementColoring (fun _ => ()) n w) ∧
        ∀ n, G.colorHistogram (fun _ => ()) n = H.colorHistogram (fun _ => ()) n := by
  rw [← bijPebbleWinsForever_graph_range_castSucc_iff (v₀ := v) (w₀ := w), range_castSucc_one,
    snoc_singleton, snoc_singleton, bijPebbleWinsForever_graph_singleton_iff]

/-- At dimension `k = 1`, `G` and `H` have the same `1`-WL histogram in every round if and only if
they have the same vertex refinement histogram in every round. -/
theorem forall_wlHistogram_one_eq_iff :
    (∀ n, G.wlHistogram 1 n = H.wlHistogram 1 n) ↔
      ∀ n, G.colorHistogram (fun _ => ()) n = H.colorHistogram (fun _ => ()) n := by
  have hwl (h : ∀ n, G.wlHistogram 1 n = H.wlHistogram 1 n) : Fintype.card V = Fintype.card W := by
    simpa only [card_wlHistogram, pow_one] using congrArg Multiset.card (h 0)
  have hcol (h : ∀ n, G.colorHistogram (fun _ => ()) n = H.colorHistogram (fun _ => ()) n) :
      Fintype.card V = Fintype.card W := (colorHistogram_zero_const_eq_iff ()).1 (h 0)
  rcases isEmpty_or_nonempty V with hV | hV <;> rcases isEmpty_or_nonempty W with hW | hW
  · exact iff_of_true (fun n => by simp [wlHistogram_eq]) fun n => by simp [colorHistogram_eq]
  · exact iff_of_false (fun h => Fintype.card_pos.ne (Fintype.card_eq_zero.symm.trans (hwl h)))
      fun h => Fintype.card_pos.ne (Fintype.card_eq_zero.symm.trans (hcol h))
  · exact iff_of_false (fun h => Fintype.card_pos.ne' ((hwl h).trans Fintype.card_eq_zero))
      fun h => Fintype.card_pos.ne' ((hcol h).trans Fintype.card_eq_zero)
  · rw [← forall_realize_countingFormula_empty_iff_wlHistogram_eq,
      ← forall_realize_countingFormula_empty_iff]

end OneDimensional

end Cslib.Logic.FO
