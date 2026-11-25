/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph
public import CslibFrontier.GameTheory.FairDivision.Indivisible.Basic

/-!
# Lipton–Markakis–Mossel–Saberi envy-graph cycle elimination

For **general monotone bundle valuations** (possibly non-additive, with complementarities or
substitutabilities), Round-Robin need not produce an `EF1` allocation. Lipton, Markakis, Mossel,
and Saberi ([LiptonMarkakisMosselSaberi2004]) introduced **envy-graph cycle elimination**, proving
that a complete `EF1` allocation—and hence an allocation whose pairwise envy is bounded by each
agent's maximum marginal utility—exists for *every* monotone valuation profile and can be computed
using `O(m n³)` valuation queries (`≤ m * n * (n - 1)` cycle-elimination steps).

At each item arrival `g = 0, …, m - 1`:

1. Maintain a partial `EF1` allocation `A`.
2. While every agent is envied by someone (`¬ ∃ s, V.IsUnenvied A s`), trace a directed cycle in
   the envy graph `(Fin n, V.envies A)` and rotate bundles backward along the cycle (`A.relabel σ`),
   giving each cycle member the bundle it envied. Because the multiset of bundles is unchanged while
   every cycle member's bundle value strictly increases, `V.IsEF1` is preserved and the total number
   of directed envy edges `V.envyEdgeCount A` strictly decreases (`envyEdgeCount_relabel_lt`).
3. Once an unenvied source agent `s` exists (`V.IsUnenvied A s`), assign the new good `g` to `s`
   (`A.giveGood s g hg`); removing `g` restores `s`'s prior bundle, which no agent envied, so
   `V.IsEF1` is preserved (`IsEF1.giveGood_of_isUnenvied`).

## Main definitions

* `Cslib.GameTheory.FairDivision.Indivisible.MonotoneValuation.envies`,
  `envyTargets`, `envyEdgeCount`, `IsUnenvied`: directed envy relation, per-agent envy set, total
  envy-edge count, and unenvied-agent predicate.
* `Cslib.GameTheory.FairDivision.Indivisible.UnenviedStep`,
  `Cslib.GameTheory.FairDivision.Indivisible.LMMSResult`: structured outputs of cycle elimination
  and full `m`-item LMMS execution.
* `Cslib.GameTheory.FairDivision.Indivisible.MonotoneValuation.eliminateCycles`,
  `lmmsRun`, `lmmsAllocate`: computable envy-cycle elimination and full LMMS allocation algorithm.

## Main results

* `Cslib.GameTheory.FairDivision.Indivisible.MonotoneValuation.IsEF1.giveGood_of_isUnenvied`,
  `IsEF1.relabel_of_le`: `EF1` preservation under unenvied item insertion and weakly improving
  bundle permutation.
* `Cslib.GameTheory.FairDivision.Indivisible.MonotoneValuation.envyEdgeCount_relabel_lt`: rotating
  bundles along any nontrivial envy-improving permutation strictly decreases `envyEdgeCount`.
* `Cslib.GameTheory.FairDivision.Indivisible.MonotoneValuation.eliminateCycles_spec`: cycle
  elimination produces an unenvied agent while preserving `IsEF1` and `allocatedGoods` in at most
  `n * (n - 1)` cycle rotations.
* `Cslib.GameTheory.FairDivision.Indivisible.MonotoneValuation.isComplete_lmmsAllocate`,
  `isEF1_lmmsAllocate`, `lmmsRun_totalCycleSwaps_le`, `lmmsAllocate_val_le_add_maxMarginal`: for
  any monotone valuation profile with `0 < n`, `V.lmmsAllocate hn` is complete, `EF1`, satisfies
  the [LiptonMarkakisMosselSaberi2004] maximum-marginal-envy bound, and performs at most
  `m * (n * (n - 1))` cycle rotations.

## References

* [LiptonMarkakisMosselSaberi2004]
* [Budish2011]
-/

public section

namespace Cslib.GameTheory.FairDivision.Indivisible

open Function

/-- Result of eliminating all directed envy cycles from a partial allocation: an updated allocation
`alloc` over the same goods, an unenvied agent `source`, and the count `cycleSwaps` of cycle
rotations performed. -/
structure UnenviedStep (n m : ℕ) where
  /-- Allocation obtained after rotating out directed envy cycles. -/
  alloc : BundleAllocation n m
  /-- Agent that no agent envies in `alloc`. -/
  source : Fin n
  /-- Number of envy-cycle rotations executed. -/
  cycleSwaps : ℕ
  deriving DecidableEq

/-- Output of the `m`-item Lipton–Markakis–Mossel–Saberi algorithm, recording both the final
allocation and the total number of envy-cycle rotations executed across all items. -/
structure LMMSResult (n m : ℕ) where
  /-- Allocation produced after processing items. -/
  alloc : BundleAllocation n m
  /-- Total number of envy-cycle rotations executed across all processed items. -/
  totalCycleSwaps : ℕ
  deriving DecidableEq

namespace MonotoneValuation

section CycleElimination

variable {n m : ℕ} {R : Type*} [LinearOrder R] (V : MonotoneValuation n m R)

/-- Agent `i` envies agent `j` under `A` when `i` strictly prefers `A.bundle j` to `A.bundle i`. -/
@[expose] def envies (A : BundleAllocation n m) (i j : Fin n) : Prop :=
  V.val i (A.bundle i) < V.val i (A.bundle j)

instance instDecidableEnvies (A : BundleAllocation n m) (i j : Fin n) :
    Decidable (V.envies A i j) :=
  inferInstanceAs (Decidable (V.val i (A.bundle i) < V.val i (A.bundle j)))

/-- Set of agents that agent `i` envies in `A`. -/
@[expose] def envyTargets (A : BundleAllocation n m) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => V.envies A i j

/-- Total number of directed edges in the envy graph of `A`. -/
@[expose] def envyEdgeCount (A : BundleAllocation n m) : ℕ :=
  ∑ i : Fin n, (V.envyTargets A i).card

/-- Agent `s` is unenvied (a source in the envy graph) when no agent envies `s`. -/
@[expose] def IsUnenvied (A : BundleAllocation n m) (s : Fin n) : Prop :=
  ∀ i : Fin n, ¬ V.envies A i s

instance instDecidableIsUnenvied (A : BundleAllocation n m) (s : Fin n) :
    Decidable (V.IsUnenvied A s) :=
  inferInstanceAs (Decidable (∀ i : Fin n, ¬ V.envies A i s))

theorem envyEdgeCount_le (A : BundleAllocation n m) : V.envyEdgeCount A ≤ n * (n - 1) := by
  have hcard : ∀ i : Fin n, (V.envyTargets A i).card ≤ n - 1 := by
    intro i
    have hsub : V.envyTargets A i ⊆ Finset.univ \ {i} := by
      intro j hj
      have hlt : V.envies A i j := (Finset.mem_filter.1 hj).2
      exact Finset.mem_sdiff.2 ⟨Finset.mem_univ j,
        Finset.notMem_singleton.2 fun hji => lt_irrefl _ (hji ▸ hlt)⟩
    calc
      (V.envyTargets A i).card ≤ (Finset.univ \ {i}).card := Finset.card_le_card hsub
      _ = n - 1 := by
        rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 (Finset.mem_univ i)),
          Finset.card_univ, Fintype.card_fin, Finset.card_singleton]
  calc
    V.envyEdgeCount A = ∑ i : Fin n, (V.envyTargets A i).card := rfl
    _ ≤ ∑ _i : Fin n, (n - 1) := Finset.sum_le_sum fun i _ => hcard i
    _ = n * (n - 1) := by simp

/-- Assigning a fresh good `g` to an unenvied agent `s` preserves `EF1` for any monotone valuation.
-/
theorem IsEF1.giveGood_of_isUnenvied {V : MonotoneValuation n m R} {A : BundleAllocation n m}
    (hEF1 : V.IsEF1 A) {s : Fin n} (hUn : V.IsUnenvied A s) {g : Fin m}
    (hg : g ∉ A.allocatedGoods) :
    V.IsEF1 (A.giveGood s g hg) := by
  intro i j
  have hmono_i : V.val i (A.bundle i) ≤ V.val i ((A.giveGood s g hg).bundle i) := by
    by_cases his : i = s
    · subst his
      rw [BundleAllocation.giveGood_bundle_self]
      exact V.mono i (Finset.subset_insert _ _)
    · rw [BundleAllocation.giveGood_bundle_of_ne A g hg his]
  by_cases hjs : j = s
  · subst hjs
    right
    rw [BundleAllocation.giveGood_bundle_self]
    have hg_not : g ∉ A.bundle j := fun hmem =>
      hg (BundleAllocation.mem_allocatedGoods.2 ⟨j, hmem⟩)
    refine ⟨g, Finset.mem_insert_self g _, ?_⟩
    have hsdiff : insert g (A.bundle j) \ {g} = A.bundle j := by
      rw [Finset.sdiff_singleton_eq_erase, Finset.erase_insert hg_not]
    rw [hsdiff]
    exact (not_lt.1 (hUn i)).trans hmono_i
  · rw [BundleAllocation.giveGood_bundle_of_ne A g hg hjs]
    rcases hEF1 i j with hle | ⟨g', hg', hle⟩
    · exact Or.inl (hle.trans hmono_i)
    · exact Or.inr ⟨g', hg', hle.trans hmono_i⟩

/-- Permuting bundles via `σ` so every agent weakly improves preserves `EF1`. -/
theorem IsEF1.relabel_of_le {V : MonotoneValuation n m R} {A : BundleAllocation n m}
    (hEF1 : V.IsEF1 A) {σ : Equiv.Perm (Fin n)}
    (himp : ∀ i : Fin n, V.val i (A.bundle i) ≤ V.val i (A.bundle (σ i))) :
    V.IsEF1 (A.relabel σ) := by
  intro i j
  rcases hEF1 i (σ j) with hle | ⟨g, hg, hle⟩
  · exact Or.inl (hle.trans (himp i))
  · exact Or.inr ⟨g, hg, hle.trans (himp i)⟩

/-- Rotating bundles along any nontrivial envy-improving permutation strictly decreases the total
number of directed edges in the envy graph ([LiptonMarkakisMosselSaberi2004]). -/
theorem envyEdgeCount_relabel_lt {A : BundleAllocation n m} {σ : Equiv.Perm (Fin n)}
    (himp : ∀ i : Fin n, σ i = i ∨ V.envies A i (σ i))
    (hne : ∃ i₀ : Fin n, σ i₀ ≠ i₀) :
    V.envyEdgeCount (A.relabel σ) < V.envyEdgeCount A := by
  obtain ⟨i₀, hi₀⟩ := hne
  let S' (i : Fin n) : Finset (Fin n) :=
    Finset.univ.filter fun k => V.val i (A.bundle (σ i)) < V.val i (A.bundle k)
  have hcard_eq : ∀ i : Fin n, (V.envyTargets (A.relabel σ) i).card = (S' i).card := by
    intro i
    have hmap : (V.envyTargets (A.relabel σ) i).map σ.toEmbedding = S' i := by
      ext k
      rw [Finset.mem_map]
      dsimp only [S']
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨Finset.mem_univ _, (Finset.mem_filter.1 hj).2⟩
      · rintro ⟨-, hk⟩
        refine ⟨σ.symm k, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, by simp⟩
        simpa [envies] using hk
    rw [← hmap, Finset.card_map]
  have hsub : ∀ i : Fin n, S' i ⊆ V.envyTargets A i := by
    intro i k hk
    have hlt : V.val i (A.bundle (σ i)) < V.val i (A.bundle k) := (Finset.mem_filter.1 hk).2
    have hle : V.val i (A.bundle i) ≤ V.val i (A.bundle (σ i)) := by
      rcases himp i with hEq | henv
      · rw [hEq]
      · exact henv.le
    exact Finset.mem_filter.2 ⟨Finset.mem_univ k, lt_of_le_of_lt hle hlt⟩
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, Finset.mem_univ i₀, ?_⟩
  · rw [hcard_eq i]
    exact Finset.card_le_card (hsub i)
  · rw [hcard_eq i₀]
    refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub i₀, fun hEq => ?_⟩)
    have henv₀ : V.envies A i₀ (σ i₀) := (himp i₀).resolve_left hi₀
    have hmemA : σ i₀ ∈ V.envyTargets A i₀ :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, henv₀⟩
    rw [← hEq] at hmemA
    exact lt_irrefl _ (Finset.mem_filter.1 hmemA).2

/-- Computable directed envy-cycle permutation when every agent in `A` is envied by someone:
each agent on the chosen directed cycle receives the bundle it envied, and all other agents keep
their bundles. -/
@[expose] def envyCyclePerm (hn : 0 < n) (A : BundleAllocation n m)
    (hno : ¬ (Finset.univ.filter fun s => V.IsUnenvied A s).Nonempty) :
    Equiv.Perm (Fin n) :=
  have hEnv : ∀ j : Fin n, (Finset.univ.filter fun i => V.envies A i j).Nonempty := by
    intro j
    by_contra hemp
    apply hno
    refine ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ j, fun i hi => hemp ?_⟩⟩
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩⟩
  let pred (j : Fin n) : Fin n := (Finset.univ.filter fun i => V.envies A i j).min' (hEnv j)
  let j₀ : Fin n := pred^[n] ⟨0, hn⟩
  let O : Finset (Fin n) := (Finset.range n).image fun k => pred^[k] j₀
  let g (y : Fin n) : Fin n := if y ∈ O then pred y else y
  have hf_inj : Injective g := by
    have hper : j₀ ∈ periodicPts pred :=
      (Cslib.FunctionalGraph.iterate_mem_periodicPts_iff pred ⟨0, hn⟩ n).2
        ((Cslib.FunctionalGraph.transientDepth_lt_card pred ⟨0, hn⟩).le.trans_eq
          (Fintype.card_fin n))
    let p := minimalPeriod pred j₀
    have hp_pos : 0 < p := minimalPeriod_pos_of_mem_periodicPts hper
    have hp_le : p ≤ n := by
      simpa only [Fintype.card_fin] using minimalPeriod_le_card (f := pred) (x := j₀)
    have hO_closed : ∀ y ∈ O, pred y ∈ O := by
      rintro y hy
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hy
      rw [← iterate_succ_apply' pred, ← Function.iterate_mod_minimalPeriod_eq]
      exact Finset.mem_image_of_mem _ (Finset.mem_range.2 ((Nat.mod_lt _ hp_pos).trans_le hp_le))
    have hO_per : ∀ y ∈ O, pred^[p] y = y := by
      rintro y hy
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hy
      have hfp : pred^[p] j₀ = j₀ := iterate_minimalPeriod (f := pred) (x := j₀)
      rw [← iterate_add_apply, Nat.add_comm, iterate_add_apply, hfp]
    intro y₁ y₂ hy
    dsimp only [g] at hy
    by_cases h₁ : y₁ ∈ O <;> by_cases h₂ : y₂ ∈ O
    · rw [ite_eq_left h₁, ite_eq_left h₂] at hy
      have hp1 : (p - 1).succ = p := by omega
      have hleft : ∀ y ∈ O, pred^[p - 1] (pred y) = y := fun y hyO => by
        rw [← iterate_succ_apply pred, hp1]
        exact hO_per y hyO
      rw [← hleft y₁ h₁, hy, hleft y₂ h₂]
    · rw [ite_eq_left h₁, ite_eq_right h₂] at hy
      exact absurd (hy ▸ hO_closed y₁ h₁) h₂
    · rw [ite_eq_right h₁, ite_eq_left h₂] at hy
      exact absurd (hy.symm ▸ hO_closed y₂ h₂) h₁
    · rwa [ite_eq_right h₁, ite_eq_right h₂] at hy
  let hsurj : Surjective g := (Finite.injective_iff_bijective.1 hf_inj).2
  let inv (y : Fin n) : Fin n :=
    (Finset.univ.filter fun x => g x = y).min' <| by
      obtain ⟨x, hx⟩ := hsurj y
      exact ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩⟩
  have hright : RightInverse inv g := fun y =>
    (Finset.mem_filter.1 ((Finset.univ.filter fun x => g x = y).min'_mem (by
      obtain ⟨x, hx⟩ := hsurj y
      exact ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩⟩))).2
  { toFun := inv
    invFun := g
    left_inv := hright
    right_inv := fun x => hf_inj (hright (g x)) }

private theorem envyCyclePerm_spec (hn : 0 < n) (A : BundleAllocation n m)
    (hno : ¬ (Finset.univ.filter fun s => V.IsUnenvied A s).Nonempty) :
    (∀ x : Fin n, V.envyCyclePerm hn A hno x = x ∨ V.envies A x (V.envyCyclePerm hn A hno x)) ∧
      ∃ x₀ : Fin n, V.envyCyclePerm hn A hno x₀ ≠ x₀ := by
  have hEnv : ∀ j : Fin n, (Finset.univ.filter fun i => V.envies A i j).Nonempty := by
    intro j
    by_contra hemp
    apply hno
    refine ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ j, fun i hi => hemp ?_⟩⟩
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩⟩
  let pred (j : Fin n) : Fin n := (Finset.univ.filter fun i => V.envies A i j).min' (hEnv j)
  have hpred_env : ∀ j : Fin n, V.envies A (pred j) j := fun j =>
    (Finset.mem_filter.1 ((Finset.univ.filter fun i => V.envies A i j).min'_mem (hEnv j))).2
  let j₀ : Fin n := pred^[n] ⟨0, hn⟩
  let O : Finset (Fin n) := (Finset.range n).image fun k => pred^[k] j₀
  set σ := V.envyCyclePerm hn A hno
  have hτ_apply : ∀ y : Fin n, σ.symm y = if y ∈ O then pred y else y := fun _ => rfl
  constructor
  · intro x
    let y := σ x
    have hτy : σ.symm y = x := σ.symm_apply_apply x
    rw [hτ_apply] at hτy
    by_cases hyO : y ∈ O
    · rw [ite_eq_left hyO] at hτy
      right
      have henv : V.envies A (pred y) y := hpred_env y
      rwa [hτy] at henv
    · rw [ite_eq_right hyO] at hτy
      exact Or.inl hτy
  · refine ⟨j₀, fun hEq => ?_⟩
    have hj₀O : j₀ ∈ O := by
      have h0 : pred^[0] j₀ = j₀ := rfl
      exact h0 ▸ Finset.mem_image_of_mem _ (Finset.mem_range.2 hn)
    have hτj₀ : σ.symm j₀ = j₀ := by
      calc
        σ.symm j₀ = σ.symm (σ j₀) := by rw [hEq]
        _ = j₀ := σ.symm_apply_apply j₀
    rw [hτ_apply, ite_eq_left hj₀O] at hτj₀
    have henv := hpred_env j₀
    rw [hτj₀] at henv
    exact lt_irrefl _ henv

/-- Fuel-bounded envy-cycle elimination loop. -/
@[expose] def eliminateCyclesAux (hn : 0 < n) : ℕ → BundleAllocation n m → UnenviedStep n m
  | fuel, A =>
    if h : (Finset.univ.filter fun s => V.IsUnenvied A s).Nonempty then
      { alloc := A
        source := (Finset.univ.filter fun s => V.IsUnenvied A s).min' h
        cycleSwaps := 0 }
    else
      match fuel with
      | 0 => { alloc := A, source := ⟨0, hn⟩, cycleSwaps := 0 }
      | k + 1 =>
        let step := eliminateCyclesAux hn k (A.relabel (V.envyCyclePerm hn A h))
        { alloc := step.alloc
          source := step.source
          cycleSwaps := step.cycleSwaps + 1 }

private theorem eliminateCyclesAux_spec (hn : 0 < n) :
    ∀ (fuel : ℕ) (A : BundleAllocation n m),
      V.envyEdgeCount A ≤ fuel →
      V.IsEF1 A →
      let res := V.eliminateCyclesAux hn fuel A
      V.IsUnenvied res.alloc res.source ∧
        V.IsEF1 res.alloc ∧
        res.alloc.allocatedGoods = A.allocatedGoods ∧
        res.cycleSwaps ≤ fuel
  | 0, A, hfuel, hEF1 => by
    dsimp only [eliminateCyclesAux]
    by_cases h : (Finset.univ.filter fun s => V.IsUnenvied A s).Nonempty
    · rw [dite_eq_left h]
      exact ⟨(Finset.mem_filter.1 ((Finset.univ.filter fun s => V.IsUnenvied A s).min'_mem h)).2,
        hEF1, rfl, le_rfl⟩
    · exfalso
      obtain ⟨himp, hne⟩ := V.envyCyclePerm_spec hn A h
      have hlt := V.envyEdgeCount_relabel_lt himp hne
      omega
  | k + 1, A, hfuel, hEF1 => by
    dsimp only [eliminateCyclesAux]
    by_cases h : (Finset.univ.filter fun s => V.IsUnenvied A s).Nonempty
    · rw [dite_eq_left h]
      exact ⟨(Finset.mem_filter.1 ((Finset.univ.filter fun s => V.IsUnenvied A s).min'_mem h)).2,
        hEF1, rfl, Nat.zero_le _⟩
    · rw [dite_eq_right h]
      obtain ⟨himp, hne⟩ := V.envyCyclePerm_spec hn A h
      have hlt : V.envyEdgeCount (A.relabel (V.envyCyclePerm hn A h)) < V.envyEdgeCount A :=
        V.envyEdgeCount_relabel_lt himp hne
      have hle_val : ∀ i : Fin n,
          V.val i (A.bundle i) ≤ V.val i (A.bundle (V.envyCyclePerm hn A h i)) := by
        intro i
        rcases himp i with hEq | henv
        · rw [hEq]
        · exact henv.le
      have hEF1' : V.IsEF1 (A.relabel (V.envyCyclePerm hn A h)) := hEF1.relabel_of_le hle_val
      obtain ⟨hUn, hEF1_res, halloc, hswaps⟩ :=
        eliminateCyclesAux_spec hn k (A.relabel (V.envyCyclePerm hn A h)) (by omega) hEF1'
      refine ⟨hUn, hEF1_res, ?_, Nat.succ_le_succ hswaps⟩
      rw [halloc, BundleAllocation.allocatedGoods_relabel]

/-- Eliminates all directed envy cycles from `A`, returning an `EF1`-preserving relabeling with an
unenvied agent in at most `n * (n - 1)` cycle rotations. -/
@[expose] def eliminateCycles (hn : 0 < n) (A : BundleAllocation n m) : UnenviedStep n m :=
  V.eliminateCyclesAux hn (V.envyEdgeCount A) A

/-- Specification of `eliminateCycles`: returns an unenvied agent while preserving `IsEF1` and
`allocatedGoods`, using at most `V.envyEdgeCount A ≤ n * (n - 1)` cycle rotations. -/
theorem eliminateCycles_spec (hn : 0 < n) {A : BundleAllocation n m} (hEF1 : V.IsEF1 A) :
    let res := V.eliminateCycles hn A
    V.IsUnenvied res.alloc res.source ∧
      V.IsEF1 res.alloc ∧
      res.alloc.allocatedGoods = A.allocatedGoods ∧
      res.cycleSwaps ≤ n * (n - 1) := by
  obtain ⟨hUn, hEF1', halloc, hswaps⟩ := V.eliminateCyclesAux_spec hn (V.envyEdgeCount A) A le_rfl
    hEF1
  exact ⟨hUn, hEF1', halloc, hswaps.trans (V.envyEdgeCount_le A)⟩

/-! ### Full `m`-item LMMS algorithm -/

/-- Processes the first `k` goods (`0, …, k - 1`) via LMMS envy-cycle elimination. -/
@[expose] def lmmsSteps (hn : 0 < n) : ∀ k ≤ m, LMMSResult n m
  | 0, _ => { alloc := BundleAllocation.empty, totalCycleSwaps := 0 }
  | k + 1, hk =>
    let prev := lmmsSteps hn k (Nat.le_of_succ_le hk)
    let cyc := V.eliminateCycles hn prev.alloc
    let g : Fin m := ⟨k, hk⟩
    if hg : g ∉ cyc.alloc.allocatedGoods then
      { alloc := cyc.alloc.giveGood cyc.source g hg
        totalCycleSwaps := prev.totalCycleSwaps + cyc.cycleSwaps }
    else
      { alloc := cyc.alloc
        totalCycleSwaps := prev.totalCycleSwaps + cyc.cycleSwaps }

private theorem lmmsSteps_spec (hn : 0 < n) :
    ∀ (k : ℕ) (hk : k ≤ m),
      let res := V.lmmsSteps hn k hk
      V.IsEF1 res.alloc ∧
        (∀ x : Fin m, x ∈ res.alloc.allocatedGoods ↔ x.val < k) ∧
        res.totalCycleSwaps ≤ k * (n * (n - 1))
  | 0, _ => by
    dsimp only [lmmsSteps]
    refine ⟨V.isEF1_empty, fun x => ?_, Nat.zero_le _⟩
    simp
  | k + 1, hk => by
    obtain ⟨hEF1_prev, halloc_prev, hswaps_prev⟩ := lmmsSteps_spec hn k (Nat.le_of_succ_le hk)
    set prev := V.lmmsSteps hn k (Nat.le_of_succ_le hk)
    obtain ⟨hUn, hEF1_cyc, halloc_cyc, hswaps_cyc⟩ := V.eliminateCycles_spec hn hEF1_prev
    set cyc := V.eliminateCycles hn prev.alloc
    let g : Fin m := ⟨k, hk⟩
    have hg : g ∉ cyc.alloc.allocatedGoods := by
      rw [halloc_cyc, halloc_prev]
      exact Nat.lt_irrefl k
    dsimp only [lmmsSteps]
    rw [dite_eq_left hg]
    refine ⟨hEF1_cyc.giveGood_of_isUnenvied hUn hg, fun x => ?_, ?_⟩
    · rw [BundleAllocation.allocatedGoods_giveGood, halloc_cyc, Finset.mem_insert, halloc_prev]
      constructor
      · rintro (rfl | hlt)
        · exact Nat.lt_succ_self k
        · exact Nat.lt_succ_of_lt hlt
      · intro hlt
        rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt' | heq
        · exact Or.inr hlt'
        · exact Or.inl (Fin.ext heq)
    · calc
        prev.totalCycleSwaps + cyc.cycleSwaps
            ≤ k * (n * (n - 1)) + n * (n - 1) := Nat.add_le_add hswaps_prev hswaps_cyc
        _ = (k + 1) * (n * (n - 1)) := (Nat.succ_mul k (n * (n - 1))).symm

/-- Full `m`-item Lipton–Markakis–Mossel–Saberi run with cycle-swap count. -/
@[expose] def lmmsRun (hn : 0 < n) : LMMSResult n m :=
  V.lmmsSteps hn m le_rfl

/-- Complete `EF1` allocation produced by the Lipton–Markakis–Mossel–Saberi envy-cycle elimination
algorithm ([LiptonMarkakisMosselSaberi2004]). -/
@[expose] def lmmsAllocate (hn : 0 < n) : BundleAllocation n m :=
  (V.lmmsRun hn).alloc

/-- `V.lmmsAllocate hn` allocates all `m` goods. -/
theorem isComplete_lmmsAllocate (hn : 0 < n) : (V.lmmsAllocate hn).IsComplete := by
  rw [BundleAllocation.isComplete_iff_allocatedGoods_eq_univ]
  ext x
  have hx : x ∈ (V.lmmsAllocate hn).allocatedGoods ↔ x.val < m :=
    (V.lmmsSteps_spec hn m le_rfl).2.1 x
  simp [hx, x.isLt]

/-- **Lipton–Markakis–Mossel–Saberi (`EF1` existence & algorithm for monotone valuations)**
([LiptonMarkakisMosselSaberi2004]; [Budish2011]): for every monotone valuation profile with `0 < n`,
`V.lmmsAllocate hn` is envy-free up to one good (`IsEF1`). -/
theorem isEF1_lmmsAllocate (hn : 0 < n) : V.IsEF1 (V.lmmsAllocate hn) :=
  (V.lmmsSteps_spec hn m le_rfl).1

/-- Across all `m` item insertions, LMMS performs at most `m * (n * (n - 1))` envy-cycle rotations.
-/
theorem lmmsRun_totalCycleSwaps_le (hn : 0 < n) :
    (V.lmmsRun hn).totalCycleSwaps ≤ m * (n * (n - 1)) :=
  (V.lmmsSteps_spec hn m le_rfl).2.2

end CycleElimination

section MaxMarginalBound

variable {n m : ℕ} {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
  (V : MonotoneValuation n m R)

/-- **Lipton–Markakis–Mossel–Saberi maximum-marginal-envy theorem**
([LiptonMarkakisMosselSaberi2004]): in `V.lmmsAllocate hn`, every agent `i`'s envy toward any agent
`j` is at most `V.maxMarginal i`. -/
theorem lmmsAllocate_val_le_add_maxMarginal (hn : 0 < n) (i j : Fin n) :
    V.val i ((V.lmmsAllocate hn).bundle j) ≤
      V.val i ((V.lmmsAllocate hn).bundle i) + V.maxMarginal i :=
  (V.isEF1_lmmsAllocate hn).val_le_add_maxMarginal i j

end MaxMarginalBound

end MonotoneValuation

end Cslib.GameTheory.FairDivision.Indivisible
