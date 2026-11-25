/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.PCP.Approximation.LabelCover.SmallSoundness
public import CslibFrontier.Computability.PCP.Approximation.SetCover.ApproxReduction
public import CslibFrontier.Computability.PCP.Approximation.SetCover.PartitionGadget
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryPair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.EraseDupsBy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Pairing

/-!
# Lund–Yannakakis / Feige hardness of approximating Set Cover

The Lund–Yannakakis / Feige reduction from Label Cover (`GapLabelCover`) to weighted and unweighted
Set Cover (`GapWeightedSetCover`, `GapSetCover`) ([LundYannakakis1994]; [Feige1998]).

For an encoded Label Cover instance `g : Graph (β → γ)` with `m = g.edges.length` edges and a
partition gadget `G : PartitionGadget γ`, every edge `e = (u, v, π)` receives `deg_L(u) * deg_R(v)`
copies of `G`'s universe in the unweighted reduction `toSetCoverOf` (and a single copy with vertex
weights `deg_L(u)`, `deg_R(v)` in the weighted reduction `toWeightedSetCoverOf`), neutralizing
non-uniform degrees in `g`.

* **Completeness**: a satisfying labelling `(ℓ, r)` selects one label per vertex copy on each side,
  forming a cover of cost `2 * m`.
* **Soundness**: for unweighted covers `C`, picking for each vertex `u` (resp. `v`) its copy
  `r₁*(u)` (resp. `r₂*(v)`) of minimum list size yields candidate sets `L u`, `R v` satisfying
  `∑ e, (|L e.src| + |R e.dst|) ≤ |C|`. When `G.Separates t`, Markov's inequality and averaging a
  random selection from `L u × R v` (`exists_labelling_of_list_sets`) yield a deterministic
  labelling satisfying at least `(1 - 2 * ρ / t) * (4 / t ^ 2)` of the edges whenever a cover of
  cost at most `ρ * (2 * m)` exists.

Instantiating `G` with `boolCubeGadget γ` and composing with `exists_GapLabelCover_npHard` proves
**Milestone 1**: `GapSetCover c` and `GapWeightedSetCover c` are `NP`-hard for every `c > 1`
(`GapSetCover_npHard`, `GapWeightedSetCover_npHard`), ruling out polynomial-time constant-factor
approximation algorithms for unweighted and weighted Set Cover unless `P = NP`.

Instantiating `G` with `exists_small_partitionGadget` gives per-instance `c * Real.log n` gap
theorems (`exists_weightedSetCover_log_gap`, `exists_setCover_log_gap`) for any
`0 < c < 1 / (4 * log 2)` and any `t ≥ logGapThreshold c p g.edges.length |γ|` (an explicit
threshold growing like `O(p * log m + log log |γ|)`), conditional on the Label Cover instance
having soundness `≤ 1 / t ^ 2`. Obtaining unconditional complexity-theoretic hardness from this
conditional reduction requires ingredients beyond the constant-round `exists_GapLabelCover_npHard`
base: super-constant parallel repetition uses a quasi-polynomial reduction and therefore yields
hardness against polynomial-time algorithms only under the stronger assumption
`NP ⊈ DTIME(n^{O(log log n)})` rather than `P ≠ NP` alone, whereas `P ≠ NP` hardness requires a
polynomial-time low-soundness Label Cover theorem (such as Dinur–Steurer for `(1 - ε) ln n`).

## Main definitions

* `Cslib.Complexity.SetCoverReduction.toWeightedSetCoverOf`,
  `Cslib.Complexity.SetCoverReduction.toSetCoverOf`: computable weighted and unweighted reductions
  from Label Cover parameterized by explicit label lists and a `PartitionGadget`.
* `Cslib.Complexity.logGapThreshold`: explicit `O(p * log m + log log |γ|)` threshold above
  which the `c * ln n` gap arithmetic holds.

## Main results

* `Cslib.Complexity.polyTimeReducible_GapLabelCover_GapWeightedSetCover`,
  `Cslib.Complexity.polyTimeReducible_GapLabelCover_GapSetCover`: gap-preserving polynomial-time
  reductions from `GapLabelCover`.
* `Cslib.Complexity.GapSetCover_npHard`, `Cslib.Complexity.GapWeightedSetCover_npHard`,
  `Cslib.Complexity.P_eq_NP_of_setCover_approx_const`,
  `Cslib.Complexity.P_eq_NP_of_weightedSetCover_approx_const`: constant-factor NP-hardness for
  every constant.
* `Cslib.Complexity.exists_weightedSetCover_log_gap`,
  `Cslib.Complexity.exists_setCover_log_gap`: per-instance `c * ln n` gap for any `t` above
  `logGapThreshold`, conditional on `1 / t ^ 2` Label Cover soundness.

## References

Primary texts uninspected (bibliographic metadata checked via search records only; locators
unverified and no numbered paper theorems are claimed). The parameterized constructions
`toWeightedSetCoverOf` and `toSetCoverOf` (explicit label lists, `PartitionGadget`, and
`deg_L(u) * deg_R(v)` edge duplication) and the explicit constant threshold `c < 1 / (4 * log 2)`
in `exists_weightedSetCover_log_gap` / `exists_setCover_log_gap` are this library's formalization.

* [C. Lund, M. Yannakakis, *On the hardness of approximating minimization
  problems*][LundYannakakis1994]
* [U. Feige, *A threshold of ln n for approximating set cover*][Feige1998]
-/

public section

namespace Cslib.Complexity

open Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM ComputableInPolyTime

/-! ### Core Label-Cover label extraction lemma -/

section LabelExtraction

private theorem card_pi_update_eq {U : Type*} [Fintype U] [DecidableEq U]
    {T : U → Type*} [∀ u, Fintype (T u)] [∀ u, DecidableEq (T u)] (u₀ : U) (y₀ : T u₀) :
    Fintype.card {f : ∀ u, T u // f u₀ = y₀} * Fintype.card (T u₀) =
      Fintype.card (∀ u, T u) := by
  classical
  let φ : {f : ∀ u, T u // f u₀ = y₀} × T u₀ ≃ ∀ u, T u :=
    { toFun := fun p => Function.update p.1.1 u₀ p.2
      invFun := fun g => (⟨Function.update g u₀ y₀, Function.update_self ..⟩, g u₀)
      left_inv := fun ⟨⟨f, hf⟩, _⟩ => by simp [Function.update_idem, ← hf]
      right_inv := fun g => by simp [Function.update_idem] }
  rw [← Fintype.card_prod, Fintype.card_congr φ]

/-- **Core Lund–Yannakakis label-extraction lemma**: given candidate label sets `L u : Finset β`
and `R v : Finset γ` such that every edge `(u, v)` with `|L u| + |R v| ≤ t` has a matching pair
`(a, b) ∈ L u × R v` and `∑ e, (|L e.src| + |R e.dst|) ≤ ρ * (2 * m)`, some deterministic
labelling satisfies at least `(1 - 2 * ρ / t) * (4 / t ^ 2)` of the edges of `g`. -/
theorem exists_labelling_of_list_sets {β γ : Type} [DecidableEq γ] [Nonempty β] [Nonempty γ]
    (g : Graph (β → γ)) (L : ℕ → Finset β) (R : ℕ → Finset γ) {t : ℕ} (ht : 0 < t)
    {ρ : ℝ} (hm : 0 < g.edges.length)
    (hmatch : ∀ i : Fin g.edges.length,
      (L (g.edges[i].src)).card + (R (g.edges[i].dst)).card ≤ t →
        ∃ a ∈ L (g.edges[i].src), ∃ b ∈ R (g.edges[i].dst), (g.edges[i].constraint) a = b)
    (hsum : ∑ i : Fin g.edges.length,
      (((L (g.edges[i].src)).card + (R (g.edges[i].dst)).card : ℕ) : ℝ) ≤
        ρ * (2 * g.edges.length)) :
    (1 - 2 * ρ / t) * (4 / (t : ℝ) ^ 2) ≤ 1 - (g.toGraph projectionEval).unsatVal := by
  classical
  let m := g.edges.length
  let edge (i : Fin g.edges.length) := g.edges[i.1]'i.2
  let a₀ := Classical.arbitrary β
  let b₀ := Classical.arbitrary γ
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  let goodPred (i : Fin g.edges.length) := (L (edge i).src).card + (R (edge i).dst).card ≤ t
  let goodEdges := Finset.univ.filter goodPred
  let badEdges := Finset.univ.filter (fun i => ¬goodPred i)
  -- Markov's inequality bounds the fraction of oversized edges `badEdges`.
  have hbad_bound : (badEdges.card : ℝ) * t ≤ ρ * (2 * m) :=
    calc (badEdges.card : ℝ) * t
        = ∑ _i ∈ badEdges, (t : ℝ) := by simp
      _ ≤ ∑ i ∈ badEdges, (((L (edge i).src).card + (R (edge i).dst).card : ℕ) : ℝ) :=
          Finset.sum_le_sum fun i hi => by
            exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_le (Finset.mem_filter.1 hi).2)
      _ ≤ ∑ i : Fin g.edges.length, (((L (edge i).src).card + (R (edge i).dst).card : ℕ) : ℝ) :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.cast_nonneg _
      _ ≤ ρ * (2 * m) := hsum
  have hgood_card : (1 - 2 * ρ / t) * m ≤ goodEdges.card := by
    have hsplit_nat : goodEdges.card + badEdges.card = m :=
      (Finset.card_filter_add_card_filter_not goodPred).trans (by simp [m])
    have hsplit : (goodEdges.card : ℝ) + badEdges.card = m := by exact_mod_cast hsplit_nat
    have hdiv : (badEdges.card : ℝ) ≤ (2 * ρ / t) * m := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ht0]; linarith
    linarith
  -- Uniform random assignment over padded nonempty candidate sets `L'`, `R'`.
  let VL := (g.edges.map Edge.src).toFinset
  let VR := (g.edges.map Edge.dst).toFinset
  let L' (u : ℕ) : Finset β := if (L u).Nonempty then L u else {a₀}
  let R' (v : ℕ) : Finset γ := if (R v).Nonempty then R v else {b₀}
  let Choice := (∀ u : VL, L' u.1) × (∀ v : VR, R' v.1)
  have hneL : ∀ u, (L' u).Nonempty := fun u => by
    dsimp only [L']; split_ifs with h; exacts [h, ⟨a₀, Finset.mem_singleton_self _⟩]
  have hneR : ∀ v, (R' v).Nonempty := fun v => by
    dsimp only [R']; split_ifs with h; exacts [h, ⟨b₀, Finset.mem_singleton_self _⟩]
  have : Nonempty Choice := ⟨fun u => ⟨_, (hneL u.1).choose_spec⟩,
    fun v => ⟨_, (hneR v.1).choose_spec⟩⟩
  let σ_of (c : Choice) (x : ℕ) : β × γ :=
    (if hx : x ∈ VL then (c.1 ⟨x, hx⟩).1 else a₀, if hy : x ∈ VR then (c.2 ⟨x, hy⟩).1 else b₀)
  let sat (c : Choice) (i : Fin g.edges.length) : Prop :=
    (g.toGraph projectionEval).Satisfies (σ_of c) i
  let hitSet (i : Fin g.edges.length) := Finset.univ.filter fun c : Choice => sat c i
  -- Each good edge is satisfied with probability ≥ 1 / (|L u| * |R v|) ≥ 4 / t^2.
  have hhit_edge : ∀ i ∈ goodEdges,
      (4 / (t : ℝ) ^ 2) * Fintype.card Choice ≤ (hitSet i).card := by
    intro i hi
    let d := edge i
    have hle := (Finset.mem_filter.1 hi).2
    obtain ⟨a_star, haL, b_star, hbR, heq⟩ := hmatch i hle
    have hLeq : L' d.src = L d.src := ite_eq_left ⟨a_star, haL⟩
    have hReq : R' d.dst = R d.dst := ite_eq_left ⟨b_star, hbR⟩
    let u₀ : VL := ⟨d.src, List.mem_toFinset.2 (List.mem_map.2 ⟨d, List.getElem_mem i.2, rfl⟩)⟩
    let v₀ : VR := ⟨d.dst, List.mem_toFinset.2 (List.mem_map.2 ⟨d, List.getElem_mem i.2, rfl⟩)⟩
    let yL₀ : L' u₀.1 := ⟨a_star, hLeq ▸ haL⟩
    let yR₀ : R' v₀.1 := ⟨b_star, hReq ▸ hbR⟩
    let hitPair := {fL : ∀ u : VL, L' u.1 // fL u₀ = yL₀} ×
      {fR : ∀ v : VR, R' v.1 // fR v₀ = yR₀}
    have hcard_mul : Fintype.card hitPair * ((L' u₀.1).card * (R' v₀.1).card) =
        Fintype.card Choice := by
      have hL := card_pi_update_eq (T := fun u : VL => L' u.1) u₀ yL₀
      have hR := card_pi_update_eq (T := fun v : VR => R' v.1) v₀ yR₀
      simp only [hitPair, Choice, Fintype.card_prod]
      rw [← hL, ← hR, Fintype.card_coe, Fintype.card_coe]
      ring
    have hsub_hit : Fintype.card hitPair ≤ (hitSet i).card := by
      rw [← Fintype.card_coe (hitSet i)]
      refine Fintype.card_le_of_injective (fun p : hitPair => (⟨(p.1.1, p.2.1), ?_⟩ : hitSet i))
        fun p q h => Prod.ext (Subtype.ext (congrArg (fun x => x.1.1) h))
          (Subtype.ext (congrArg (fun x => x.1.2) h))
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      change (g.toGraph projectionEval).Satisfies (σ_of (p.1.1, p.2.1)) i
      rw [satisfies_toGraph_projectionEval_iff, List.get_eq_getElem]
      have hu' : d.src ∈ VL := u₀.2
      have hv' : d.dst ∈ VR := v₀.2
      have hL : (p.1.1 ⟨d.src, hu'⟩).1 = a_star := congrArg Subtype.val p.1.2
      have hR : (p.2.1 ⟨d.dst, hv'⟩).1 = b_star := congrArg Subtype.val p.2.2
      simp only [σ_of, d, edge, hu', hv', ↓reduceDIte, hL, hR]
      exact heq
    have hprod_le : 4 * ((L' u₀.1).card * (R' v₀.1).card) ≤ t ^ 2 := by
      rw [hLeq, hReq, ← mul_assoc]
      exact (_root_.four_mul_le_sq_add _ _).trans (Nat.pow_le_pow_left hle 2)
    have hnat : 4 * Fintype.card Choice ≤ (hitSet i).card * t ^ 2 := by
      rw [← hcard_mul, mul_left_comm]
      exact Nat.mul_le_mul hsub_hit hprod_le
    rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos ht0)]
    exact_mod_cast hnat
  -- Double counting and averaging yield a concrete assignment `c_star`.
  have hsum_sat : ∑ _c : Choice, (goodEdges.card : ℝ) * (4 / (t : ℝ) ^ 2) ≤
      ∑ c : Choice, ((Finset.univ.filter fun i : Fin g.edges.length => sat c i).card : ℝ) := by
    have hswap : (∑ i : Fin g.edges.length, ((hitSet i).card : ℝ)) =
        ∑ c : Choice, ((Finset.univ.filter fun i : Fin g.edges.length => sat c i).card : ℝ) := by
      exact_mod_cast (by simp only [hitSet, Finset.card_filter]; exact Finset.sum_comm :
        ∑ i : Fin g.edges.length, (hitSet i).card =
          ∑ c : Choice, (Finset.univ.filter fun i : Fin g.edges.length => sat c i).card)
    calc ∑ _c : Choice, (goodEdges.card : ℝ) * (4 / (t : ℝ) ^ 2)
        = ∑ _i ∈ goodEdges, (4 / (t : ℝ) ^ 2) * Fintype.card Choice := by simp; ring
      _ ≤ ∑ i ∈ goodEdges, ((hitSet i).card : ℝ) := Finset.sum_le_sum hhit_edge
      _ ≤ ∑ i : Fin g.edges.length, ((hitSet i).card : ℝ) :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.cast_nonneg _
      _ = _ := hswap
  obtain ⟨c_star, -, hc_star⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum_sat
  have hcompl_nat : ((g.toGraph projectionEval).unsatEdges (σ_of c_star)).card +
      (Finset.univ.filter fun i : Fin m => sat c_star i).card = m := by
    rw [add_comm]
    exact (Finset.card_filter_add_card_filter_not _).trans (by simp)
  have hcompl : (((g.toGraph projectionEval).unsatEdges (σ_of c_star)).card : ℝ) +
      ((Finset.univ.filter fun i : Fin m => sat c_star i).card : ℝ) = m := by
    exact_mod_cast hcompl_nat
  have hfrac : (goodEdges.card : ℝ) * (4 / (t : ℝ) ^ 2) ≤
      (1 - (g.toGraph projectionEval).unsatVal) * m := by
    have h1 := ConstraintGraph.unsatVal_le (g.toGraph projectionEval) (σ_of c_star)
    have h2 : (1 - (g.toGraph projectionEval).unsatFrac (σ_of c_star)) * m =
        ((Finset.univ.filter fun i : Fin m => sat c_star i).card : ℝ) := by
      rw [ConstraintGraph.unsatFrac, Fintype.card_fin]
      change (1 - _ / (m : ℝ)) * m = _
      field_simp [hm0.ne']; linarith
    exact hc_star.trans (h2 ▸ mul_le_mul_of_nonneg_right (by linarith) hm0.le)
  refine le_of_mul_le_mul_right ?_ hm0
  calc (1 - 2 * ρ / t) * (4 / (t : ℝ) ^ 2) * m
      = (1 - 2 * ρ / t) * m * (4 / (t : ℝ) ^ 2) := by ring
    _ ≤ (goodEdges.card : ℝ) * (4 / (t : ℝ) ^ 2) := by gcongr
    _ ≤ _ := hfrac

end LabelExtraction

/-! ### Reductions to Weighted and Unweighted Set Cover -/

namespace SetCoverReduction

section Combinatorial

variable {β γ : Type}

/-- Deduplicated list of left endpoints appearing in `g.edges`. -/
@[expose] def leftVertices (g : Graph (β → γ)) : List ℕ :=
  (g.edges.map Edge.src).eraseDupsBy fun a b => decide (a = b)

/-- Deduplicated list of right endpoints appearing in `g.edges`. -/
@[expose] def rightVertices (g : Graph (β → γ)) : List ℕ :=
  (g.edges.map Edge.dst).eraseDupsBy fun a b => decide (a = b)

/-- Left degree of vertex `u` in `g.edges`. -/
@[expose] def degL (g : Graph (β → γ)) (u : ℕ) : ℕ :=
  g.edges.countP fun d => decide (d.src = u)

/-- Right degree of vertex `v` in `g.edges`. -/
@[expose] def degR (g : Graph (β → γ)) (v : ℕ) : ℕ :=
  g.edges.countP fun d => decide (d.dst = v)

private theorem mem_leftVertices {g : Graph (β → γ)} {u : ℕ} :
    u ∈ leftVertices g ↔ ∃ d ∈ g.edges, d.src = u := by
  simp only [leftVertices, List.mem_eraseDupsBy_eq, List.mem_map]

private theorem mem_rightVertices {g : Graph (β → γ)} {v : ℕ} :
    v ∈ rightVertices g ↔ ∃ d ∈ g.edges, d.dst = v := by
  simp only [rightVertices, List.mem_eraseDupsBy_eq, List.mem_map]

private theorem deg_pos_of_mem {g : Graph (β → γ)} {proj : Edge (β → γ) → ℕ} {u : ℕ}
    (hu : ∃ d ∈ g.edges, proj d = u) :
    0 < g.edges.countP (fun d => decide (proj d = u)) :=
  let ⟨d, hd, hdu⟩ := hu
  List.countP_pos_iff.2 ⟨d, hd, decide_eq_true hdu⟩

private theorem degL_pos_of_mem {g : Graph (β → γ)} {u : ℕ} (hu : u ∈ leftVertices g) :
    0 < degL g u :=
  deg_pos_of_mem (mem_leftVertices.1 hu)

private theorem degR_pos_of_mem {g : Graph (β → γ)} {v : ℕ} (hv : v ∈ rightVertices g) :
    0 < degR g v :=
  deg_pos_of_mem (mem_rightVertices.1 hv)

private theorem sum_map_eq_sum_countP_mul {α : Type*} (l : List α) (proj : α → ℕ)
    (S : Finset ℕ) (hS : ∀ x ∈ l, proj x ∈ S) (f : ℕ → ℕ) :
    (l.map fun x => f (proj x)).sum =
      ∑ u ∈ S, l.countP (fun x => decide (proj x = u)) * f u := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, add_mul, Finset.sum_add_distrib,
      ih fun y hy => hS y (List.mem_cons_of_mem x hy)]
    have : ∑ u ∈ S, (if decide (proj x = u) = true then 1 else 0) * f u = f (proj x) := by
      simp [hS x List.mem_cons_self]
    omega

private theorem sum_over_edges_deg (g : Graph (β → γ)) (proj : Edge (β → γ) → ℕ)
    (V : Finset ℕ) (hV : ∀ d ∈ g.edges, proj d ∈ V) (f : ℕ → ℕ) :
    ∑ i : Fin g.edges.length, f (proj g.edges[i]) =
      ∑ u ∈ V, g.edges.countP (fun d => decide (proj d = u)) * f u := by
  rw [← sum_map_eq_sum_countP_mul g.edges proj V hV f,
    ← List.sum_ofFn (f := fun i : Fin g.edges.length => f (proj g.edges[i]))]
  congr 1; ext1 i; by_cases hi : i < g.edges.length <;> simp [hi]

private theorem sum_deg_eq_length (g : Graph (β → γ)) (proj : Edge (β → γ) → ℕ)
    (V : Finset ℕ) (hV : ∀ d ∈ g.edges, proj d ∈ V) :
    ∑ u ∈ V, g.edges.countP (fun d => decide (proj d = u)) = g.edges.length := by
  simpa using (sum_over_edges_deg g proj V hV (fun _ => 1)).symm

private theorem sum_cand_card_le_of_deg_bounds
    (g : Graph (β → γ)) (L : ℕ → Finset β) (R : ℕ → Finset γ) {totL totR tot : ℕ} {ρ : ℝ}
    (hsumL : ∑ u ∈ (leftVertices g).toFinset, degL g u * (L u).card ≤ totL)
    (hsumR : ∑ v ∈ (rightVertices g).toFinset, degR g v * (R v).card ≤ totR)
    (hpart : totL + totR = tot) (htot : (tot : ℝ) ≤ ρ * (2 * g.edges.length)) :
    ∑ i : Fin g.edges.length,
      (((L g.edges[i].src).card + (R g.edges[i].dst).card : ℕ) : ℝ) ≤
        ρ * (2 * g.edges.length) := by
  have hsum_nat : ∑ i : Fin g.edges.length, ((L g.edges[i].src).card + (R g.edges[i].dst).card) ≤
      tot := by
    have hL := sum_over_edges_deg g Edge.src (leftVertices g).toFinset
      (fun d hd => List.mem_toFinset.2 (mem_leftVertices.2 ⟨d, hd, rfl⟩)) (fun u => (L u).card)
    have hR := sum_over_edges_deg g Edge.dst (rightVertices g).toFinset
      (fun d hd => List.mem_toFinset.2 (mem_rightVertices.2 ⟨d, hd, rfl⟩)) (fun v => (R v).card)
    rw [Finset.sum_add_distrib, hL, hR]
    exact (Nat.add_le_add hsumL hsumR).trans hpart.le
  exact le_trans (by exact_mod_cast hsum_nat) htot

private theorem mem_edgeFilter_flatMap (g : Graph (β → γ)) (fallback : γ)
    (proj : Edge (β → γ) → ℕ) (u : ℕ) (body : ℕ → Edge (β → γ) → List ℕ) (z : ℕ) :
    z ∈ ((List.range g.edges.length).flatMap fun e =>
        let d := g.edges.getD e ⟨0, 0, fun _ => fallback⟩
        if proj d = u then body e d else []) ↔
      ∃ (e : ℕ) (he : e < g.edges.length), proj (g.edges[e]'he) = u ∧
        z ∈ body e (g.edges[e]'he) := by
  simp only [List.mem_flatMap, List.mem_range]
  refine ⟨fun ⟨e, he, hz⟩ => ?_, fun ⟨e, he, h, hz⟩ => ⟨e, he, by
    rw [List.getD_eq_getElem _ _ he]; simp [h, hz]⟩⟩
  rw [List.getD_eq_getElem _ _ he] at hz
  split_ifs at hz with h
  · exact ⟨e, he, h, hz⟩
  · cases hz

private theorem getElem_fin_map_append_left_eq {α₁ α₂ δ : Type*} {S : List δ}
    {L₁ : List α₁} {L₂ : List α₂} {f₁ : α₁ → δ} {f₂ : α₂ → δ}
    (hS : S = L₁.map f₁ ++ L₂.map f₂) {i : Fin S.length} {k : ℕ}
    (hi : (i : ℕ) = k) (hk : k < L₁.length) :
    S[i] = f₁ (L₁[k]'hk) := by
  subst hS
  rw [Fin.getElem_fin]
  simp only [hi]
  rw [List.getElem_append_left (by simp [hk]), List.getElem_map]

private theorem getElem_fin_map_append_right_eq {α₁ α₂ δ : Type*} {S : List δ}
    {L₁ : List α₁} {L₂ : List α₂} {f₁ : α₁ → δ} {f₂ : α₂ → δ}
    (hS : S = L₁.map f₁ ++ L₂.map f₂) {i : Fin S.length} {nL k : ℕ}
    (hi : (i : ℕ) = nL + k) (hnL : nL = L₁.length) (hk : k < L₂.length) :
    S[i] = f₂ (L₂[k]'hk) := by
  subst hS hnL
  have hge : (L₁.map f₁).length ≤ L₁.length + k := by simp
  rw [Fin.getElem_fin]
  simp only [hi, List.getElem_append_right hge, List.length_map, Nat.add_sub_cancel_left,
    List.getElem_map]

private structure SideInfo (α : Type) where
  V : Finset ℕ
  deg : ℕ → ℕ
  copies : ℕ → ℕ
  wt : ℕ → ℕ
  n : ℕ
  item : Fin n → ℕ × ℕ × α
  item_mem : ∀ k : Fin n, (item k).1 ∈ V ∧ (item k).2.1 < copies (item k).1
  copies_pos : ∀ v ∈ V, 0 < copies v
  copies_mul_wt : ∀ v ∈ V, copies v * wt v = deg v

private def SideInfo.HasAll {α : Type} (S : SideInfo α) : Prop :=
  ∀ v ∈ S.V, ∀ r < S.copies v, ∀ a : α, ∃ k : Fin S.n, S.item k = (v, r, a)

private theorem SideInfo.chooseCover {α : Type} (S : SideInfo α) (hAll : S.HasAll) (lab : ℕ → α) :
    ∃ C : Finset (Fin S.n),
      (∀ v ∈ S.V, ∀ r < S.copies v, ∃ k ∈ C, S.item k = (v, r, lab v)) ∧
      ∑ k ∈ C, S.wt (S.item k).1 = ∑ v ∈ S.V, S.deg v := by
  classical
  let pick (p : Σ v : ↥S.V, Fin (S.copies v.1)) : Fin S.n :=
    (hAll p.1.1 p.1.2 p.2.1 p.2.2 (lab p.1.1)).choose
  have hspec (p : Σ v : ↥S.V, Fin (S.copies v.1)) :
      S.item (pick p) = (p.1.1, p.2.1, lab p.1.1) :=
    (hAll p.1.1 p.1.2 p.2.1 p.2.2 (lab p.1.1)).choose_spec
  have hinj : Function.Injective pick := by
    rintro ⟨⟨v₁, hv₁⟩, ⟨r₁, hr₁⟩⟩ ⟨⟨v₂, hv₂⟩, ⟨r₂, hr₂⟩⟩ h
    have h1 := (hspec ⟨⟨v₁, hv₁⟩, ⟨r₁, hr₁⟩⟩).symm.trans
      ((congrArg S.item h).trans (hspec ⟨⟨v₂, hv₂⟩, ⟨r₂, hr₂⟩⟩))
    obtain ⟨rfl, rfl, -⟩ := Prod.mk.injEq .. |>.mp h1
    rfl
  refine ⟨Finset.univ.image pick, fun v hv r hr =>
    ⟨pick ⟨⟨v, hv⟩, ⟨r, hr⟩⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), hspec _⟩, ?_⟩
  rw [Finset.sum_image (fun _ _ _ _ h => hinj h), Fintype.sum_sigma]
  refine (Finset.sum_congr rfl fun v _ => ?_).trans (Finset.sum_coe_sort S.V S.deg)
  simp only [hspec, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact S.copies_mul_wt v.1 v.2

private theorem SideInfo.exists_candOfCover {α : Type} (S : SideInfo α) (Sub : Finset (Fin S.n)) :
    ∃ (cand : ℕ → Finset α) (rStar : ℕ → ℕ),
      (∀ v ∈ S.V, rStar v < S.copies v) ∧
      (∀ k ∈ Sub, ∀ v r, (S.item k).1 = v → (S.item k).2.1 = r → r = rStar v →
        (S.item k).2.2 ∈ cand v) ∧
      ∑ v ∈ S.V, S.deg v * (cand v).card ≤ ∑ k ∈ Sub, S.wt (S.item k).1 := by
  classical
  let rep (v r : ℕ) : Finset α :=
    (Sub.filter fun k => (S.item k).1 = v ∧ (S.item k).2.1 = r).image fun k => (S.item k).2.2
  have hmin (v : ℕ) (hv : v ∈ S.V) := Finset.exists_min_image (Finset.range (S.copies v))
    (fun r => (rep v r).card) ⟨0, Finset.mem_range.2 (S.copies_pos v hv)⟩
  let rStar (v : ℕ) : ℕ := if hv : v ∈ S.V then (hmin v hv).choose else 0
  let cand (v : ℕ) : Finset α := rep v (rStar v)
  refine ⟨cand, rStar,
    fun v hv => by simpa only [rStar, hv, ↓reduceDIte] using
      Finset.mem_range.1 (hmin v hv).choose_spec.1,
    fun k hk v _ hv hr heq => by
      subst heq; exact Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨hk, hv, hr⟩, rfl⟩,
    ?_⟩
  rw [← Finset.sum_fiberwise_of_maps_to (s := Sub) (t := S.V) (fun k _ => (S.item_mem k).1)]
  refine Finset.sum_le_sum fun v hv => ?_
  calc S.deg v * (cand v).card
      = S.wt v * (S.copies v * (cand v).card) := by rw [← S.copies_mul_wt v hv]; ring
    _ = S.wt v * ∑ _r ∈ Finset.range (S.copies v), (cand v).card := by simp
    _ ≤ S.wt v * ∑ r ∈ Finset.range (S.copies v), (rep v r).card :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum fun r hr => by
          simpa only [cand, rStar, hv, ↓reduceDIte] using (hmin v hv).choose_spec.2 r hr)
    _ ≤ S.wt v * ∑ r ∈ Finset.range (S.copies v),
          ((Sub.filter fun k => (S.item k).1 = v).filter fun k => (S.item k).2.1 = r).card :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum fun r _ =>
          Finset.card_image_le.trans_eq (congrArg Finset.card (by
            ext k; simp [Finset.mem_filter, and_assoc])))
    _ = S.wt v * (Sub.filter fun k => (S.item k).1 = v).card := by
        rw [Finset.sum_card_fiberwise_eq_card_filter, Finset.filter_eq_self.2]
        intro k hk; exact Finset.mem_range.2 ((Finset.mem_filter.1 hk).2 ▸ (S.item_mem k).2)
    _ = ∑ k ∈ Sub.filter (fun k => (S.item k).1 = v), S.wt (S.item k).1 := by
        rw [Finset.card_eq_sum_ones, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k hk => by rw [mul_one, (Finset.mem_filter.1 hk).2]

private def weightedSideInfo {α : Type} (verts : List ℕ) (labels : List α)
    (deg : ℕ → ℕ) : SideInfo α :=
  let items := verts.flatMap fun v => labels.map fun a => (v, a)
  { V := verts.toFinset
    deg := deg
    copies := fun _ => 1
    wt := deg
    n := items.length
    item := fun k => (items[k].1, 0, items[k].2)
    item_mem := fun k => by
      obtain ⟨v, hv, heq⟩ := List.mem_flatMap.1 (List.getElem_mem k.isLt)
      obtain ⟨a, -, hpair⟩ := List.mem_map.1 heq
      have hv' : items[k].1 = v := (congrArg Prod.fst hpair).symm
      exact ⟨List.mem_toFinset.2 (hv' ▸ hv), Nat.one_pos⟩
    copies_pos := fun _ _ => Nat.one_pos
    copies_mul_wt := fun _ _ => one_mul _ }

private theorem weightedSideInfo_hasAll {α : Type} {verts : List ℕ} {labels : List α}
    (hlabels : ∀ a, a ∈ labels) (deg : ℕ → ℕ) :
    (weightedSideInfo verts labels deg).HasAll := by
  intro v hv r hr a
  obtain rfl : r = 0 := Nat.lt_one_iff.1 hr
  have hmem : (v, a) ∈ verts.flatMap fun v => labels.map fun a => (v, a) :=
    List.mem_flatMap.2 ⟨v, List.mem_toFinset.1 hv, List.mem_map.2 ⟨a, hlabels a, rfl⟩⟩
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.1 hmem
  exact ⟨⟨k, hk⟩, by simp [weightedSideInfo, hget]⟩

private def unweightedSideInfo {α : Type} (verts : List ℕ) (labels : List α)
    (deg : ℕ → ℕ) (hdeg_pos : ∀ v ∈ verts, 0 < deg v) : SideInfo α :=
  let items := verts.flatMap fun v => (List.range (deg v)).flatMap fun r => labels.map fun a =>
    (v, r, a)
  { V := verts.toFinset
    deg := deg
    copies := deg
    wt := fun _ => 1
    n := items.length
    item := fun k => items[k]
    item_mem := fun k => by
      obtain ⟨v, hv, heq⟩ := List.mem_flatMap.1 (List.getElem_mem k.isLt)
      obtain ⟨r, hr, heq2⟩ := List.mem_flatMap.1 heq
      obtain ⟨a, -, hpair⟩ := List.mem_map.1 heq2
      have hv' : items[k].1 = v := (congrArg Prod.fst hpair).symm
      have hr' : items[k].2.1 = r := (congrArg (fun p => p.2.1) hpair).symm
      exact ⟨List.mem_toFinset.2 (hv' ▸ hv), hv' ▸ hr' ▸ List.mem_range.1 hr⟩
    copies_pos := fun v hv => hdeg_pos v (List.mem_toFinset.1 hv)
    copies_mul_wt := fun _ _ => mul_one _ }

private theorem unweightedSideInfo_hasAll {α : Type} {verts : List ℕ} {labels : List α}
    (hlabels : ∀ a, a ∈ labels) (deg : ℕ → ℕ) (hdeg_pos : ∀ v ∈ verts, 0 < deg v) :
    (unweightedSideInfo verts labels deg hdeg_pos).HasAll := by
  intro v hv r hr a
  have hmem : (v, r, a) ∈ verts.flatMap fun v =>
      (List.range (deg v)).flatMap fun r => labels.map fun a => (v, r, a) :=
    List.mem_flatMap.2 ⟨v, List.mem_toFinset.1 hv,
      List.mem_flatMap.2 ⟨r, List.mem_range.2 hr, List.mem_map.2 ⟨a, hlabels a, rfl⟩⟩⟩
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.1 hmem
  exact ⟨⟨k, hk⟩, hget⟩

private structure BipartiteCoverModel {β γ : Type} (g : Graph (β → γ)) (G : PartitionGadget γ) where
  ground : List ℕ
  numSets : ℕ
  mem : ℕ → Fin numSets → Prop
  weight : Fin numSets → ℕ
  left : SideInfo β
  right : SideInfo γ
  hVL : left.V = (leftVertices g).toFinset
  hVR : right.V = (rightVertices g).toFinset
  hdegL : left.deg = degL g
  hdegR : right.deg = degR g
  numSets_eq : numSets = left.n + right.n
  weight_left : ∀ k : Fin left.n,
    weight ⟨k.1, Nat.lt_of_lt_of_eq (Nat.lt_add_right _ k.isLt) numSets_eq.symm⟩ =
      left.wt (left.item k).1
  weight_right : ∀ k : Fin right.n,
    weight ⟨left.n + k.1, Nat.lt_of_lt_of_eq (Nat.add_lt_add_left k.isLt _) numSets_eq.symm⟩ =
      right.wt (right.item k).1
  ground_elim : ∀ z ∈ ground,
    ∃ e : Fin g.edges.length, ∃ x < G.size,
      ∃ r₁ < left.copies g.edges[e].src, ∃ r₂ < right.copies g.edges[e].dst,
        (∀ k : Fin left.n, (left.item k).1 = g.edges[e].src → (left.item k).2.1 = r₁ →
          G.mem x (g.edges[e].constraint (left.item k).2.2) = false →
          mem z ⟨k.1, Nat.lt_of_lt_of_eq (Nat.lt_add_right _ k.isLt) numSets_eq.symm⟩) ∧
        (∀ k : Fin right.n, (right.item k).1 = g.edges[e].dst → (right.item k).2.1 = r₂ →
          G.mem x (right.item k).2.2 = true →
          mem z ⟨left.n + k.1, Nat.lt_of_lt_of_eq (Nat.add_lt_add_left k.isLt _) numSets_eq.symm⟩)
  ground_intro : ∀ (e : Fin g.edges.length) (x : ℕ), x < G.size →
    ∀ r₁ < left.copies g.edges[e].src, ∀ r₂ < right.copies g.edges[e].dst,
      ∃ z ∈ ground,
        (∀ k : Fin left.n,
          mem z ⟨k.1, Nat.lt_of_lt_of_eq (Nat.lt_add_right _ k.isLt) numSets_eq.symm⟩ →
          (left.item k).1 = g.edges[e].src ∧ (left.item k).2.1 = r₁ ∧
          G.mem x (g.edges[e].constraint (left.item k).2.2) = false) ∧
        (∀ k : Fin right.n,
          mem z ⟨left.n + k.1, Nat.lt_of_lt_of_eq (Nat.add_lt_add_left k.isLt _) numSets_eq.symm⟩ →
          (right.item k).1 = g.edges[e].dst ∧ (right.item k).2.1 = r₂ ∧
          G.mem x (right.item k).2.2 = true)

private def BipartiteCoverModel.idxL {g : Graph (β → γ)} {G : PartitionGadget γ}
    (M : BipartiteCoverModel g G) (k : Fin M.left.n) : Fin M.numSets :=
  ⟨k.1, Nat.lt_of_lt_of_eq (Nat.lt_add_right _ k.isLt) M.numSets_eq.symm⟩

private def BipartiteCoverModel.idxR {g : Graph (β → γ)} {G : PartitionGadget γ}
    (M : BipartiteCoverModel g G) (k : Fin M.right.n) : Fin M.numSets :=
  ⟨M.left.n + k.1, Nat.lt_of_lt_of_eq (Nat.add_lt_add_left k.isLt _) M.numSets_eq.symm⟩

private theorem BipartiteCoverModel.src_mem_leftV {g : Graph (β → γ)} {G : PartitionGadget γ}
    (M : BipartiteCoverModel g G) (e : Fin g.edges.length) : g.edges[e].src ∈ M.left.V :=
  M.hVL ▸ List.mem_toFinset.2 (mem_leftVertices.2 ⟨g.edges[e], List.getElem_mem e.isLt, rfl⟩)

private theorem BipartiteCoverModel.dst_mem_rightV {g : Graph (β → γ)} {G : PartitionGadget γ}
    (M : BipartiteCoverModel g G) (e : Fin g.edges.length) : g.edges[e].dst ∈ M.right.V :=
  M.hVR ▸ List.mem_toFinset.2 (mem_rightVertices.2 ⟨g.edges[e], List.getElem_mem e.isLt, rfl⟩)

private theorem BipartiteCoverModel.coverable [Nonempty β]
    {g : Graph (β → γ)} {G : PartitionGadget γ} (M : BipartiteCoverModel g G)
    (hL : M.left.HasAll) (hR : M.right.HasAll) :
    ∃ C : Finset (Fin M.numSets), ∀ z ∈ M.ground, ∃ i ∈ C, M.mem z i := by
  refine ⟨Finset.univ, fun z hz => ?_⟩
  obtain ⟨e, x, _, r₁, hr₁, r₂, hr₂, hcovL, hcovR⟩ := M.ground_elim z hz
  let a₀ : β := Classical.arbitrary β
  let b := g.edges[e].constraint a₀
  cases hbit : G.mem x b
  · obtain ⟨k, hk⟩ := hL _ (M.src_mem_leftV e) r₁ hr₁ a₀
    exact ⟨M.idxL k, Finset.mem_univ _, hcovL k (by rw [hk]) (by rw [hk]) (by rw [hk]; exact hbit)⟩
  · obtain ⟨k, hk⟩ := hR _ (M.dst_mem_rightV e) r₂ hr₂ b
    exact ⟨M.idxR k, Finset.mem_univ _, hcovR k (by rw [hk]) (by rw [hk]) (by rw [hk]; exact hbit)⟩

private theorem BipartiteCoverModel.idxL_inj {g : Graph (β → γ)} {G : PartitionGadget γ}
    (M : BipartiteCoverModel g G) : Function.Injective M.idxL :=
  fun _ _ h => Fin.ext (by simpa [idxL] using congrArg Fin.val h)

private theorem BipartiteCoverModel.idxR_inj {g : Graph (β → γ)} {G : PartitionGadget γ}
    (M : BipartiteCoverModel g G) : Function.Injective M.idxR :=
  fun _ _ h => Fin.ext (by have := congrArg Fin.val h; dsimp only [idxR] at this; omega)

private theorem BipartiteCoverModel.complete [DecidableEq γ] [Nonempty β] [Nonempty γ]
    {g : Graph (β → γ)} {G : PartitionGadget γ} (M : BipartiteCoverModel g G)
    (hL : M.left.HasAll) (hR : M.right.HasAll)
    (hsat : 1 ≤ 1 - (g.toGraph projectionEval).unsatVal) :
    ∃ C : Finset (Fin M.numSets),
      (∀ z ∈ M.ground, ∃ i ∈ C, M.mem z i) ∧ ∑ i ∈ C, M.weight i ≤ 2 * g.edges.length := by
  classical
  have hSat : (g.toGraph projectionEval).Satisfiable :=
    (ConstraintGraph.unsatVal_eq_zero_iff _).1
      (le_antisymm (by linarith) (ConstraintGraph.unsatVal_nonneg _))
  obtain ⟨ℓ, r, hsat_edge⟩ := (satisfiable_toGraph_projectionEval_iff g).1 hSat
  obtain ⟨CL, hCL_cov, hCL_wt⟩ := M.left.chooseCover hL ℓ
  obtain ⟨CR, hCR_cov, hCR_wt⟩ := M.right.chooseCover hR r
  refine ⟨CL.image M.idxL ∪ CR.image M.idxR, fun z hz => ?_, ?_⟩
  · obtain ⟨e, x, _, r₁, hr₁, r₂, hr₂, hcovL, hcovR⟩ := M.ground_elim z hz
    have hcon := hsat_edge g.edges[e] (List.getElem_mem e.isLt)
    cases hbit : G.mem x (g.edges[e].constraint (ℓ g.edges[e].src))
    · obtain ⟨k, hkCL, hk⟩ := hCL_cov _ (M.src_mem_leftV e) r₁ hr₁
      exact ⟨M.idxL k, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hkCL),
        hcovL k (by rw [hk]) (by rw [hk]) (by rw [hk]; exact hbit)⟩
    · obtain ⟨k, hkCR, hk⟩ := hCR_cov _ (M.dst_mem_rightV e) r₂ hr₂
      exact ⟨M.idxR k, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hkCR),
        hcovR k (by rw [hk]) (by rw [hk]) (by rw [hk]; exact hcon ▸ hbit)⟩
  · have hside {α : Type} (S : SideInfo α) (C : Finset (Fin S.n))
        (idx : Fin S.n → Fin M.numSets) (hinj : Function.Injective idx)
        (hwt : ∀ k, M.weight (idx k) = S.wt (S.item k).1)
        (hCwt : ∑ k ∈ C, S.wt (S.item k).1 = ∑ v ∈ S.V, S.deg v)
        (proj : Edge (β → γ) → ℕ)
        (hdeg : ∀ v, S.deg v = g.edges.countP fun d => decide (proj d = v))
        (hV : ∀ d ∈ g.edges, proj d ∈ S.V) :
        ∑ i ∈ C.image idx, M.weight i = g.edges.length := by
      rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
      exact (Finset.sum_congr rfl fun k _ => hwt k).trans <| hCwt.trans <| by
        simp only [hdeg]; exact sum_deg_eq_length g proj S.V hV
    have hwtL := hside M.left CL M.idxL M.idxL_inj M.weight_left hCL_wt Edge.src
      (fun _ => congrFun M.hdegL _) fun d hd =>
        M.hVL ▸ List.mem_toFinset.2 (mem_leftVertices.2 ⟨d, hd, rfl⟩)
    have hwtR := hside M.right CR M.idxR M.idxR_inj M.weight_right hCR_wt Edge.dst
      (fun _ => congrFun M.hdegR _) fun d hd =>
        M.hVR ▸ List.mem_toFinset.2 (mem_rightVertices.2 ⟨d, hd, rfl⟩)
    have := Finset.sum_union_inter (s₁ := CL.image M.idxL) (s₂ := CR.image M.idxR) (f := M.weight)
    omega

private theorem BipartiteCoverModel.sound_of_isCover [DecidableEq γ] [Nonempty β] [Nonempty γ]
    {g : Graph (β → γ)} {G : PartitionGadget γ} (M : BipartiteCoverModel g G)
    {t : ℕ} (ht : 0 < t) (hsep : G.Separates t) (hm : 0 < g.edges.length) {ρ : ℝ}
    {C : Finset (Fin M.numSets)}
    (hC : ∀ z ∈ M.ground, ∃ i ∈ C, M.mem z i)
    (hwt : ((∑ i ∈ C, M.weight i : ℕ) : ℝ) ≤ ρ * (2 * g.edges.length)) :
    (1 - 2 * ρ / t) * (4 / (t : ℝ) ^ 2) ≤ 1 - (g.toGraph projectionEval).unsatVal := by
  classical
  let SubL : Finset (Fin M.left.n) := Finset.univ.filter fun k => M.idxL k ∈ C
  let SubR : Finset (Fin M.right.n) := Finset.univ.filter fun k => M.idxR k ∈ C
  obtain ⟨L, r₁Star, hr₁Star, hL_mem, hsumL⟩ := M.left.exists_candOfCover SubL
  obtain ⟨R, r₂Star, hr₂Star, hR_mem, hsumR⟩ := M.right.exists_candOfCover SubR
  have himgL : SubL.image M.idxL = C.filter fun i : Fin M.numSets => (i : ℕ) < M.left.n := by
    ext i; simp only [SubL, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨k, hk, h⟩ => h ▸ ⟨hk, k.isLt⟩, fun ⟨hi, hlt⟩ => ⟨⟨i.1, hlt⟩, hi, Fin.ext rfl⟩⟩
  have himgR : SubR.image M.idxR = C.filter fun i : Fin M.numSets => M.left.n ≤ (i : ℕ) := by
    ext i; simp only [SubR, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun ⟨k, hk, h⟩ => h ▸ ⟨hk, Nat.le_add_right _ _⟩, fun ⟨hi, hge⟩ => ?_⟩
    have hlt : i.1 < M.left.n + M.right.n := i.isLt.trans_eq M.numSets_eq
    have heq : M.idxR ⟨i.1 - M.left.n, by omega⟩ = i := Fin.ext (by dsimp [idxR]; omega)
    exact ⟨⟨i.1 - M.left.n, by omega⟩, heq ▸ hi, heq⟩
  have hpart : (∑ k ∈ SubL, M.left.wt (M.left.item k).1) +
      (∑ k ∈ SubR, M.right.wt (M.right.item k).1) = ∑ i ∈ C, M.weight i := by
    have hL : ∑ k ∈ SubL, M.left.wt (M.left.item k).1 =
        ∑ i ∈ C.filter fun i : Fin M.numSets => (i : ℕ) < M.left.n, M.weight i := by
      rw [← himgL, Finset.sum_image (fun _ _ _ _ h => M.idxL_inj h)]
      exact Finset.sum_congr rfl fun k _ => (M.weight_left k).symm
    have hR : ∑ k ∈ SubR, M.right.wt (M.right.item k).1 =
        ∑ i ∈ C.filter fun i : Fin M.numSets => M.left.n ≤ (i : ℕ), M.weight i := by
      rw [← himgR, Finset.sum_image (fun _ _ _ _ h => M.idxR_inj h)]
      exact Finset.sum_congr rfl fun k _ => (M.weight_right k).symm
    rw [hL, hR]
    simpa only [not_lt] using Finset.sum_filter_add_sum_filter_not C
      (fun i : Fin M.numSets => (i : ℕ) < M.left.n) M.weight
  refine exists_labelling_of_list_sets g L R ht hm (fun i hle => ?_)
    (sum_cand_card_le_of_deg_bounds g L R (by rwa [← M.hVL, ← M.hdegL])
      (by rwa [← M.hVR, ← M.hdegR]) hpart hwt)
  refine G.exists_eq_of_covers hsep g.edges[i].constraint _ _ hle fun x hx => ?_
  obtain ⟨z, hz, hbackL, hbackR⟩ := M.ground_intro i x hx
    (r₁Star _) (hr₁Star _ (M.src_mem_leftV i)) (r₂Star _) (hr₂Star _ (M.dst_mem_rightV i))
  obtain ⟨j, hjC, hjz⟩ := hC z hz
  by_cases hjL : (j : ℕ) < M.left.n
  · left
    let k : Fin M.left.n := ⟨j.1, hjL⟩
    have hkSub : k ∈ SubL := Finset.mem_filter.2 ⟨Finset.mem_univ _, hjC⟩
    obtain ⟨hsrc, hr1, hmem⟩ := hbackL k hjz
    exact ⟨(M.left.item k).2.2, hL_mem k hkSub _ _ hsrc hr1 rfl, hmem⟩
  · right
    have hlt : j.1 < M.left.n + M.right.n := j.isLt.trans_eq M.numSets_eq
    let k : Fin M.right.n := ⟨j.1 - M.left.n, by omega⟩
    have hidx : M.idxR k = j := Fin.ext (by dsimp only [idxR, k]; omega)
    have hkSub : k ∈ SubR := Finset.mem_filter.2 ⟨Finset.mem_univ _, hidx ▸ hjC⟩
    obtain ⟨hdst, hr2, hmem⟩ := hbackR k ((congrArg (M.mem z) hidx).mpr hjz)
    exact ⟨(M.right.item k).2.2, hR_mem k hkSub _ _ hdst hr2 rfl, hmem⟩

/-! #### Weighted reduction -/

/-- Ground elements for the weighted Set Cover reduction: pairs `Nat.pair e x` for edge index
`e < g.edges.length` and gadget element `x < G.size`. -/
@[expose] def weightedGround {γ : Type} (G : PartitionGadget γ) (g : Graph (β → γ)) : List ℕ :=
  (List.range g.edges.length).flatMap fun e =>
    (List.range G.size).map (Nat.pair e)

/-- Left candidate sets `(u, a)` in the weighted reduction, weighted by `degL g u`. -/
@[expose] def weightedLeftSet (fallback : γ) (G : PartitionGadget γ) (g : Graph (β → γ))
    (u : ℕ) (a : β) : WeightedSet :=
  ⟨(List.range g.edges.length).flatMap fun e =>
      let d := g.edges.getD e ⟨0, 0, fun _ => fallback⟩
      if d.src = u then
        ((List.range G.size).filter fun x => !G.mem x (d.constraint a)).map (Nat.pair e)
      else [],
    degL g u⟩

/-- Right candidate sets `(v, b)` in the weighted reduction, weighted by `degR g v`. -/
@[expose] def weightedRightSet (fallback : γ) (G : PartitionGadget γ) (g : Graph (β → γ))
    (v : ℕ) (b : γ) : WeightedSet :=
  ⟨(List.range g.edges.length).flatMap fun e =>
      let d := g.edges.getD e ⟨0, 0, fun _ => fallback⟩
      if d.dst = v then
        ((List.range G.size).filter fun x => G.mem x b).map (Nat.pair e)
      else [],
    degR g v⟩

/-- Left item list `(u, a)` for the weighted reduction. -/
@[expose] def weightedLeftItems (bs : List β) (g : Graph (β → γ)) : List (ℕ × β) :=
  (leftVertices g).flatMap fun u => bs.map fun a => (u, a)

/-- Right item list `(v, b)` for the weighted reduction. -/
@[expose] def weightedRightItems (gs : List γ) (g : Graph (β → γ)) : List (ℕ × γ) :=
  (rightVertices g).flatMap fun v => gs.map fun b => (v, b)

/-- Weighted set system constructed by the Lund–Yannakakis / Feige reduction. -/
@[expose] def weightedSetSystemOf (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) (g : Graph (β → γ)) : WeightedSetSystem :=
  ⟨weightedGround G g,
    (weightedLeftItems bs g).map (fun p => weightedLeftSet fallback G g p.1 p.2) ++
      (weightedRightItems gs g).map (fun p => weightedRightSet fallback G g p.1 p.2)⟩

/-- Computable weighted Set Cover reduction from Label Cover parameterized by explicit label lists
`bs`, `gs`, a fallback label `fallback : γ`, and a partition gadget `G`. -/
@[expose] def toWeightedSetCoverOf (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) (g : Graph (β → γ)) : WeightedSetSystem × ℕ :=
  (weightedSetSystemOf bs gs fallback G g, 2 * g.edges.length)

theorem weightedSetSystemOf_ground_length {bs : List β} {gs : List γ} {fallback : γ}
    {G : PartitionGadget γ} {g : Graph (β → γ)} :
    (weightedSetSystemOf bs gs fallback G g).ground.length = g.edges.length * G.size := by
  simp [weightedSetSystemOf, weightedGround, List.length_flatMap, List.map_const',
    List.sum_replicate]

private theorem mem_weightedGround {G : PartitionGadget γ} {g : Graph (β → γ)} {z : ℕ} :
    z ∈ weightedGround G g ↔
      ∃ e < g.edges.length, ∃ x < G.size, Nat.pair e x = z := by
  simp only [weightedGround, List.mem_flatMap, List.mem_map, List.mem_range]

private theorem mem_weightedLeftSet {fallback : γ} {G : PartitionGadget γ} {g : Graph (β → γ)}
    {u : ℕ} {a : β} {e x : ℕ} (he : e < g.edges.length) (hx : x < G.size) :
    Nat.pair e x ∈ (weightedLeftSet fallback G g u a).elements ↔
      g.edges[e].src = u ∧ G.mem x (g.edges[e].constraint a) = false := by
  dsimp only [weightedLeftSet]
  refine (mem_edgeFilter_flatMap g fallback Edge.src u
    (fun e d => ((List.range G.size).filter fun x => !G.mem x (d.constraint a)).map (Nat.pair e))
    (Nat.pair e x)).trans ?_
  simp only [List.mem_map, List.mem_filter, List.mem_range, Bool.not_eq_true']
  exact ⟨fun ⟨_, _, hsrc, _, ⟨_, hx'⟩, hp⟩ => by
      obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 hp; exact ⟨hsrc, hx'⟩,
    fun ⟨hsrc, hmem⟩ => ⟨e, he, hsrc, x, ⟨hx, hmem⟩, rfl⟩⟩

private theorem mem_weightedRightSet {fallback : γ} {G : PartitionGadget γ} {g : Graph (β → γ)}
    {v : ℕ} {b : γ} {e x : ℕ} (he : e < g.edges.length) (hx : x < G.size) :
    Nat.pair e x ∈ (weightedRightSet fallback G g v b).elements ↔
      g.edges[e].dst = v ∧ G.mem x b = true := by
  dsimp only [weightedRightSet]
  refine (mem_edgeFilter_flatMap g fallback Edge.dst v
    (fun e _ => ((List.range G.size).filter fun x => G.mem x b).map (Nat.pair e))
    (Nat.pair e x)).trans ?_
  simp only [List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨fun ⟨_, _, hdst, _, ⟨_, hx'⟩, hp⟩ => by
      obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 hp; exact ⟨hdst, hx'⟩,
    fun ⟨hdst, hmem⟩ => ⟨e, he, hdst, x, ⟨hx, hmem⟩, rfl⟩⟩

private theorem weightedSetSystemOf_sets (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) (g : Graph (β → γ)) :
    (weightedSetSystemOf bs gs fallback G g).sets =
      (weightedLeftItems bs g).map (fun p => weightedLeftSet fallback G g p.1 p.2) ++
        (weightedRightItems gs g).map (fun p => weightedRightSet fallback G g p.1 p.2) := rfl

private abbrev weightedModel (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) (g : Graph (β → γ)) : BipartiteCoverModel g G where
  ground := (weightedSetSystemOf bs gs fallback G g).ground
  numSets := (weightedSetSystemOf bs gs fallback G g).sets.length
  mem z i := z ∈ (weightedSetSystemOf bs gs fallback G g).sets[i].elements
  weight i := (weightedSetSystemOf bs gs fallback G g).sets[i].weight
  left := weightedSideInfo (leftVertices g) bs (degL g)
  right := weightedSideInfo (rightVertices g) gs (degR g)
  hVL := rfl
  hVR := rfl
  hdegL := rfl
  hdegR := rfl
  numSets_eq := by
    simp [weightedSetSystemOf, weightedSideInfo, weightedLeftItems, weightedRightItems]
  weight_left k := by
    rw [getElem_fin_map_append_left_eq (weightedSetSystemOf_sets bs gs fallback G g) rfl k.isLt]
    rfl
  weight_right k := by
    rw [getElem_fin_map_append_right_eq (weightedSetSystemOf_sets bs gs fallback G g) rfl rfl
      k.isLt]
    rfl
  ground_elim z hz := by
    obtain ⟨e, he, x, hx, rfl⟩ := mem_weightedGround.1 hz
    refine ⟨⟨e, he⟩, x, hx, 0, Nat.one_pos, 0, Nat.one_pos,
      fun k hsrc _ hmem => ?_, fun k hdst _ hmem => ?_⟩
    · rw [getElem_fin_map_append_left_eq (weightedSetSystemOf_sets bs gs fallback G g) rfl k.isLt]
      exact (mem_weightedLeftSet he hx).2 ⟨hsrc.symm, hmem⟩
    · rw [getElem_fin_map_append_right_eq (weightedSetSystemOf_sets bs gs fallback G g) rfl rfl
        k.isLt]
      exact (mem_weightedRightSet he hx).2 ⟨hdst.symm, hmem⟩
  ground_intro e x hx r₁ hr₁ r₂ hr₂ := by
    obtain rfl : r₁ = 0 := Nat.lt_one_iff.1 hr₁
    obtain rfl : r₂ = 0 := Nat.lt_one_iff.1 hr₂
    refine ⟨Nat.pair e.1 x, mem_weightedGround.2 ⟨e.1, e.isLt, x, hx, rfl⟩,
      fun k hmem => ?_, fun k hmem => ?_⟩
    · rw [getElem_fin_map_append_left_eq (weightedSetSystemOf_sets bs gs fallback G g) rfl k.isLt]
        at hmem
      exact let ⟨h, b⟩ := (mem_weightedLeftSet e.isLt hx).1 hmem; ⟨h.symm, rfl, b⟩
    · rw [getElem_fin_map_append_right_eq (weightedSetSystemOf_sets bs gs fallback G g) rfl rfl
        k.isLt] at hmem
      exact let ⟨h, b⟩ := (mem_weightedRightSet e.isLt hx).1 hmem; ⟨h.symm, rfl, b⟩

theorem weightedSetSystemOf_coverable [Nonempty β] {bs : List β} {gs : List γ} {fallback : γ}
    (hbs_all : ∀ a, a ∈ bs) (hgs_all : ∀ b, b ∈ gs)
    (G : PartitionGadget γ) (g : Graph (β → γ)) :
    (weightedSetSystemOf bs gs fallback G g).Coverable :=
  (weightedModel bs gs fallback G g).coverable
    (weightedSideInfo_hasAll hbs_all _) (weightedSideInfo_hasAll hgs_all _)

theorem weightedSetSystemOf_complete [DecidableEq γ] [Nonempty β] [Nonempty γ]
    {bs : List β} {gs : List γ} {fallback : γ}
    (hbs_all : ∀ a, a ∈ bs) (hgs_all : ∀ b, b ∈ gs)
    (G : PartitionGadget γ) (g : Graph (β → γ))
    (hsat : 1 ≤ 1 - (g.toGraph projectionEval).unsatVal) :
    (weightedSetSystemOf bs gs fallback G g).optCoverWeight ≤ 2 * g.edges.length := by
  obtain ⟨C, hC, hwt⟩ := (weightedModel bs gs fallback G g).complete
    (weightedSideInfo_hasAll hbs_all _) (weightedSideInfo_hasAll hgs_all _) hsat
  exact (WeightedSetSystem.optCoverWeight_le hC).trans hwt

theorem weightedSetSystemOf_sound_of_isCover [DecidableEq γ] [Nonempty β] [Nonempty γ]
    {bs : List β} {gs : List γ} {fallback : γ} {G : PartitionGadget γ} {t : ℕ} (ht : 0 < t)
    (hsep : G.Separates t) {g : Graph (β → γ)} (hm : 0 < g.edges.length) {ρ : ℝ}
    {C : Finset (Fin (weightedSetSystemOf bs gs fallback G g).sets.length)}
    (hC : (weightedSetSystemOf bs gs fallback G g).IsCover C)
    (hwt : ((weightedSetSystemOf bs gs fallback G g).coverWeight C : ℝ) ≤
      ρ * (2 * g.edges.length)) :
    (1 - 2 * ρ / t) * (4 / (t : ℝ) ^ 2) ≤ 1 - (g.toGraph projectionEval).unsatVal :=
  (weightedModel bs gs fallback G g).sound_of_isCover ht hsep hm hC hwt

theorem weightedSetSystemOf_sound [DecidableEq γ] [Nonempty β] [Nonempty γ]
    {bs : List β} {gs : List γ} {fallback : γ} (hbs_all : ∀ a, a ∈ bs) (hgs_all : ∀ b, b ∈ gs)
    {G : PartitionGadget γ} {t : ℕ} (ht : 0 < t) (hsep : G.Separates t)
    {g : Graph (β → γ)} (hm : 0 < g.edges.length) {ρ : ℝ}
    (hwt : ((weightedSetSystemOf bs gs fallback G g).optCoverWeight : ℝ) ≤
      ρ * (2 * g.edges.length)) :
    (1 - 2 * ρ / t) * (4 / (t : ℝ) ^ 2) ≤ 1 - (g.toGraph projectionEval).unsatVal := by
  obtain ⟨C, hC, hCwt⟩ := WeightedSetSystem.exists_isCover_optCoverWeight
    (weightedSetSystemOf_coverable hbs_all hgs_all G g)
  rw [← hCwt] at hwt
  exact weightedSetSystemOf_sound_of_isCover ht hsep hm hC hwt

/-! #### Unweighted reduction -/

/-- Ground elements for the unweighted Set Cover reduction: quadruples
`(e, x, r₁, r₂)` encoded as `Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂)` for each edge `e`,
gadget element `x < G.size`, left copy `r₁ < degL g e.src`, and right copy `r₂ < degR g e.dst`. -/
@[expose] def unweightedGround (fallback : γ) (G : PartitionGadget γ) (g : Graph (β → γ)) :
    List ℕ :=
  (List.range g.edges.length).flatMap fun e =>
    let d := g.edges.getD e ⟨0, 0, fun _ => fallback⟩
    (List.range G.size).flatMap fun x =>
      (List.range (degL g d.src)).flatMap fun r₁ =>
        (List.range (degR g d.dst)).map fun r₂ =>
          Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂)

/-- Left candidate sets `(u, r₁, a)` in the unweighted reduction. -/
@[expose] def unweightedLeftSet (fallback : γ) (G : PartitionGadget γ) (g : Graph (β → γ))
    (u r₁ : ℕ) (a : β) : List ℕ :=
  (List.range g.edges.length).flatMap fun e =>
    let d := g.edges.getD e ⟨0, 0, fun _ => fallback⟩
    if d.src = u then
      ((List.range G.size).filter fun x => !G.mem x (d.constraint a)).flatMap fun x =>
        (List.range (degR g d.dst)).map fun r₂ =>
          Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂)
    else []

/-- Right candidate sets `(v, r₂, b)` in the unweighted reduction. -/
@[expose] def unweightedRightSet (fallback : γ) (G : PartitionGadget γ) (g : Graph (β → γ))
    (v r₂ : ℕ) (b : γ) : List ℕ :=
  (List.range g.edges.length).flatMap fun e =>
    let d := g.edges.getD e ⟨0, 0, fun _ => fallback⟩
    if d.dst = v then
      ((List.range G.size).filter fun x => G.mem x b).flatMap fun x =>
        (List.range (degL g d.src)).map fun r₁ =>
          Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂)
    else []

/-- Left item list `(u, r₁, a)` for the unweighted reduction. -/
@[expose] def unweightedLeftItems (bs : List β) (g : Graph (β → γ)) : List (ℕ × ℕ × β) :=
  (leftVertices g).flatMap fun u =>
    (List.range (degL g u)).flatMap fun r₁ =>
      bs.map fun a => (u, r₁, a)

/-- Right item list `(v, r₂, b)` for the unweighted reduction. -/
@[expose] def unweightedRightItems (gs : List γ) (g : Graph (β → γ)) : List (ℕ × ℕ × γ) :=
  (rightVertices g).flatMap fun v =>
    (List.range (degR g v)).flatMap fun r₂ =>
      gs.map fun b => (v, r₂, b)

/-- Unweighted set system constructed by the Lund–Yannakakis / Feige reduction. -/
@[expose] def setSystemOf (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) (g : Graph (β → γ)) : SetSystem :=
  ⟨unweightedGround fallback G g,
    (unweightedLeftItems bs g).map
        (fun (u, r₁, a) => unweightedLeftSet fallback G g u r₁ a) ++
      (unweightedRightItems gs g).map
        (fun (v, r₂, b) => unweightedRightSet fallback G g v r₂ b)⟩

/-- Computable unweighted Set Cover reduction from Label Cover parameterized by explicit label
lists `bs`, `gs`, a fallback label `fallback : γ`, and a partition gadget `G`. -/
@[expose] def toSetCoverOf (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) (g : Graph (β → γ)) : SetSystem × ℕ :=
  (setSystemOf bs gs fallback G g, 2 * g.edges.length)

private theorem mem_unweightedGround {fallback : γ} {G : PartitionGadget γ}
    {g : Graph (β → γ)} {z : ℕ} :
    z ∈ unweightedGround fallback G g ↔
      ∃ e < g.edges.length, ∃ x < G.size,
        ∃ r₁ < degL g (g.edges.getD e ⟨0, 0, fun _ => fallback⟩).src,
          ∃ r₂ < degR g (g.edges.getD e ⟨0, 0, fun _ => fallback⟩).dst,
            Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂) = z := by
  simp only [unweightedGround, List.mem_flatMap, List.mem_map, List.mem_range]

private theorem mem_unweightedLeftSet {fallback : γ} {G : PartitionGadget γ} {g : Graph (β → γ)}
    {u r₁' : ℕ} {a : β} {e x r₁ r₂ : ℕ} (he : e < g.edges.length) (hx : x < G.size)
    (hr₂ : r₂ < degR g g.edges[e].dst) :
    Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂) ∈ unweightedLeftSet fallback G g u r₁' a ↔
      g.edges[e].src = u ∧ r₁ = r₁' ∧ G.mem x (g.edges[e].constraint a) = false := by
  dsimp only [unweightedLeftSet]
  refine (mem_edgeFilter_flatMap g fallback Edge.src u
    (fun e d => ((List.range G.size).filter fun x => !G.mem x (d.constraint a)).flatMap fun x =>
      (List.range (degR g d.dst)).map fun r₂ => Nat.pair (Nat.pair e x) (Nat.pair r₁' r₂))
    (Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂))).trans ?_
  simp only [List.mem_flatMap, List.mem_filter, List.mem_range, Bool.not_eq_true', List.mem_map]
  refine ⟨fun ⟨_, _, hsrc, _, ⟨_, hx'⟩, _, _, hp⟩ => ?_,
    fun ⟨hsrc, h, hmem⟩ => h ▸ ⟨e, he, hsrc, x, ⟨hx, hmem⟩, r₂, hr₂, rfl⟩⟩
  obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := by simpa only [Nat.pair_eq_pair] using hp
  exact ⟨hsrc, rfl, hx'⟩

private theorem mem_unweightedRightSet {fallback : γ} {G : PartitionGadget γ} {g : Graph (β → γ)}
    {v r₂' : ℕ} {b : γ} {e x r₁ r₂ : ℕ} (he : e < g.edges.length) (hx : x < G.size)
    (hr₁ : r₁ < degL g g.edges[e].src) :
    Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂) ∈ unweightedRightSet fallback G g v r₂' b ↔
      g.edges[e].dst = v ∧ r₂ = r₂' ∧ G.mem x b = true := by
  dsimp only [unweightedRightSet]
  refine (mem_edgeFilter_flatMap g fallback Edge.dst v
    (fun e d => ((List.range G.size).filter fun x => G.mem x b).flatMap fun x =>
      (List.range (degL g d.src)).map fun r₁ => Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂'))
    (Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂))).trans ?_
  simp only [List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map]
  refine ⟨fun ⟨_, _, hdst, _, ⟨_, hx'⟩, _, _, hp⟩ => ?_,
    fun ⟨hdst, h, hmem⟩ => h ▸ ⟨e, he, hdst, x, ⟨hx, hmem⟩, r₁, hr₁, rfl⟩⟩
  obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := by simpa only [Nat.pair_eq_pair] using hp
  exact ⟨hdst, rfl, hx'⟩

theorem setSystemOf_ground_length_le {bs : List β} {gs : List γ} {fallback : γ}
    {G : PartitionGadget γ} {g : Graph (β → γ)} :
    (setSystemOf bs gs fallback G g).ground.length ≤ g.edges.length ^ 3 * G.size := by
  simp only [setSystemOf, unweightedGround, List.length_flatMap, List.length_map,
    List.length_range, List.map_const', List.sum_replicate, smul_eq_mul]
  refine (List.sum_le_sum fun e _ => (Nat.mul_le_mul_left G.size (Nat.mul_le_mul
    List.countP_le_length List.countP_le_length))).trans_eq ?_
  simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  ring

theorem setSystemOf_ground_length_ge {bs : List β} {gs : List γ} {fallback : γ}
    {G : PartitionGadget γ} {g : Graph (β → γ)} (hm : 0 < g.edges.length) :
    G.size ≤ (setSystemOf bs gs fallback G g).ground.length := by
  have hr₁ : 0 < degL g g.edges[0].src :=
    degL_pos_of_mem (mem_leftVertices.2 ⟨g.edges[0], List.getElem_mem hm, rfl⟩)
  have hr₂ : 0 < degR g g.edges[0].dst :=
    degR_pos_of_mem (mem_rightVertices.2 ⟨g.edges[0], List.getElem_mem hm, rfl⟩)
  let f (x : Fin G.size) : ℕ := Nat.pair (Nat.pair 0 x.1) (Nat.pair 0 0)
  have hinj : Function.Injective f := fun _ _ h =>
    Fin.ext (Nat.pair_eq_pair.1 (Nat.pair_eq_pair.1 h).1).2
  calc G.size = (Finset.univ.image f).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    _ ≤ (setSystemOf bs gs fallback G g).ground.toFinset.card := Finset.card_le_card fun z hz => by
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hz
        refine List.mem_toFinset.2 (mem_unweightedGround.2 ⟨0, hm, x.1, x.isLt, 0, ?_, 0, ?_, rfl⟩)
        · rwa [List.getD_eq_getElem _ _ hm]
        · rwa [List.getD_eq_getElem _ _ hm]
    _ ≤ (setSystemOf bs gs fallback G g).ground.length := List.toFinset_card_le _

theorem setSystemOf_ground_length_pos {bs : List β} {gs : List γ} {fallback : γ}
    {G : PartitionGadget γ} {g : Graph (β → γ)}
    (hm : 0 < g.edges.length) (hG : 0 < G.size) :
    0 < (setSystemOf bs gs fallback G g).ground.length :=
  hG.trans_le (setSystemOf_ground_length_ge hm)

private theorem setSystemOf_sets (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) (g : Graph (β → γ)) :
    (setSystemOf bs gs fallback G g).sets =
      (unweightedLeftItems bs g).map (fun x => unweightedLeftSet fallback G g x.1 x.2.1 x.2.2) ++
        (unweightedRightItems gs g).map
          (fun x => unweightedRightSet fallback G g x.1 x.2.1 x.2.2) := rfl

private abbrev unweightedModel (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) (g : Graph (β → γ)) : BipartiteCoverModel g G where
  ground := (setSystemOf bs gs fallback G g).ground
  numSets := (setSystemOf bs gs fallback G g).sets.length
  mem z i := z ∈ (setSystemOf bs gs fallback G g).sets[i]
  weight _ := 1
  left := unweightedSideInfo (leftVertices g) bs (degL g) (fun _ => degL_pos_of_mem)
  right := unweightedSideInfo (rightVertices g) gs (degR g) (fun _ => degR_pos_of_mem)
  hVL := rfl
  hVR := rfl
  hdegL := rfl
  hdegR := rfl
  numSets_eq := by
    simp [setSystemOf, unweightedSideInfo, unweightedLeftItems, unweightedRightItems]
  weight_left _ := rfl
  weight_right _ := rfl
  ground_elim z hz := by
    obtain ⟨e, he, x, hx, r₁, hr₁, r₂, hr₂, rfl⟩ := mem_unweightedGround.1 hz
    rw [List.getD_eq_getElem _ _ he] at hr₁ hr₂
    refine ⟨⟨e, he⟩, x, hx, r₁, hr₁, r₂, hr₂, fun k hsrc hr₁' hmem => ?_,
      fun k hdst hr₂' hmem => ?_⟩
    · rw [getElem_fin_map_append_left_eq (setSystemOf_sets bs gs fallback G g) rfl k.isLt]
      exact (mem_unweightedLeftSet he hx hr₂).2 ⟨hsrc.symm, hr₁'.symm, hmem⟩
    · rw [getElem_fin_map_append_right_eq (setSystemOf_sets bs gs fallback G g) rfl rfl k.isLt]
      exact (mem_unweightedRightSet he hx hr₁).2 ⟨hdst.symm, hr₂'.symm, hmem⟩
  ground_intro e x hx r₁ hr₁ r₂ hr₂ := by
    refine ⟨Nat.pair (Nat.pair e.1 x) (Nat.pair r₁ r₂), mem_unweightedGround.2
      ⟨e.1, e.isLt, x, hx, r₁, by rwa [List.getD_eq_getElem _ _ e.isLt],
        r₂, by rwa [List.getD_eq_getElem _ _ e.isLt], rfl⟩,
      fun k hmem => ?_, fun k hmem => ?_⟩
    · rw [getElem_fin_map_append_left_eq (setSystemOf_sets bs gs fallback G g) rfl k.isLt] at hmem
      exact let ⟨h, r, b⟩ := (mem_unweightedLeftSet e.isLt hx hr₂).1 hmem; ⟨h.symm, r.symm, b⟩
    · rw [getElem_fin_map_append_right_eq (setSystemOf_sets bs gs fallback G g) rfl rfl k.isLt]
        at hmem
      exact let ⟨h, r, b⟩ := (mem_unweightedRightSet e.isLt hx hr₁).1 hmem; ⟨h.symm, r.symm, b⟩

theorem setSystemOf_coverable [Nonempty β] {bs : List β} {gs : List γ} {fallback : γ}
    (hbs_all : ∀ a, a ∈ bs) (hgs_all : ∀ b, b ∈ gs)
    (G : PartitionGadget γ) (g : Graph (β → γ)) :
    (setSystemOf bs gs fallback G g).Coverable :=
  (unweightedModel bs gs fallback G g).coverable
    (unweightedSideInfo_hasAll hbs_all (degL g) (fun _ => degL_pos_of_mem))
    (unweightedSideInfo_hasAll hgs_all (degR g) (fun _ => degR_pos_of_mem))

theorem setSystemOf_complete [DecidableEq γ] [Nonempty β] [Nonempty γ]
    {bs : List β} {gs : List γ} {fallback : γ}
    (hbs_all : ∀ a, a ∈ bs) (hgs_all : ∀ b, b ∈ gs)
    (G : PartitionGadget γ) (g : Graph (β → γ))
    (hsat : 1 ≤ 1 - (g.toGraph projectionEval).unsatVal) :
    (setSystemOf bs gs fallback G g).optCoverSize ≤ 2 * g.edges.length := by
  obtain ⟨C, hC, hcard⟩ := (unweightedModel bs gs fallback G g).complete
    (unweightedSideInfo_hasAll hbs_all (degL g) (fun _ => degL_pos_of_mem))
    (unweightedSideInfo_hasAll hgs_all (degR g) (fun _ => degR_pos_of_mem)) hsat
  dsimp only [unweightedModel] at hC hcard
  refine (SetSystem.optCoverSize_le hC).trans ?_
  rw [Finset.card_eq_sum_ones]
  exact hcard

theorem setSystemOf_sound_of_isCover [DecidableEq γ] [Nonempty β] [Nonempty γ]
    {bs : List β} {gs : List γ} {fallback : γ} {G : PartitionGadget γ} {t : ℕ} (ht : 0 < t)
    (hsep : G.Separates t) {g : Graph (β → γ)} (hm : 0 < g.edges.length) {ρ : ℝ}
    {C : Finset (Fin (setSystemOf bs gs fallback G g).sets.length)}
    (hC : (setSystemOf bs gs fallback G g).IsCover C)
    (hcard : (C.card : ℝ) ≤ ρ * (2 * g.edges.length)) :
    (1 - 2 * ρ / t) * (4 / (t : ℝ) ^ 2) ≤ 1 - (g.toGraph projectionEval).unsatVal := by
  refine (unweightedModel bs gs fallback G g).sound_of_isCover ht hsep hm hC ?_
  dsimp only [unweightedModel]
  rwa [← Finset.card_eq_sum_ones]

theorem setSystemOf_sound [DecidableEq γ] [Nonempty β] [Nonempty γ]
    {bs : List β} {gs : List γ} {fallback : γ} (hbs_all : ∀ a, a ∈ bs) (hgs_all : ∀ b, b ∈ gs)
    {G : PartitionGadget γ} {t : ℕ} (ht : 0 < t) (hsep : G.Separates t)
    {g : Graph (β → γ)} (hm : 0 < g.edges.length) {ρ : ℝ}
    (hcard : ((setSystemOf bs gs fallback G g).optCoverSize : ℝ) ≤ ρ * (2 * g.edges.length)) :
    (1 - 2 * ρ / t) * (4 / (t : ℝ) ^ 2) ≤ 1 - (g.toGraph projectionEval).unsatVal := by
  obtain ⟨C, hC, hCcard⟩ := SetSystem.exists_isCover_optCoverSize
    (setSystemOf_coverable hbs_all hgs_all G g)
  rw [← hCcard] at hcard
  exact setSystemOf_sound_of_isCover ht hsep hm hC hcard

end Combinatorial

/-! ### Polynomial-time certificates -/

section PolyTime

private theorem computableInPolyTime_endpointVertices {β γ : Type}
    (encC : (β → γ) ↪ List Bool) {proj : Edge (β → γ) → ℕ}
    (hproj : ComputableInPolyTime proj (Edge.encoding encC) encUnary) :
    ComputableInPolyTime
      (fun g : Graph (β → γ) => (g.edges.map proj).eraseDupsBy fun a b => decide (a = b))
      (Graph.encoding encC) (encList encUnary) :=
  eraseDupsByWithInput ((ComputableInPolyTime.map hproj).comp (Graph.isPolyTime_edges id'))
    (decide_eq' (fst _ _).snd' (snd _ _))

private theorem computableInPolyTime_leftVertices {β γ : Type} (encC : (β → γ) ↪ List Bool) :
    ComputableInPolyTime (leftVertices (β := β) (γ := γ))
      (Graph.encoding encC) (encList encUnary) :=
  computableInPolyTime_endpointVertices encC (Edge.isPolyTime_src id')

private theorem computableInPolyTime_rightVertices {β γ : Type} (encC : (β → γ) ↪ List Bool) :
    ComputableInPolyTime (rightVertices (β := β) (γ := γ))
      (Graph.encoding encC) (encList encUnary) :=
  computableInPolyTime_endpointVertices encC (Edge.isPolyTime_dst id')

private theorem computableInPolyTime_countEndpoint {β γ : Type}
    (encC : (β → γ) ↪ List Bool) {proj : Edge (β → γ) → ℕ}
    (hproj : ComputableInPolyTime (fun q : (Graph (β → γ) × ℕ) × Edge (β → γ) => proj q.2)
      (encPair (encPair (Graph.encoding encC) encUnary) (Edge.encoding encC)) encUnary) :
    ComputableInPolyTime
      (fun p : Graph (β → γ) × ℕ => p.1.edges.countP fun d => decide (proj d = p.2))
      (encPair (Graph.encoding encC) encUnary) encUnary :=
  countPWithInput (Graph.isPolyTime_edges (fst _ _)) (hproj.decide_eq' ((snd _ _).comp (fst _ _)))

private theorem computableInPolyTime_degL {β γ : Type} (encC : (β → γ) ↪ List Bool) :
    ComputableInPolyTime (fun p : Graph (β → γ) × ℕ => degL p.1 p.2)
      (encPair (Graph.encoding encC) encUnary) encUnary := by
  unfold degL
  exact computableInPolyTime_countEndpoint encC (Edge.isPolyTime_src (snd _ _))

private theorem computableInPolyTime_degR {β γ : Type} (encC : (β → γ) ↪ List Bool) :
    ComputableInPolyTime (fun p : Graph (β → γ) × ℕ => degR p.1 p.2)
      (encPair (Graph.encoding encC) encUnary) encUnary := by
  unfold degR
  exact computableInPolyTime_countEndpoint encC (Edge.isPolyTime_dst (snd _ _))

private theorem computableInPolyTime_twoMulEdgesLength {β γ : Type} (encC : (β → γ) ↪ List Bool) :
    ComputableInPolyTime (fun g : Graph (β → γ) => 2 * g.edges.length)
      (Graph.encoding encC) encNat :=
  binary_mul' (const 2) (unary_to_binary.comp ((length_list _).comp (Graph.isPolyTime_edges id')))

private theorem computableInPolyTime_edgeGetD {β γ π : Type} {encC : (β → γ) ↪ List Bool}
    {encP : π ↪ List Bool} (fallback : γ) {graph : π → Graph (β → γ)} {idx : π → ℕ}
    (hgraph : ComputableInPolyTime graph encP (Graph.encoding encC))
    (hidx : ComputableInPolyTime idx encP encUnary) :
    ComputableInPolyTime (fun p => (graph p).edges.getD (idx p) ⟨0, 0, fun _ => fallback⟩)
      encP (Edge.encoding encC) := by
  have h := listGetDWithInput (Graph.isPolyTime_edges hgraph) hidx ⟨0, 0, fun _ => fallback⟩
  exact h

private theorem computableInPolyTime_leftGadgetFilter {β γ π : Type} [Finite β] [Finite γ]
    {encC : (β → γ) ↪ List Bool} {encP : π ↪ List Bool}
    (G : PartitionGadget γ) (a : β) {edge : π → Edge (β → γ)}
    (hedge : ComputableInPolyTime edge encP (Edge.encoding encC)) :
    ComputableInPolyTime
      (fun p => (List.range G.size).filter fun x => !G.mem x ((edge p).constraint a))
      encP (encList encNat) :=
  (of_finite (encIn := encC) (encOut := encList encNat)
    (fun c : β → γ => (List.range G.size).filter fun x => !G.mem x (c a))).comp
    (Edge.isPolyTime_constraint hedge)

private theorem computableInPolyTime_edgeFilterFlatMap {β γ π : Type}
    {encC : (β → γ) ↪ List Bool} {encP : π ↪ List Bool} (fallback : γ)
    {graph : π → Graph (β → γ)} {vert : π → ℕ} {proj : Edge (β → γ) → ℕ}
    {body : π × ℕ → List ℕ}
    (hgraph : ComputableInPolyTime graph encP (Graph.encoding encC))
    (hvert : ComputableInPolyTime vert encP encUnary)
    (hproj : ComputableInPolyTime proj (Edge.encoding encC) encUnary)
    (hbody : ComputableInPolyTime body (encPair encP encUnary) (encList encNat)) :
    ComputableInPolyTime
      (fun p : π => (List.range (graph p).edges.length).flatMap fun e =>
        let d := (graph p).edges.getD e ⟨0, 0, fun _ => fallback⟩
        if proj d = vert p then body (p, e) else [])
      encP (encList encNat) := by
  refine flatMapWithInput (unary_range' ((length_list _).comp (Graph.isPolyTime_edges hgraph))) ?_
  have hedge := computableInPolyTime_edgeGetD fallback (hgraph.comp (fst _ _)) (snd _ _)
  have hcond : ComputableInPolyTime
      (fun q : π × ℕ =>
        decide (proj ((graph q.1).edges.getD q.2 ⟨0, 0, fun _ => fallback⟩) = vert q.1))
      (encPair encP encUnary) encBool :=
    (hproj.comp hedge).decide_eq' (hvert.comp (fst _ _))
  simpa only [decide_eq_true_eq] using ite' hcond hbody (const [])

private theorem computableInPolyTime_weightedGround {β γ : Type} (encC : (β → γ) ↪ List Bool)
    (G : PartitionGadget γ) :
    ComputableInPolyTime (weightedGround (β := β) G) (Graph.encoding encC) (encList encNat) := by
  unfold weightedGround
  refine flatMapWithInput (unary_range' (length_list _ |>.comp (Graph.isPolyTime_edges id'))) ?_
  refine mapWithInput (const (encOut := encList encNat) (List.range G.size)) ?_
  exact binary_pair' (unary_to_binary.comp ((snd _ _).comp (fst _ _))) (snd _ _)

private theorem computableInPolyTime_weightedLeftSet {β γ : Type} [Finite β] [Finite γ]
    (encC : (β → γ) ↪ List Bool) (fallback : γ) (G : PartitionGadget γ) (a : β) :
    ComputableInPolyTime (fun p : Graph (β → γ) × ℕ => weightedLeftSet fallback G p.1 p.2 a)
      (encPair (Graph.encoding encC) encUnary) encWeightedSet := by
  refine computableInPolyTime_weightedSetMk
    (computableInPolyTime_edgeFilterFlatMap fallback (fst _ _) (snd _ _) (Edge.isPolyTime_src id')
      (body := fun q : (Graph (β → γ) × ℕ) × ℕ =>
        ((List.range G.size).filter fun x =>
          !G.mem x ((q.1.1.edges.getD q.2 ⟨0, 0, fun _ => fallback⟩).constraint a)).map
            (Nat.pair q.2))
      (mapWithInput (computableInPolyTime_leftGadgetFilter G a
        (computableInPolyTime_edgeGetD fallback ((fst _ _).comp (fst _ _)) (snd _ _)))
        (binary_pair' (unary_to_binary.comp ((snd _ _).comp (fst _ _))) (snd _ _))))
    (unary_to_binary.comp (computableInPolyTime_degL encC))

private theorem computableInPolyTime_weightedRightSet {β γ : Type}
    (encC : (β → γ) ↪ List Bool) (fallback : γ) (G : PartitionGadget γ) (b : γ) :
    ComputableInPolyTime (fun p : Graph (β → γ) × ℕ => weightedRightSet fallback G p.1 p.2 b)
      (encPair (Graph.encoding encC) encUnary) encWeightedSet :=
  computableInPolyTime_weightedSetMk
    (computableInPolyTime_edgeFilterFlatMap fallback (fst _ _) (snd _ _) (Edge.isPolyTime_dst id')
      (body := fun q : (Graph (β → γ) × ℕ) × ℕ =>
        ((List.range G.size).filter fun x => G.mem x b).map (Nat.pair q.2))
      (mapWithInput (const (encOut := encList encNat)
        ((List.range G.size).filter fun x => G.mem x b))
        (binary_pair' (unary_to_binary.comp ((snd _ _).comp (fst _ _))) (snd _ _))))
    (unary_to_binary.comp (computableInPolyTime_degR encC))

theorem computableInPolyTime_toWeightedSetCoverOf {β γ : Type} [Finite β] [Finite γ]
    (encC : (β → γ) ↪ List Bool) (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) :
    ComputableInPolyTime (toWeightedSetCoverOf bs gs fallback G)
      (Graph.encoding encC) encWeightedSetCover := by
  have mapFlat {α : Type} (verts : Graph (β → γ) → List ℕ) (ls : List α)
      (f : Graph (β → γ) → ℕ → α → WeightedSet)
      (hv : ComputableInPolyTime verts (Graph.encoding encC) (encList encUnary))
      (hf : ∀ a ∈ ls, ComputableInPolyTime (fun p : Graph (β → γ) × ℕ => f p.1 p.2 a)
        (encPair (Graph.encoding encC) encUnary) encWeightedSet) :
      ComputableInPolyTime
        (fun g => ((verts g).flatMap fun u => ls.map fun a => (u, a)).map fun p => f g p.1 p.2)
        (Graph.encoding encC) (encList encWeightedSet) := by
    have heq : (fun g => ((verts g).flatMap fun u => ls.map fun a => (u, a)).map
          fun p => f g p.1 p.2) = fun g => (verts g).flatMap fun u => ls.map fun a => f g u a := by
      funext g; simp [List.map_flatMap, List.map_map, Function.comp_def]
    rw [heq]; exact flatMapWithInput hv (mapConst ls hf)
  exact (computableInPolyTime_weightedSetSystemMk (computableInPolyTime_weightedGround encC G)
    (listAppend'
      (mapFlat leftVertices bs (weightedLeftSet fallback G) (computableInPolyTime_leftVertices encC)
        fun a _ => computableInPolyTime_weightedLeftSet encC fallback G a)
      (mapFlat rightVertices gs (weightedRightSet fallback G)
        (computableInPolyTime_rightVertices encC)
        fun b _ => computableInPolyTime_weightedRightSet encC fallback G b))).prod
    (computableInPolyTime_twoMulEdgesLength encC)

private theorem computableInPolyTime_unweightedGround {β γ : Type}
    (encC : (β → γ) ↪ List Bool) (fallback : γ) (G : PartitionGadget γ) :
    ComputableInPolyTime (unweightedGround (β := β) fallback G)
      (Graph.encoding encC) (encList encNat) := by
  unfold unweightedGround
  refine flatMapWithInput (unary_range' ((length_list _).comp (Graph.isPolyTime_edges id'))) ?_
  refine flatMapWithInput (const (encOut := encList encNat) (List.range G.size)) ?_
  have hedge := computableInPolyTime_edgeGetD (encC := encC) fallback
    (encP := encPair (encPair (Graph.encoding encC) encUnary) encNat)
    ((fst _ _).comp (fst _ _)) ((snd _ _).comp (fst _ _))
  refine flatMapWithInput (unary_range' ((computableInPolyTime_degL encC).comp
    (((fst _ _).comp (fst _ _)).prod (Edge.isPolyTime_src hedge)))) ?_
  refine mapWithInput (unary_range' ((computableInPolyTime_degR encC).comp
    (((fst _ _).comp ((fst _ _).comp (fst _ _))).prod
      (Edge.isPolyTime_dst (hedge.comp (fst _ _)))))) ?_
  exact binary_pair'
    (binary_pair'
      (unary_to_binary.comp ((snd _ _).comp ((fst _ _).comp ((fst _ _).comp (fst _ _)))))
      ((snd _ _).comp ((fst _ _).comp (fst _ _))))
    (binary_pair' (unary_to_binary.comp ((snd _ _).comp (fst _ _)))
      (unary_to_binary.comp (snd _ _)))

private theorem computableInPolyTime_unweightedEdgeBranch {β γ : Type}
    (encC : (β → γ) ↪ List Bool) (fallback : γ)
    {xs : ((Graph (β → γ) × ℕ) × ℕ) × ℕ → List ℕ}
    {otherDeg : Graph (β → γ) → ℕ → ℕ} {otherProj : Edge (β → γ) → ℕ}
    {pairCopies : ℕ × ℕ → ℕ}
    (hxs : ComputableInPolyTime xs
      (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary) encUnary)
      (encList encNat))
    (hotherDeg : ComputableInPolyTime (fun p : Graph (β → γ) × ℕ => otherDeg p.1 p.2)
      (encPair (Graph.encoding encC) encUnary) encUnary)
    (hotherProj : ComputableInPolyTime otherProj (Edge.encoding encC) encUnary)
    (hpair : ComputableInPolyTime pairCopies (encPair encNat encNat) encNat) :
    ComputableInPolyTime
      (fun q : ((Graph (β → γ) × ℕ) × ℕ) × ℕ =>
        (xs q).flatMap fun x =>
          (List.range (otherDeg q.1.1.1
            (otherProj (q.1.1.1.edges.getD q.2 ⟨0, 0, fun _ => fallback⟩)))).map fun r' =>
              Nat.pair (Nat.pair q.2 x) (pairCopies (q.1.2, r')))
      (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary) encUnary)
      (encList encNat) := by
  refine flatMapWithInput hxs ?_
  have hg : ComputableInPolyTime (fun q : (((Graph (β → γ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.1)
      (encPair (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary) encUnary)
        encNat) (Graph.encoding encC) :=
    (fst _ _).comp ((fst _ _).comp ((fst _ _).comp (fst _ _)))
  have hedge := computableInPolyTime_edgeGetD fallback hg ((snd _ _).comp (fst _ _))
  refine mapWithInput (unary_range' (hotherDeg.comp (hg.prod (hotherProj.comp hedge)))) ?_
  exact binary_pair'
    (binary_pair' (unary_to_binary.comp ((snd _ _).comp ((fst _ _).comp (fst _ _))))
      ((snd _ _).comp (fst _ _)))
    (hpair.comp ((unary_to_binary.comp
      ((snd _ _).comp ((fst _ _).comp ((fst _ _).comp (fst _ _))))).prod
      (unary_to_binary.comp (snd _ _))))

private theorem computableInPolyTime_unweightedLeftSet {β γ : Type} [Finite β] [Finite γ]
    (encC : (β → γ) ↪ List Bool) (fallback : γ) (G : PartitionGadget γ) (a : β) :
    ComputableInPolyTime
      (fun q : (Graph (β → γ) × ℕ) × ℕ => unweightedLeftSet fallback G q.1.1 q.1.2 q.2 a)
      (encPair (encPair (Graph.encoding encC) encUnary) encUnary) (encList encNat) := by
  have h := computableInPolyTime_edgeFilterFlatMap (encC := encC)
    (encP := encPair (encPair (Graph.encoding encC) encUnary) encUnary) fallback
    ((fst _ _).comp (fst _ _)) ((snd _ _).comp (fst _ _)) (Edge.isPolyTime_src id')
    (computableInPolyTime_unweightedEdgeBranch encC fallback
      (computableInPolyTime_leftGadgetFilter G a
        (computableInPolyTime_edgeGetD fallback ((fst _ _).comp ((fst _ _).comp (fst _ _)))
          (snd _ _)))
      (computableInPolyTime_degR encC) (Edge.isPolyTime_dst id') binary_pair)
  exact h

private theorem computableInPolyTime_unweightedRightSet {β γ : Type}
    (encC : (β → γ) ↪ List Bool) (fallback : γ) (G : PartitionGadget γ) (b : γ) :
    ComputableInPolyTime
      (fun q : (Graph (β → γ) × ℕ) × ℕ => unweightedRightSet fallback G q.1.1 q.1.2 q.2 b)
      (encPair (encPair (Graph.encoding encC) encUnary) encUnary) (encList encNat) := by
  have h := computableInPolyTime_edgeFilterFlatMap (encC := encC)
    (encP := encPair (encPair (Graph.encoding encC) encUnary) encUnary) fallback
    ((fst _ _).comp (fst _ _)) ((snd _ _).comp (fst _ _)) (Edge.isPolyTime_dst id')
    (computableInPolyTime_unweightedEdgeBranch encC fallback
      (const (encOut := encList encNat) ((List.range G.size).filter fun x => G.mem x b))
      (computableInPolyTime_degL encC) (Edge.isPolyTime_src id')
      (binary_pair' (snd _ _) (fst _ _)))
  exact h

theorem computableInPolyTime_toSetCoverOf {β γ : Type} [Finite β] [Finite γ]
    (encC : (β → γ) ↪ List Bool) (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) :
    ComputableInPolyTime (toSetCoverOf bs gs fallback G)
      (Graph.encoding encC) encSetCover := by
  have mapFlat {α : Type} (verts : Graph (β → γ) → List ℕ) (deg : Graph (β → γ) → ℕ → ℕ)
      (ls : List α) (f : Graph (β → γ) → ℕ → ℕ → α → List ℕ)
      (hv : ComputableInPolyTime verts (Graph.encoding encC) (encList encUnary))
      (hd : ComputableInPolyTime (fun p : Graph (β → γ) × ℕ => deg p.1 p.2)
        (encPair (Graph.encoding encC) encUnary) encUnary)
      (hf : ∀ a ∈ ls, ComputableInPolyTime
        (fun q : (Graph (β → γ) × ℕ) × ℕ => f q.1.1 q.1.2 q.2 a)
        (encPair (encPair (Graph.encoding encC) encUnary) encUnary) (encList encNat)) :
      ComputableInPolyTime
        (fun g => ((verts g).flatMap fun u => (List.range (deg g u)).flatMap fun r =>
          ls.map fun a => (u, r, a)).map fun (u, r, a) => f g u r a)
        (Graph.encoding encC) encNatSetList := by
    have heq : (fun g => ((verts g).flatMap fun u => (List.range (deg g u)).flatMap fun r =>
          ls.map fun a => (u, r, a)).map fun (u, r, a) => f g u r a) =
        fun g => (verts g).flatMap fun u => (List.range (deg g u)).flatMap fun r =>
          ls.map fun a => f g u r a := by
      funext g; simp [List.map_flatMap, List.map_map, Function.comp_def]
    rw [heq]; exact flatMapWithInput hv (flatMapWithInput (unary_range' hd) (mapConst ls hf))
  exact (computableInPolyTime_setSystemMk (computableInPolyTime_unweightedGround encC fallback G)
    (listAppend'
      (mapFlat leftVertices degL bs (unweightedLeftSet fallback G)
        (computableInPolyTime_leftVertices encC) (computableInPolyTime_degL encC)
        fun a _ => computableInPolyTime_unweightedLeftSet encC fallback G a)
      (mapFlat rightVertices degR gs (unweightedRightSet fallback G)
        (computableInPolyTime_rightVertices encC) (computableInPolyTime_degR encC)
        fun b _ => computableInPolyTime_unweightedRightSet encC fallback G b))).prod
    (computableInPolyTime_twoMulEdgesLength encC)

end PolyTime

end SetCoverReduction

/-! ### Hardness endpoints: Milestone 1 and `c ln n` gap -/

section Hardness

open SetCoverReduction

private theorem edges_length_pos_of_no_gapLabelCover {β γ : Type} [DecidableEq γ] [Nonempty β]
    [Nonempty γ] {s : ℝ} {g : Graph (β → γ)} (hg : g ∈ (GapLabelCover β γ 1 s).no) :
    0 < g.edges.length := by
  rw [GapLabelCover, PromiseProblem.mem_no_gapMax] at hg
  by_contra h
  have hunsat : (g.toGraph projectionEval).unsatVal = 0 :=
    (ConstraintGraph.unsatVal_eq_zero_iff _).2
      ⟨fun _ => (Classical.arbitrary β, Classical.arbitrary γ),
        fun i => False.elim (h (lt_of_le_of_lt (Nat.zero_le _) i.isLt))⟩
  linarith

private theorem one_div_sq_lt_gap {r : ℝ} {t : ℕ} (ht : 0 < t) (hr : 4 * r ≤ t) :
    1 / (t : ℝ) ^ 2 < (1 - 2 * r / t) * (4 / (t : ℝ) ^ 2) := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hhalf : (1 / 2 : ℝ) ≤ 1 - 2 * r / t := by
    have : 2 * r / t ≤ 1 / 2 := (div_le_div_iff₀ ht0 (by norm_num)).2 (by linarith)
    linarith
  calc 1 / (t : ℝ) ^ 2 < 2 / (t : ℝ) ^ 2 :=
        div_lt_div_of_pos_right (by norm_num) (sq_pos_of_pos ht0)
    _ = (1 / 2 : ℝ) * (4 / (t : ℝ) ^ 2) := by ring
    _ ≤ (1 - 2 * r / t) * (4 / (t : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hhalf (by positivity)

private theorem polyTimeReducible_GapLabelCover_aux
    {β γ : Type} [Finite β] [Nonempty β] [Finite γ] [DecidableEq γ] [Nonempty γ]
    (encC : (β → γ) ↪ List Bool) {Sys : Type} (encSys : Sys ↪ List Bool)
    (optCost : Sys → ℕ) (Coverable : Sys → Prop)
    (GapSys : ℝ → PromiseProblem (Sys × ℕ))
    (hGapYes : ∀ {r X k}, (X, k) ∈ (GapSys r).yes ↔ Coverable X ∧ optCost X ≤ k)
    (hGapNo : ∀ {r X k},
      (X, k) ∈ (GapSys r).no ↔ Coverable X ∧ r * k ≤ optCost X ∧ (k : ℝ) < r * k)
    (toSys : List β → List γ → γ → PartitionGadget γ → Graph (β → γ) → Sys)
    (htop : ∀ bs gs fallback G,
      ComputableInPolyTime (fun g => (toSys bs gs fallback G g, 2 * g.edges.length))
        (Graph.encoding encC) (encPair encSys encNat))
    (hcov : ∀ {bs gs} fallback G g, (∀ a, a ∈ bs) → (∀ b, b ∈ gs) →
      Coverable (toSys bs gs fallback G g))
    (hcomplete : ∀ {bs gs} fallback G g, (∀ a, a ∈ bs) → (∀ b, b ∈ gs) →
      1 ≤ 1 - (g.toGraph projectionEval).unsatVal →
      optCost (toSys bs gs fallback G g) ≤ 2 * g.edges.length)
    (hsound : ∀ {bs gs} fallback G {t : ℕ}, 0 < t → G.Separates t →
      ∀ {g : Graph (β → γ)}, 0 < g.edges.length → ∀ {ρ : ℝ},
      (∀ a, a ∈ bs) → (∀ b, b ∈ gs) →
      (optCost (toSys bs gs fallback G g) : ℝ) ≤ ρ * (2 * g.edges.length) →
      (1 - 2 * ρ / t) * (4 / (t : ℝ) ^ 2) ≤ 1 - (g.toGraph projectionEval).unsatVal)
    {G : PartitionGadget γ} {t : ℕ} (ht : 0 < t)
    (hsep : G.Separates t) {r s : ℝ} (hr : 1 < r)
    (hs : s < (1 - 2 * r / t) * (4 / (t : ℝ) ^ 2)) :
    PromiseProblem.PolyTimeReducible (Graph.encoding encC) (encPair encSys encNat)
      (GapLabelCover β γ 1 s) (GapSys r) := by
  classical
  let _ := Fintype.ofFinite β; let _ := Fintype.ofFinite γ
  have hbs (a : β) : a ∈ Finset.univ.toList := Finset.mem_toList.2 (Finset.mem_univ a)
  have hgs (b : γ) : b ∈ Finset.univ.toList := Finset.mem_toList.2 (Finset.mem_univ b)
  refine ⟨fun g => (toSys _ _ (Classical.arbitrary γ) G g, 2 * g.edges.length),
    htop _ _ _ G, fun g hg => hGapYes.2 ⟨hcov _ G g hbs hgs,
      hcomplete _ G g hbs hgs (PromiseProblem.mem_yes_gapMax.1 hg)⟩, fun g hg => ?_⟩
  have hm := edges_length_pos_of_no_gapLabelCover hg
  rw [GapLabelCover, PromiseProblem.mem_no_gapMax] at hg
  refine hGapNo.2 ⟨hcov _ G g hbs hgs, ?_,
    lt_mul_of_one_lt_left (by exact_mod_cast (by omega : 0 < 2 * g.edges.length)) hr⟩
  by_contra hlt; push Not at hlt; push_cast at hlt
  linarith [hsound _ G ht hsep hm hbs hgs (ρ := r) hlt.le]

/-- **Gap-preserving polynomial-time reduction from `GapLabelCover` to `GapWeightedSetCover`**. -/
theorem polyTimeReducible_GapLabelCover_GapWeightedSetCover
    {β γ : Type} [Finite β] [Nonempty β] [Finite γ] [DecidableEq γ] [Nonempty γ]
    (encC : (β → γ) ↪ List Bool) {G : PartitionGadget γ} {t : ℕ} (ht : 0 < t)
    (hsep : G.Separates t) {r s : ℝ} (hr : 1 < r)
    (hs : s < (1 - 2 * r / t) * (4 / (t : ℝ) ^ 2)) :
    PromiseProblem.PolyTimeReducible (Graph.encoding encC) encWeightedSetCover
      (GapLabelCover β γ 1 s) (GapWeightedSetCover r) :=
  polyTimeReducible_GapLabelCover_aux encC encWeightedSetSystem
    WeightedSetSystem.optCoverWeight WeightedSetSystem.Coverable GapWeightedSetCover
    (fun {r X k} => by rw [GapWeightedSetCover, mem_yes_GapWeightedSetCoverFn])
    (fun {r X k} => by rw [GapWeightedSetCover, mem_no_GapWeightedSetCoverFn])
    weightedSetSystemOf (computableInPolyTime_toWeightedSetCoverOf encC)
    (fun fallback G g hbs hgs => weightedSetSystemOf_coverable hbs hgs G g)
    (fun fallback G g hbs hgs => weightedSetSystemOf_complete hbs hgs G g)
    (fun fallback G _ ht hs _ hm _ hbs hgs => weightedSetSystemOf_sound hbs hgs ht hs hm)
    ht hsep hr hs

/-- **Gap-preserving polynomial-time reduction from `GapLabelCover` to `GapSetCover`**. -/
theorem polyTimeReducible_GapLabelCover_GapSetCover
    {β γ : Type} [Finite β] [Nonempty β] [Finite γ] [DecidableEq γ] [Nonempty γ]
    (encC : (β → γ) ↪ List Bool) {G : PartitionGadget γ} {t : ℕ} (ht : 0 < t)
    (hsep : G.Separates t) {r s : ℝ} (hr : 1 < r)
    (hs : s < (1 - 2 * r / t) * (4 / (t : ℝ) ^ 2)) :
    PromiseProblem.PolyTimeReducible (Graph.encoding encC) encSetCover
      (GapLabelCover β γ 1 s) (GapSetCover r) :=
  polyTimeReducible_GapLabelCover_aux encC encSetSystem
    SetSystem.optCoverSize SetSystem.Coverable GapSetCover
    (fun {r X k} => by rw [GapSetCover, mem_yes_GapSetCoverFn])
    (fun {r X k} => by rw [GapSetCover, mem_no_GapSetCoverFn])
    setSystemOf (computableInPolyTime_toSetCoverOf encC)
    (fun fallback G g hbs hgs => setSystemOf_coverable hbs hgs G g)
    (fun fallback G g hbs hgs => setSystemOf_complete hbs hgs G g)
    (fun fallback G _ ht hs _ hm _ hbs hgs => setSystemOf_sound hbs hgs ht hs hm)
    ht hsep hr hs

/-- **Milestone 1 (unweighted Set Cover):** `GapSetCover c` is `NP`-hard for every constant
`c > 1`, unconditionally from `exists_GapLabelCover_npHard` and `boolCubeGadget`. -/
theorem GapSetCover_npHard {c : ℝ} (hc : 1 < c) :
    PromiseProblem.NPHard encSetCover (GapSetCover c) := by
  let t : ℕ := Nat.ceil (4 * c) + 4
  have ht4 : (4 : ℝ) ≤ t := by exact_mod_cast (Nat.le_add_left 4 _)
  have ht_ge : 4 * c ≤ t := (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_add_right _ 4)
  have hδ1 : (1 : ℝ) / (t : ℝ) ^ 2 < 1 := (div_lt_one (by positivity)).2 (by nlinarith)
  obtain ⟨k, _, hLC⟩ := exists_GapLabelCover_npHard (by positivity : (0 : ℝ) < 1 / t ^ 2) hδ1
  exact hLC.trans <| polyTimeReducible_GapLabelCover_GapSetCover
    (β := Fin k → (Bool × (Fin 6 → Bool)) × (Bool × (Fin 6 → Bool)))
    (γ := Fin k → Bool × (Fin 6 → Bool))
    (encPi (encPi (encPair encBool (encPi encBool))))
    (by positivity) (boolCubeGadget_separates _ t) hc (one_div_sq_lt_gap (by positivity) ht_ge)

/-- **Milestone 1 (weighted Set Cover):** `GapWeightedSetCover c` is `NP`-hard for every
constant `c > 1`. -/
theorem GapWeightedSetCover_npHard {c : ℝ} (hc : 1 < c) :
    PromiseProblem.NPHard encWeightedSetCover (GapWeightedSetCover c) :=
  (GapSetCover_npHard hc).trans (polyTimeReducible_GapSetCover_GapWeightedSetCover c)

/-- If `P ≠ NP`, `GapSetCover c` does not lie in `PromiseP` for any `c > 1`. -/
theorem GapSetCover_notMem_PromiseP {c : ℝ} (hc : 1 < c) {α : Type} {enc : α ↪ List Bool}
    (hpne : P enc ≠ NP enc) : GapSetCover c ∉ PromiseP encSetCover :=
  (GapSetCover_npHard hc).notMem_PromiseP hpne

/-- If `P ≠ NP`, `GapWeightedSetCover c` does not lie in `PromiseP` for any `c > 1`. -/
theorem GapWeightedSetCover_notMem_PromiseP {c : ℝ} (hc : 1 < c) {α : Type}
    {enc : α ↪ List Bool} (hpne : P enc ≠ NP enc) :
    GapWeightedSetCover c ∉ PromiseP encWeightedSetCover :=
  (GapWeightedSetCover_npHard hc).notMem_PromiseP hpne

/-- No polynomial-time constant-factor approximation algorithm exists for unweighted Set Cover
unless `P = NP`. -/
theorem P_eq_NP_of_setCover_approx_const {A : SetSystem → List ℕ} {c : ℝ} (hc0 : 0 ≤ c)
    (hA : ComputableInPolyTime A encSetSystem (encList encNat))
    (happrox : minSetCover.IsApprox (fun _ => c) A) {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc :=
  P_eq_NP_of_setCover_approx (GapSetCover_npHard (by linarith : 1 < c + 2)) hc0
    (by linarith : c < c + 2) hA happrox enc

/-- No polynomial-time constant-factor approximation algorithm exists for weighted Set Cover
unless `P = NP`. -/
theorem P_eq_NP_of_weightedSetCover_approx_const {A : WeightedSetSystem → List ℕ} {c : ℝ}
    (hc0 : 0 ≤ c) (hA : ComputableInPolyTime A encWeightedSetSystem (encList encNat))
    (happrox : minWeightedSetCover.IsApprox (fun _ => c) A) {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc :=
  P_eq_NP_of_weightedSetCover_approx (GapWeightedSetCover_npHard (by linarith : 1 < c + 2)) hc0
    (by linarith : c < c + 2) hA happrox enc

/-- Explicit lower threshold on the separation parameter `t` in terms of `c`, polynomial blowup
degree `p`, edge count `m`, and label cardinality `cardGamma` for the `c * Real.log n` gap
reductions. Asymptotically this threshold grows as `O(p * log m + log log cardGamma)` for fixed
`0 < c < 1 / (4 * log 2)`. -/
@[expose] noncomputable def logGapThreshold (c : ℝ) (p m cardGamma : ℕ) : ℕ :=
  let gap : ℝ := 1 - 4 * Real.log 2 * c
  let δ : ℝ := gap / (8 * c)
  let α : ℝ := δ / 2
  let A₀ : ℕ := Nat.clog 2 (2 * cardGamma + 1)
  let B : ℝ := (p : ℝ) * Real.log m + Real.log ((A₀ + 1 : ℕ) : ℝ)
  let T₀ : ℕ := Nat.ceil (max (α - 1 - Real.log α) 0 / α) + 1
  let T₁ : ℕ := Nat.ceil (1 / (c * Real.log 2)) + 1
  let T₂ : ℕ := Nat.ceil (max B 0 / δ) + 1
  max (max 4 T₀) (max T₁ T₂)

/-- `logGapThreshold` is always at least `4`. -/
theorem four_le_logGapThreshold (c : ℝ) (p m cardGamma : ℕ) :
    4 ≤ logGapThreshold c p m cardGamma :=
  le_trans (le_max_left 4 _) (le_max_left _ _)

private theorem le_mul_of_ceil_succ_le {x a : ℝ} {t : ℕ} (ha : 0 < a)
    (ht : Nat.ceil (max x 0 / a) + 1 ≤ t) : x ≤ a * t := by
  have hdiv : max x 0 / a ≤ t :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (Nat.le_add_right _ 1) ht)
  exact (le_max_left x 0).trans ((div_le_iff₀ ha).1 hdiv |>.trans_eq (mul_comm _ _))

private theorem logGapThreshold_spec {c : ℝ} {p m cardGamma t : ℕ}
    (hc0 : 0 < c) (hc : c < 1 / (4 * Real.log 2))
    (ht : logGapThreshold c p m cardGamma ≤ t) :
    4 ≤ t ∧ 1 < c * (t * Real.log 2) ∧
      c * (((p : ℝ) * Real.log m +
        Real.log ((Nat.clog 2 (2 * cardGamma + 1) + 1 : ℕ) : ℝ)) +
        Real.log ((t : ℝ) + 1) + t * Real.log 2) ≤ (t : ℝ) / 4 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgap : 0 < 1 - 4 * Real.log 2 * c := by
    have := (lt_div_iff₀ (by positivity)).1 hc; linarith
  let δ : ℝ := (1 - 4 * Real.log 2 * c) / (8 * c)
  have hδ : 0 < δ := by positivity
  have hα : 0 < δ / 2 := by positivity
  have htT0 : Nat.ceil (max (δ / 2 - 1 - Real.log (δ / 2)) 0 / (δ / 2)) + 1 ≤ t :=
    (le_max_right 4 _).trans ((le_max_left _ _).trans ht)
  have htT1 : Nat.ceil (1 / (c * Real.log 2)) + 1 ≤ t :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htT2 : Nat.ceil (max ((p : ℝ) * Real.log m +
      Real.log ((Nat.clog 2 (2 * cardGamma + 1) + 1 : ℕ) : ℝ)) 0 / δ) + 1 ≤ t :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  refine ⟨(four_le_logGapThreshold c p m cardGamma).trans ht, ?_, ?_⟩
  · have ht1 : 1 / (c * Real.log 2) < t :=
      (Nat.le_ceil _).trans_lt (by exact_mod_cast Nat.lt_of_succ_le htT1)
    linarith [(div_lt_iff₀ (mul_pos hc0 hlog2)).1 ht1]
  · have h1 := Real.log_le_sub_one_of_pos (mul_pos hα (by positivity : (0 : ℝ) < t + 1))
    rw [Real.log_mul hα.ne' (by positivity)] at h1
    have hlogt : Real.log ((t : ℝ) + 1) ≤ δ * t := by
      have := le_mul_of_ceil_succ_le hα htT0; linarith
    have hBt := le_mul_of_ceil_succ_le hδ htT2
    calc c * (_ + Real.log ((t : ℝ) + 1) + t * Real.log 2)
        ≤ c * (2 * δ * t + t * Real.log 2) := mul_le_mul_of_nonneg_left (by linarith) hc0.le
      _ = (t : ℝ) / 4 := by dsimp only [δ]; field_simp [hc0.ne']; ring

private theorem log_gap_ratio_bounds {c : ℝ} (hc0 : 0 < c) {t m len p A₀ : ℕ}
    (hm : 0 < m) (hlow_len : 2 ^ t ≤ len) (hup_len : len ≤ m ^ p * (2 ^ t * (t * A₀ + 1)))
    (hlog_low : 1 < c * (t * Real.log 2))
    (hlog_high : c * ((p : ℝ) * Real.log m + Real.log ((A₀ + 1 : ℕ) : ℝ) +
      Real.log ((t : ℝ) + 1) + t * Real.log 2) ≤ (t : ℝ) / 4) :
    1 < c * Real.log len ∧ c * Real.log len ≤ (t : ℝ) / 4 := by
  have hlow_real : (2 : ℝ) ^ t ≤ len := by exact_mod_cast hlow_len
  have hlen_pos : (0 : ℝ) < len := lt_of_lt_of_le (by positivity) hlow_real
  have hlog_ge : t * Real.log 2 ≤ Real.log len :=
    (Real.log_pow 2 t).symm ▸ Real.log_le_log (by positivity) hlow_real
  have hup_nat : len ≤ m ^ p * (2 ^ t * ((t + 1) * (A₀ + 1))) :=
    hup_len.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
      (by rw [add_mul, mul_add, one_mul, mul_one]; omega)))
  have hup_real : (len : ℝ) ≤ (m : ℝ) ^ p * ((2 : ℝ) ^ t * (((t : ℝ) + 1) * ((A₀ + 1 : ℕ) : ℝ))) :=
    by exact_mod_cast hup_nat
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have hA_pos : (0 : ℝ) < ((A₀ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos A₀
  have hlog_le : Real.log len ≤ ((p : ℝ) * Real.log m + Real.log ((A₀ + 1 : ℕ) : ℝ)) +
      Real.log ((t : ℝ) + 1) + t * Real.log 2 := by
    have h := Real.log_le_log hlen_pos hup_real
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) hA_pos.ne', Real.log_pow, Real.log_pow] at h
    linarith
  exact ⟨hlog_low.trans_le (mul_le_mul_of_nonneg_left hlog_ge hc0.le),
    (mul_le_mul_of_nonneg_left hlog_le hc0.le).trans (by simpa only [add_assoc] using hlog_high)⟩

private theorem exists_log_gap_aux {β γ : Type}
    [Fintype γ] [DecidableEq γ]
    {Sys : Type} (groundLen optCost : Sys → ℕ)
    (Coverable : Sys → Prop) (memYes memNo : Sys → ℕ → (Sys → ℝ) → Prop)
    (hYes_iff : ∀ X k r, memYes X k r ↔ Coverable X ∧ optCost X ≤ k)
    (hNo_iff : ∀ X k r, memNo X k r ↔ Coverable X ∧ r X * k ≤ optCost X ∧ (k : ℝ) < r X * k)
    {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / (4 * Real.log 2))
    (g : Graph (β → γ)) (hm : 0 < List.length g.edges) (p : ℕ)
    (sys : PartitionGadget γ → Sys)
    (hcov : ∀ G, Coverable (sys G))
    (hlow : ∀ G, G.size ≤ groundLen (sys G))
    (hup : ∀ G, groundLen (sys G) ≤ List.length g.edges ^ p * G.size)
    (hcomplete : ∀ G, 1 ≤ 1 - ConstraintGraph.unsatVal (g.toGraph projectionEval) →
      optCost (sys G) ≤ 2 * List.length g.edges)
    (hsound : ∀ (G : PartitionGadget γ) {t : ℕ}, 0 < t → G.Separates t →
      ∀ {ρ : ℝ}, (optCost (sys G) : ℝ) ≤ ρ * (2 * List.length g.edges) →
        (1 - 2 * ρ / t) * (4 / (t : ℝ) ^ 2) ≤
          1 - ConstraintGraph.unsatVal (g.toGraph projectionEval))
    {t : ℕ} (ht : logGapThreshold c p g.edges.length (Fintype.card γ) ≤ t) :
    4 ≤ t ∧ ∃ G : PartitionGadget γ, G.Separates t ∧
      G.size = 2 ^ t * (t * Nat.clog 2 (2 * Fintype.card γ + 1) + 1) ∧
      Coverable (sys G) ∧
      (1 ≤ 1 - ConstraintGraph.unsatVal (g.toGraph projectionEval) →
        memYes (sys G) (2 * List.length g.edges) (fun Y => c * Real.log (groundLen Y))) ∧
      (1 - ConstraintGraph.unsatVal (g.toGraph projectionEval) ≤ 1 / (t : ℝ) ^ 2 →
        memNo (sys G) (2 * List.length g.edges) (fun Y => c * Real.log (groundLen Y))) := by
  obtain ⟨ht4, hlog_low, hlog_high⟩ := logGapThreshold_spec hc0 hc ht
  obtain ⟨G, hsep, hGsize⟩ := exists_small_partitionGadget γ t
  refine ⟨ht4, G, hsep, hGsize, hcov G,
    fun hyes => (hYes_iff ..).2 ⟨hcov G, hcomplete G hyes⟩, fun hno => ?_⟩
  obtain ⟨hratio_gt, hratio_le⟩ := log_gap_ratio_bounds hc0 hm
    ((hGsize ▸ Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans (hlow G))
    (hGsize ▸ hup G) hlog_low (by simpa only [add_assoc] using hlog_high)
  refine (hNo_iff ..).2 ⟨hcov G, ?_,
    lt_mul_of_one_lt_left (by exact_mod_cast (by omega : 0 < 2 * g.edges.length)) hratio_gt⟩
  by_contra hlt; push Not at hlt; push_cast at hlt
  have hsound' := hsound G (by omega) hsep (ρ := c * Real.log (groundLen (sys G))) hlt.le
  exact absurd (hsound'.trans hno) (not_le_of_gt (one_div_sq_lt_gap (by omega) (by linarith)))

/-- **Per-instance logarithmic gap for weighted Set Cover (`c * ln n`)** for any `0 < c < 1 /
(4 * log 2)` and any separation parameter `t ≥ logGapThreshold c 1 g.edges.length |γ|` (using the
`O(t * 2 ^ t * log |γ|)` separating partition gadget `exists_small_partitionGadget`), conditional
on `1 - unsatVal ≤ 1 / t ^ 2`. Upgrading this conditional reduction to hardness requires either
super-constant parallel repetition via a quasi-polynomial reduction (assuming
`NP ⊈ DTIME(n^{O(log log n)})`, not `P ≠ NP` alone) or polynomial-time low-soundness Label Cover
such as Dinur–Steurer (for `P ≠ NP`). -/
theorem exists_weightedSetCover_log_gap {β γ : Type} [Fintype β] [Nonempty β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / (4 * Real.log 2))
    (g : Graph (β → γ)) (hm : 0 < List.length g.edges)
    {t : ℕ} (ht : logGapThreshold c 1 g.edges.length (Fintype.card γ) ≤ t) :
    4 ≤ t ∧ ∃ G : PartitionGadget γ, G.Separates t ∧
      G.size = 2 ^ t * (t * Nat.clog 2 (2 * Fintype.card γ + 1) + 1) ∧
      let bs : List β := Finset.univ.toList
      let gs : List γ := Finset.univ.toList
      let W := weightedSetSystemOf bs gs (Classical.arbitrary γ) G g
      let k := 2 * List.length g.edges
      W.Coverable ∧
      (1 ≤ 1 - ConstraintGraph.unsatVal (g.toGraph projectionEval) →
        (W, k) ∈ (GapWeightedSetCoverFn fun X => c * Real.log (List.length X.ground)).yes) ∧
      (1 - ConstraintGraph.unsatVal (g.toGraph projectionEval) ≤ 1 / (t : ℝ) ^ 2 →
        (W, k) ∈ (GapWeightedSetCoverFn fun X => c * Real.log (List.length X.ground)).no) := by
  let bs : List β := Finset.univ.toList
  let gs : List γ := Finset.univ.toList
  have hbs (a : β) : a ∈ bs := Finset.mem_toList.2 (Finset.mem_univ a)
  have hgs (b : γ) : b ∈ gs := Finset.mem_toList.2 (Finset.mem_univ b)
  obtain ⟨ht4, G, hsep, hGsize, hcov, hyes, hno⟩ := exists_log_gap_aux
    (fun X => X.ground.length) WeightedSetSystem.optCoverWeight
    WeightedSetSystem.Coverable (fun X k r => (X, k) ∈ (GapWeightedSetCoverFn r).yes)
    (fun X k r => (X, k) ∈ (GapWeightedSetCoverFn r).no)
    (fun _ _ _ => mem_yes_GapWeightedSetCoverFn) (fun _ _ _ => mem_no_GapWeightedSetCoverFn)
    hc0 hc g hm 1 (fun G => weightedSetSystemOf bs gs (Classical.arbitrary γ) G g)
    (fun G => weightedSetSystemOf_coverable hbs hgs G g)
    (fun G => by rw [weightedSetSystemOf_ground_length]; exact Nat.le_mul_of_pos_left _ hm)
    (fun G => by rw [pow_one, weightedSetSystemOf_ground_length])
    (fun G h => weightedSetSystemOf_complete hbs hgs G g h)
    (fun G _ ht hs _ hwt => weightedSetSystemOf_sound hbs hgs ht hs hm hwt) ht
  exact ⟨ht4, G, hsep, hGsize, hcov, hyes, hno⟩

/-- **Per-instance logarithmic gap for unweighted Set Cover (`c * ln n`)** for any `0 < c < 1 /
(4 * log 2)` and any separation parameter `t ≥ logGapThreshold c 3 g.edges.length |γ|`, conditional
on Label Cover soundness `≤ 1 / t ^ 2`. Upgrading this conditional reduction beyond the
constant-round `exists_GapLabelCover_npHard` base requires either super-constant parallel repetition
via a quasi-polynomial reduction (assuming `NP ⊈ DTIME(n^{O(log log n)})`, not `P ≠ NP` alone) or
polynomial-time low-soundness Label Cover such as Dinur–Steurer (for `P ≠ NP`). -/
theorem exists_setCover_log_gap {β γ : Type} [Fintype β] [Nonempty β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / (4 * Real.log 2))
    (g : Graph (β → γ)) (hm : 0 < List.length g.edges)
    {t : ℕ} (ht : logGapThreshold c 3 g.edges.length (Fintype.card γ) ≤ t) :
    4 ≤ t ∧ ∃ G : PartitionGadget γ, G.Separates t ∧
      G.size = 2 ^ t * (t * Nat.clog 2 (2 * Fintype.card γ + 1) + 1) ∧
      let bs : List β := Finset.univ.toList
      let gs : List γ := Finset.univ.toList
      let S := setSystemOf bs gs (Classical.arbitrary γ) G g
      let k := 2 * List.length g.edges
      S.Coverable ∧
      (1 ≤ 1 - ConstraintGraph.unsatVal (g.toGraph projectionEval) →
        (S, k) ∈ (GapSetCoverFn fun X => c * Real.log (List.length X.ground)).yes) ∧
      (1 - ConstraintGraph.unsatVal (g.toGraph projectionEval) ≤ 1 / (t : ℝ) ^ 2 →
        (S, k) ∈ (GapSetCoverFn fun X => c * Real.log (List.length X.ground)).no) := by
  let bs : List β := Finset.univ.toList
  let gs : List γ := Finset.univ.toList
  have hbs (a : β) : a ∈ bs := Finset.mem_toList.2 (Finset.mem_univ a)
  have hgs (b : γ) : b ∈ gs := Finset.mem_toList.2 (Finset.mem_univ b)
  obtain ⟨ht4, G, hsep, hGsize, hcov, hyes, hno⟩ := exists_log_gap_aux
    (fun X => X.ground.length) SetSystem.optCoverSize SetSystem.Coverable
    (fun X k r => (X, k) ∈ (GapSetCoverFn r).yes) (fun X k r => (X, k) ∈ (GapSetCoverFn r).no)
    (fun _ _ _ => mem_yes_GapSetCoverFn) (fun _ _ _ => mem_no_GapSetCoverFn)
    hc0 hc g hm 3 (fun G => setSystemOf bs gs (Classical.arbitrary γ) G g)
    (fun G => setSystemOf_coverable hbs hgs G g)
    (fun _ => setSystemOf_ground_length_ge hm) (fun _ => setSystemOf_ground_length_le)
    (fun G h => setSystemOf_complete hbs hgs G g h)
    (fun G _ ht hs _ hcard => setSystemOf_sound hbs hgs ht hs hm hcard) ht
  exact ⟨ht4, G, hsep, hGsize, hcov, hyes, hno⟩

end Hardness

end Cslib.Complexity
