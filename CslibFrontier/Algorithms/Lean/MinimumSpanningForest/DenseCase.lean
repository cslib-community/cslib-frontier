/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.GrowingPartition
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Bounded-frontier Prim passes for the dense quotient

The dense-case subroutine of [PettieRamachandran2002], §2.3, can use the tree-growing
passes of [FredmanTarjan1987], §5. Within a pass an old vertex has one priority-queue item,
even if several edges can reach it. Growth ends when the queue exceeds its size bound,
when a marked vertex is reached, or when no edge leaves the growing tree. All cuts in a
pass belong to the same graph. Edges chosen across those cuts can be contracted together.

This graph-level algorithm recomputes the set of queue vertices from the boundary.
It establishes correctness and termination. The implementation of the pass by Fibonacci
heaps and its machine instruction bound are separate obligations.
-/

public section

namespace Cslib.Multigraph.PettieRamachandran.DenseCase

open Finset PrimPartition.SearchState

variable {V E W : Type*} [LinearOrder W] [DecidableEq V] [DecidableEq E]

/-- One priority-queue item for each *outside vertex* adjacent to the growing component.
Parallel edges to the same outside vertex contribute only one item. -/
noncomputable def frontier (ends : E → Sym2 V) (S : Finset E) (C : Finset V) : Finset V := by
  classical
  exact ((S.filter (fun e => e ∈ (toGraph ends).edgeCut (C : Set V))).biUnion
    (fun e => (ends e).toFinset)) \ C

/-- Grow a new tree during one fixed-topology pass. Return its marked vertices and the labels
of the minimum boundary edges used to grow it. -/
noncomputable def grow (ends : E → Sym2 V) (S : Finset E) (w : E → W)
    (limit : ℕ) (marked : Finset V) : ℕ → Finset V → Finset V × Finset E
  | 0, C => (C, ∅)
  | fuel + 1, C =>
    if (frontier ends S C).card > limit then (C, ∅) else
      match minExit ends S C w with
      | none => (C, ∅)
      | some x =>
        let more := insert x.outside C
        if x.outside ∈ marked then (more, {x.edge}) else
          let rest := grow ends S w limit marked fuel more
          (rest.1, insert x.edge rest.2)

omit [DecidableEq V] [DecidableEq E] in
private theorem exit_safe {ends : E → Sym2 V} {w : E → W} {S : Finset E} {C : Finset V}
    (x : Exit ends S C w) : x.edge ∈ msf ends w S := by
  apply mem_msf_of_mem_edgeCut w x.active
    (Graph.mem_edgeCut_iff.mpr ⟨x.inside, x.outside, x.inc, x.left_mem, x.right_notMem⟩)
  intro f hf cut
  obtain ⟨a, b, inc, ha, hb⟩ := Graph.mem_edgeCut_iff.mp cut
  exact x.minimum f hf a ha b hb inc

private theorem grow_safe (ends : E → Sym2 V) (S : Finset E) (w : E → W)
    (limit : ℕ) (marked : Finset V) (fuel : ℕ) (C : Finset V) :
    (grow ends S w limit marked fuel C).2 ⊆ msf ends w S := by
  induction fuel generalizing C with
  | zero => exact empty_subset _
  | succ n ih =>
    rw [grow]
    split
    · exact empty_subset _
    · split
      · exact empty_subset _
      next x _ =>
        dsimp only
        split
        · exact singleton_subset_iff.mpr (exit_safe x)
        · exact insert_subset (exit_safe x) (ih _)

/-- Grow from each still-unmarked seed, remembering marks until the end of the pass. -/
private noncomputable def scan (ends : E → Sym2 V) (S : Finset E) (w : E → W)
    (limit fuel : ℕ) (marked : Finset V) : List V → Finset E
  | [] => ∅
  | v :: vs =>
    if v ∈ marked then scan ends S w limit fuel marked vs else
      let r := grow ends S w limit marked fuel {v}
      r.2 ∪ scan ends S w limit fuel (marked ∪ r.1) vs

private theorem scan_safe (ends : E → Sym2 V) (S : Finset E) (w : E → W)
    (limit fuel : ℕ) (marked : Finset V) (vs : List V) :
    scan ends S w limit fuel marked vs ⊆ msf ends w S := by
  induction vs generalizing marked with
  | nil => exact empty_subset _
  | cons v vs ih =>
    rw [scan]
    split
    · exact ih _
    · exact union_subset (grow_safe ..) (ih _)

private noncomputable def firstSeed (ends : E → Sym2 V) (S : Finset E)
    (h : (support ends S).Nonempty) : V :=
  ((support ends S).exists_min_image (fun v => (frontier ends S {v}).card) h).choose

omit [DecidableEq E] in
private theorem seed_mem (ends : E → Sym2 V) (S : Finset E) (h : (support ends S).Nonempty) :
    firstSeed ends S h ∈ support ends S :=
  ((support ends S).exists_min_image (fun v => (frontier ends S {v}).card) h).choose_spec.1

omit [DecidableEq V] [DecidableEq E] in
private theorem seed_cut {ends : E → Sym2 V} {S : Finset E} {v : V} (hv : v ∈ support ends S) :
    ∃ e ∈ S, e ∈ (toGraph ends).edgeCut (({v} : Finset V) : Set V) := by
  obtain ⟨e, he, nonloop, hv⟩ := mem_support.mp hv
  obtain ⟨a, b, inc⟩ : ∃ a b, ends e = s(a, b) :=
    Sym2.inductionOn (ends e) fun a b => ⟨a, b, rfl⟩
  have ab : a ≠ b := by simpa [inc] using nonloop
  rw [inc, Sym2.mem_iff] at hv
  refine ⟨e, he, Graph.mem_edgeCut_iff.mpr ?_⟩
  rcases hv with rfl | rfl
  · exact ⟨_, _, inc, by simp, by simpa using ab.symm⟩
  · exact ⟨_, _, inc.trans Sym2.eq_swap, by simp, by simpa using ab⟩

omit [DecidableEq E] in
private theorem frontier_card_le_incident (ends : E → Sym2 V) (S : Finset E) (v : V) :
    (frontier ends S {v}).card ≤ (S.filter (fun e => v ∈ ends e)).card := by
  classical
  let other (e : E) := if h : v ∈ ends e then h.other else v
  apply le_trans (card_le_card (t := (S.filter (fun e => v ∈ ends e)).image other) ?_) card_image_le
  intro u hu
  obtain ⟨hunion, different⟩ := mem_sdiff.mp hu
  obtain ⟨e, hcut, hu⟩ := mem_biUnion.mp hunion
  obtain ⟨he, cut⟩ := mem_filter.mp hcut
  obtain ⟨a, b, inc, ha, hb⟩ := Graph.mem_edgeCut_iff.mp cut
  have av : a = v := by simpa using ha
  subst a
  change ends e = s(v, b) at inc
  have hve : v ∈ ends e := by simp [inc]
  refine mem_image.mpr ⟨e, mem_filter.mpr ⟨he, hve⟩, ?_⟩
  have hu' : u = b := by
    rw [inc, Sym2.mem_toFinset, Sym2.mem_iff] at hu
    exact hu.resolve_left (by simpa using different)
  rw [hu', show other e = hve.other by simp [other, hve]]
  exact Sym2.congr_right.mp ((Sym2.other_spec hve).trans inc)

omit [DecidableEq E] in
/-- The minimum initial queue size is at most the average number of incident edge labels.
Each original edge can pay for at most two incidences, even with parallel edges or loops. -/
private theorem seed_average (ends : E → Sym2 V) (S : Finset E) (h : (support ends S).Nonempty) :
    (support ends S).card * (frontier ends S {firstSeed ends S h}).card ≤ 2 * S.card := by
  classical
  let X := support ends S
  let d := (frontier ends S {firstSeed ends S h}).card
  have least : ∀ v ∈ X, d ≤ (frontier ends S {v}).card :=
    ((support ends S).exists_min_image (fun v => (frontier ends S {v}).card) h).choose_spec.2
  calc
    X.card * d = ∑ _v ∈ X, d := by simp
    _ ≤ ∑ v ∈ X, (S.filter (fun e => v ∈ ends e)).card :=
      sum_le_sum fun v hv => (least v hv).trans (frontier_card_le_incident ends S v)
    _ = ∑ e ∈ S, (X.filter (fun v => v ∈ ends e)).card := by
      simp only [card_filter]
      exact sum_comm
    _ ≤ ∑ _e ∈ S, 2 := by
      apply sum_le_sum
      intro e _
      apply le_trans (card_le_card (t := (ends e).toFinset) ?_)
      · rw [Sym2.card_toFinset]
        split <;> decide
      · intro v hv
        exact Sym2.mem_toFinset.mpr (mem_filter.mp hv).2
    _ = 2 * S.card := by simp [Nat.mul_comm]

/-- The queue bound uses the original edge count and the current number of old vertices.
The first seed is chosen to minimize the number of distinct incident neighbors. -/
noncomputable def queueLimit (originalEdges : ℕ) (ends : E → Sym2 V) (S : Finset E)
    (h : (support ends S).Nonempty) : ℕ :=
  max (frontier ends S {firstSeed ends S h}).card (2 ^ (2 * originalEdges / (support ends S).card))

omit [DecidableEq E] in
/-- The explicit first-seed bound in the implementation agrees with the density threshold
of Fredman and Tarjan when the original edge count bounds the current edge count. -/
theorem queueLimit_eq (originalEdges : ℕ) (ends : E → Sym2 V) (S : Finset E)
    (h : (support ends S).Nonempty) (hm : S.card ≤ originalEdges) :
    queueLimit originalEdges ends S h = 2 ^ (2 * originalEdges / (support ends S).card) := by
  have avg := (seed_average ends S h).trans (Nat.mul_le_mul_left 2 hm)
  apply max_eq_right
  apply le_trans _ (Nat.lt_two_pow_self).le
  exact (Nat.le_div_iff_mul_le (Finset.card_pos.mpr h)).mpr (by simpa [Nat.mul_comm] using avg)

/-- One forest of edges that can be contracted simultaneously. A seed with a smallest initial
queue is processed first, and all remaining seeds can be processed in any order. -/
noncomputable def phase (originalEdges : ℕ) (ends : E → Sym2 V) (S : Finset E) (w : E → W)
    (h : (support ends S).Nonempty) : Finset E := by
  classical
  let v := firstSeed ends S h
  let k := queueLimit originalEdges ends S h
  let fuel := (support ends S).card
  let first := grow ends S w k ∅ fuel {v}
  exact first.2 ∪ scan ends S w k fuel first.1 (support ends S).toList

theorem phase_subset_msf (originalEdges : ℕ) (ends : E → Sym2 V) (S : Finset E) (w : E → W)
    (h : (support ends S).Nonempty) : phase originalEdges ends S w h ⊆ msf ends w S := by
  exact union_subset (grow_safe ..) (scan_safe ..)

private theorem phase_nonempty (originalEdges : ℕ) (ends : E → Sym2 V) (S : Finset E) (w : E → W)
    (h : (support ends S).Nonempty) : (phase originalEdges ends S w h).Nonempty := by
  classical
  let v := firstSeed ends S h
  let k := queueLimit originalEdges ends S h
  have le : (frontier ends S {v}).card ≤ k := le_max_left _ _
  obtain ⟨x, hx⟩ := exists_minExit w (seed_cut (seed_mem ends S h))
  apply Finset.Nonempty.mono (s := (grow ends S w k ∅ (support ends S).card {v}).2)
    (subset_union_left (s₂ := scan ..))
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr h)
  rw [hn, grow, ite_eq_right (Nat.not_lt.mpr le)]
  change minExit ends S {v} w = some x at hx
  simp [hx]

private theorem shrink {S F : Finset E} (hF : F ⊆ S) (ne : F.Nonempty) :
    (S \ F).card < S.card := by
  have := card_sdiff_add_card_eq_card hF
  have := card_pos.mpr ne
  omega

/-- Solve the dense quotient using repeated bounded-frontier passes. The original edge count
is kept fixed when setting the queue limits in later passes. -/
noncomputable def solve (originalEdges : ℕ) (w : E → W) (ends : E → Sym2 V)
    (S : Finset E) : Finset E := by
  classical
  exact if h : (support ends S).Nonempty then
    let F := phase originalEdges ends S w h
    F ∪ solve originalEdges w (Sym2.map (contract ends (F : Set E)) ∘ ends) (S \ F)
  else ∅
termination_by S.card
decreasing_by
  exact shrink ((phase_subset_msf ..).trans (msf_subset w)) (phase_nonempty ..)

/-- With distinct weights, the dense passes return precisely the native minimum spanning
forest, also on disconnected inputs, parallel edges, and loops. -/
theorem solve_eq (originalEdges : ℕ) (w : E → W) (hw : Function.Injective w)
    (ends : E → Sym2 V) (S : Finset E) : solve originalEdges w ends S = msf ends w S := by
  classical
  rw [solve]
  split
  next h =>
    dsimp only
    rw [solve_eq originalEdges w hw]
    exact (msf_eq_union_msf_map w hw (phase_subset_msf ..)
      (fun _ _ => contract_eq_contract_iff)).symm
  next h =>
    apply (Finset.eq_empty_iff_forall_notMem.mpr ?_).symm
    intro e he
    have heS := msf_subset w he
    have nonloop : ¬(ends e).IsDiag := fun hd => notMem_msf_of_isDiag w hd he
    obtain ⟨v, hv⟩ : ∃ v, v ∈ ends e :=
      Sym2.inductionOn (ends e) fun a b => ⟨a, Sym2.mem_mk_left a b⟩
    exact h ⟨v, mem_support.mpr ⟨e, heS, nonloop, hv⟩⟩
termination_by S.card
decreasing_by
  exact shrink ((phase_subset_msf ..).trans (msf_subset w)) (phase_nonempty ..)

end Cslib.Multigraph.PettieRamachandran.DenseCase
