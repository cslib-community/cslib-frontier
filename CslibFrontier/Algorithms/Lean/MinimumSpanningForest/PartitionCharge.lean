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
# Charging corrupted boundary labels to live endpoints

A fresh queue insertion during a search is charged to the live endpoint which exposed it.
After contraction that endpoint is dead in every later quotient. The live-endpoint potential
therefore pays for each original edge label at most twice, even if it spans several growing
components over time. Combining this with a per-search bound gives the global corrupted-edge
estimate in [Pettie and Ramachandran, Lemma 3.3(d)][PettieRamachandran2002].
-/

public section

namespace Cslib.Multigraph.PrimPartition

open Finset

variable {E V W : Type*} [DecidableEq V] [DecidableEq E] [LinearOrder W]

/-- Labels incident to some previously live vertex reached during this component search. -/
noncomputable def touched (ends : E → Sym2 V) (S : Finset E) (C dead : Finset V) : Finset E := by
  classical exact S.filter fun e => ∃ x ∈ ends e, x ∈ C ∧ x ∉ dead

omit [DecidableEq E] [DecidableEq V] in
theorem mem_touched {ends : E → Sym2 V} {S : Finset E} {C dead : Finset V} {e : E} :
    e ∈ touched ends S C dead ↔ e ∈ S ∧ ∃ x ∈ ends e, x ∈ C ∧ x ∉ dead := by
  classical exact mem_filter

private def liveEnds (dead : Finset V) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun a b => (if a ∈ dead then 0 else 1) + (if b ∈ dead then 0 else 1),
    fun _ _ => Nat.add_comm ..⟩

private def potential (ends : E → Sym2 V) (S : Finset E) (dead : Finset V) : ℕ :=
  ∑ e ∈ S, liveEnds dead (ends e)

omit [DecidableEq E] in
private theorem step_charge (ends : E → Sym2 V) (S R : Finset E) (C dead : Finset V)
    (c : V → V) (hR : R ⊆ S) :
    (touched ends S C dead).card + potential (Sym2.map c ∘ ends) R ((dead ∪ C).image c) ≤
      potential ends S dead := by
  classical
  let spent (e : E) : ℕ := if ∃ x ∈ ends e, x ∈ C ∧ x ∉ dead then 1 else 0
  let left (e : E) := liveEnds ((dead ∪ C).image c) (Sym2.map c (ends e))
  have singles (e : E) : spent e + left e ≤ liveEnds dead (ends e) := by
    obtain ⟨a, b, hab⟩ : ∃ a b, ends e = s(a, b) :=
      Sym2.inductionOn (ends e) fun a b => ⟨a, b, rfl⟩
    have hit {v : V} (h : v ∈ dead ∨ v ∈ C) : c v ∈ (dead ∪ C).image c :=
      mem_image_of_mem _ (mem_union.2 h)
    have hspent : spent e = if (a ∈ C ∧ a ∉ dead) ∨ (b ∈ C ∧ b ∉ dead) then 1 else 0 := by
      simp only [spent, hab, Sym2.mem_iff]
      congr 1
      grind
    rw [hspent]
    simp only [left, hab, Sym2.map_mk, liveEnds, Sym2.lift_mk]
    by_cases a ∈ dead <;> by_cases b ∈ dead <;> by_cases a ∈ C <;> by_cases b ∈ C <;>
      split_ifs <;> grind
  have walks : (touched ends S C dead).card = ∑ e ∈ S, spent e := by
    simp [touched, spent, ← Finset.sum_filter]
  have rest : ∑ e ∈ R, left e ≤ ∑ e ∈ S, left e := sum_le_sum_of_subset_of_nonneg hR
    (fun _ _ _ => Nat.zero_le _)
  calc
    _ ≤ (∑ e ∈ S, spent e) + ∑ e ∈ S, left e := Nat.add_le_add (le_of_eq walks) rest
    _ = ∑ e ∈ S, (spent e + left e) := (sum_add_distrib ..).symm
    _ ≤ _ := sum_le_sum (fun e _ => singles e)

/-- An inverse corruption rate per search is preserved when the searches run successively.
The sum of live endpoint occurrences in an initially unmarked graph is exactly twice its
number of edge labels, including both occurrences of a loop. -/
theorem marks_le_twice_edges {w : E → W} (p : Grower V E W w) (denominator extra : ℕ)
    (localBound : ∀ (ends : E → Sym2 V) (S : Finset E) (dead : Finset V) (seed : V),
      seed ∉ dead → let q := p.run ends S extra dead seed
        denominator * (q.part.marks ends w S).card ≤ (touched ends S q.vertices dead).card)
    (ends : E → Sym2 V) (S : Finset E) (vertices : List V) :
    denominator * (collect w ends S (partition p extra ends S id ∅ vertices)).marked.card ≤
      2 * S.card := by
  have loop (rep : V → V) (dead : Finset V) :
      denominator * (collect w ends S (partition p extra ends S rep dead vertices)).marked.card ≤
        potential ends S dead := by
    induction vertices generalizing ends S rep dead with
    | nil => simp [partition, collect, potential]
    | cons v vs ih =>
      rw [partition]
      split
      · exact ih ends S rep dead
      next fresh =>
        let q := p.run ends S extra dead (rep v)
        let c := contract ends (internalEdges ends S q.part.vertices)
        let rest := q.part.remaining ends w S
        let dead' := (dead ∪ q.vertices).image c
        let parts := partition p extra (q.part.nextEnds ends S) rest (c ∘ rep) dead' vs
        let tail := collect w (q.part.nextEnds ends S) rest parts
        have h₁ := localBound ends S dead (rep v) fresh
        have h₂ := ih (ends := q.part.nextEnds ends S) (S := rest) (c ∘ rep) dead'
        have h₃ := step_charge ends S rest q.vertices dead c (q.part.remaining_subset ends w S)
        change denominator * (q.part.marks ends w S).card ≤
          (touched ends S q.vertices dead).card at h₁
        change denominator * tail.marked.card ≤
          potential (Sym2.map c ∘ ends) rest dead' at h₂
        change (touched ends S q.vertices dead).card +
          potential (Sym2.map c ∘ ends) rest dead' ≤ _ at h₃
        change denominator * (q.part.marks ends w S ∪ tail.marked).card ≤ _
        calc
          _ ≤ denominator * ((q.part.marks ends w S).card + tail.marked.card) :=
            Nat.mul_le_mul_left _ (card_union_le _ _)
          _ ≤ _ := by rw [Nat.mul_add]; omega
  have start : potential ends S ∅ = 2 * S.card := by
    have two (e : E) : liveEnds (∅ : Finset V) (ends e) = 2 := by
      induction ends e using Sym2.ind with
      | _ a b => simp [liveEnds]
    simp [potential, two, Nat.mul_comm]
  exact (loop id ∅).trans_eq start

end Cslib.Multigraph.PrimPartition
