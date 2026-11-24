/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.HeapPrim
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.PartitionCharge
import all CslibFrontier.Algorithms.Lean.SoftHeap.Forest

/-!
# Insertions during one soft-heap Prim search

Only first exposures of a cut edge cause insertions, and a search that reaches an old
representative stops before exposing that representative's incident labels. As a result
each insertion contributes a distinct label incident to a newly retired live vertex.
-/

public section

namespace Cslib.Multigraph.PrimPartition.HeapPrim

open Finset Cslib.SoftHeap

variable {V E W : Type} [DecidableEq V] [LinearOrder E] [LinearOrder W]
variable {ends : E → Sym2 V} {w : E → W} {S : Finset E}

private def newLabels (ends : E → Sym2 V) (S : Finset E) (C D : Finset V) : Finset E :=
  S.filter fun e => (orient D (ends e)).isSome && (orient C (ends e)).isNone

private theorem expose_count (t : ℕ) (C D : Finset V) (h : Forest E) (vh : h.Valid w t) :
    (expose ends w t S C D h).Valid w t ∧ (expose ends w t S C D h).insertions =
      h.insertions + (newLabels ends S C D).card := by
  let P (e : E) := (orient D (ends e)).isSome && (orient C (ends e)).isNone
  let step (h : Forest E) (e : E) := if P e then Forest.insert w t e h else h
  have fold (l : List E) (k : Forest E) (hk : k.Valid w t) :
      (l.foldl step k).Valid w t ∧ (l.foldl step k).insertions = k.insertions + l.countP P := by
    induction l generalizing k with
    | nil => simpa using hk
    | cons e es ih =>
      by_cases he : P e
      · have ⟨v, mass⟩ := Forest.insert_spec w t e k hk
        obtain ⟨ok, count⟩ := ih _ v
        refine ⟨by simpa [step, he] using ok, ?_⟩
        simp [step, he, count, mass, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simpa [step, he] using ih k hk
  have eq : (newLabels ends S C D).card = S.sort.countP P := by
    simpa only [newLabels, P, sort_toFinset, Bool.decide_eq_true] using
      (S.sort_nodup (· ≤ ·)).card_eq_countP (P := fun x => P x)
  exact ⟨(fold _ h vh).1, (fold _ h vh).2.trans (congrArg (h.insertions + ·) eq.symm)⟩

omit [DecidableEq V] [LinearOrder E] in
private theorem touched_mono (dead : Finset V) {C D : Finset V} (hCD : C ⊆ D) :
    touched ends S C dead ⊆ touched ends S D dead := by
  intro e he
  obtain ⟨heS, z, hz, hC, hd⟩ := mem_touched.1 he
  exact mem_touched.2 ⟨heS, z, hz, hCD hC, hd⟩

private theorem newLabels_charge (C dead : Finset V) (v : V) (live : v ∉ dead) :
    (newLabels ends S C (insert v C)).card + (touched ends S C dead).card ≤
      (touched ends S (insert v C) dead).card := by
  classical
  have newSub : newLabels ends S C (insert v C) ⊆
      touched ends S (insert v C) dead \ touched ends S C dead := by
    intro e he
    obtain ⟨heS, hcond⟩ := mem_filter.1 he
    obtain ⟨yes, no⟩ := Bool.and_eq_true_iff.1 hcond
    obtain ⟨⟨a, b⟩, eq⟩ := Option.isSome_iff_exists.1 yes
    obtain ⟨hab, ha, hb⟩ := orient_eq_some.1 eq
    have hbC : b ∉ C := fun h => hb (mem_insert_of_mem h)
    have haC : a ∉ C := by
      intro h
      have old := orient_eq_some.2 ⟨hab, h, hbC⟩
      simp [old] at no
    have hva := (mem_insert.1 ha).resolve_right haC
    refine mem_sdiff.2 ⟨mem_touched.2 ⟨heS, a, by simp [hab], ha, hva ▸ live⟩, ?_⟩
    intro old
    obtain ⟨_, z, hz, hC, _⟩ := mem_touched.1 old
    rcases Sym2.mem_iff.1 (hab ▸ hz) with rfl | rfl
    · exact haC hC
    · exact hbC hC
  have oldSub := touched_mono (ends := ends) (S := S) dead (subset_insert v C)
  have count := card_le_card newSub
  have total := card_sdiff_add_card_eq_card oldSub
  omega

/-- The number of insertions represented by the heap of a completed component search
does not exceed the number of labels touched at a live reached vertex. -/
theorem insertions_le_touched (t extra : ℕ) (dead : Finset V) (seed : V) (live : seed ∉ dead) :
    let q := grow t dead S.card extra (start ends w t S seed)
    q.heap.insertions ≤ (touched ends S q.search.vertices dead).card := by
  have loop (ticks extra : ℕ) (q : State ends w S) (vh : q.heap.Valid w t)
      (paid : q.heap.insertions ≤ (touched ends S q.search.vertices dead).card) :
      (grow t dead ticks extra q).heap.insertions ≤
        (touched ends S (grow t dead ticks extra q).search.vertices dead).card := by
    induction ticks generalizing extra q with
    | zero => exact paid
    | succ ticks ih =>
      cases extra with
      | zero => exact paid
      | succ extra =>
        rw [grow]
        split
        · exact paid
        next e rep h hit =>
          obtain ⟨_, valid, same⟩ := Forest.extract_spec vh hit
          split
          next active =>
            split
            · exact ih _ _ valid (same.le.trans paid)
            next u v out =>
              split
              · simp only [advance_heap, Bool.false_eq_true, ↓reduceIte, advance_vertices]
                exact (same.le.trans paid).trans
                  (card_le_card (touched_mono dead (subset_insert ..)))
              next cont =>
                have hv : v ∉ dead := fun hy => cont (Or.inl hy)
                obtain ⟨good, mass⟩ := expose_count (ends := ends) (S := S) t q.search.vertices
                  (insert v q.search.vertices) h valid
                apply ih
                · simpa only [advance_heap, ↓reduceIte] using good
                · simp only [advance_heap, ↓reduceIte, advance_vertices, mass, same]
                  have more := newLabels_charge (ends := ends) (S := S) q.search.vertices dead v hv
                  omega
          · exact ih _ _ valid (same.le.trans paid)
  have empty : (∅ : Forest E).Valid w t := by simp [Forest.Valid]
  obtain ⟨good, count⟩ := expose_count (ends := ends) (S := S) t ∅ {seed} [] empty
  have charge := newLabels_charge (ends := ends) (S := S) ∅ dead seed live
  have base : (start ends w t S seed).heap.insertions ≤ (touched ends S {seed} dead).card := by
    change (expose ends w t S ∅ {seed} []).insertions ≤ _
    rw [count]
    change 0 + _ ≤ _
    rw [Nat.zero_add]
    simpa only [insert_empty_eq] using (Nat.le_add_right _ _).trans charge
  exact loop _ _ _ good base

end Cslib.Multigraph.PrimPartition.HeapPrim
