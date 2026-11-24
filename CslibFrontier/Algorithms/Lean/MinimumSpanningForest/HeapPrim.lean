/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.GrowingPartition
public import CslibFrontier.Algorithms.Lean.SoftHeap.Ordering
public import Mathlib.Data.Finset.Sort

/-!
# Growing a Prim component by soft-heap extraction

Only newly exposed edges are inserted. Extraction discards a stale edge if both ends have
already been reached. For a successful extraction the algorithm records its representative
key, updated by any earlier floor on the selected edge, as a lower bound on the current cut.
These nondecreasing recorded keys witness the entire Prim prefix. The forest is threaded
through all steps in one component search.

This implementation computes newly exposed labels by scanning the finite edge set.
-/

public section

namespace Cslib.Multigraph.PrimPartition.HeapPrim

open Finset Cslib.SoftHeap

variable {V E W : Type} [DecidableEq V] [LinearOrder E] [LinearOrder W]
  {ends : E → Sym2 V} {S : Finset E} {w : E → W}

/-- Orient an edge out of `C` when exactly one endpoint has been reached. -/
@[expose] def orient (C : Finset V) : Sym2 V → Option (V × V) :=
  Sym2.lift ⟨fun a b => if a ∈ C then (if b ∈ C then none else some (a, b))
    else (if b ∈ C then some (b, a) else none), by
    intro a b
    by_cases ha : a ∈ C <;> by_cases hb : b ∈ C <;> simp [ha, hb]⟩

theorem orient_eq_some {C : Finset V} {z : Sym2 V} {a b : V} :
    orient C z = some (a, b) ↔ z = s(a, b) ∧ a ∈ C ∧ b ∉ C := by
  induction z using Sym2.ind with
  | _ x y =>
    by_cases hx : x ∈ C <;> by_cases hy : y ∈ C <;>
      simp [orient, hx, hy] <;> grind

/-- Insert those edges that have just become outgoing for the first time. -/
@[expose] def expose (ends : E → Sym2 V) (w : E → W) (t : ℕ) (S : Finset E)
    (before after : Finset V) (h : Forest E) : Forest E :=
  S.sort.foldl (fun heap e =>
    if (orient after (ends e)).isSome && (orient before (ends e)).isNone then
      Forest.insert w t e heap else heap) h

/-- The priority queue and the Prim certificate accumulated by one component search. -/
structure State (ends : E → Sym2 V) (w : E → W) (S : Finset E) where
  /-- Reached vertices and frozen keys. -/
  search : SearchState ends w S
  /-- Unexamined edge occurrences, possibly including stale edges. -/
  heap : Forest E
  /-- An already chosen label is internal, so all further cut updates leave it unchanged. -/
  inside : ∀ e ∈ search.chosen, ∀ v ∈ ends e, v ∈ search.vertices

/-- Start with exactly the edges on the seed cut. -/
@[expose] def start (ends : E → Sym2 V) (w : E → W) (t : ℕ) (S : Finset E) (seed : V) :
    State ends w S where
  search := SearchState.start seed
  heap := expose ends w t S ∅ {seed} []
  inside := by simp [SearchState.start]

/-- Record the lower bound witnessed at an extraction on each boundary edge. -/
@[expose] def liftCut (ends : E → Sym2 V) (C : Finset V) (k : E → W) (level : W) (e : E) : W :=
  if (orient C (ends e)).isSome then max (k e) level else k e

/-- Extend the certificate and expose new edges after an oriented extraction. -/
@[expose] def advance (q : State ends w S) (t : ℕ) (e rep : E) (u v : V) (active : e ∈ S)
    (out : orient q.search.vertices (ends e) = some (u, v)) (h : Forest E)
    (continueSearch : Bool) : State ends w S := by
  let C := q.search.vertices
  let floor := max (q.search.key e) (w rep)
  let k := liftCut ends C q.search.key floor
  obtain ⟨inc, hu, hv⟩ := orient_eq_some.mp out
  have rise (f : E) (_ : f ∈ S) : q.search.key f ≤ k f := by
    dsimp [k, liftCut]; split <;> simp
  have frozen (f : E) (hf : f ∈ q.search.chosen) : k f = q.search.key f := by
    unfold k liftCut
    split
    · next has =>
      obtain ⟨⟨a, b⟩, pair⟩ := Option.isSome_iff_exists.mp has
      obtain ⟨inc', _, absent⟩ := orient_eq_some.mp pair
      exact False.elim (absent (q.inside f hf b (inc' ▸ Sym2.mem_mk_right ..)))
    · rfl
  let exit : SearchState.Exit ends S C k :=
    ⟨e, u, v, active, hu, hv, inc, fun f _ x hx y hy hxy => by
      have pair := orient_eq_some.mpr ⟨hxy, hx, hy⟩
      have yes : orient C (ends e) = some (u, v) := out
      simp [k, liftCut, yes, pair, floor]⟩
  let s := q.search.takeExit k rise frozen exit
  refine ⟨s, if continueSearch then expose ends w t S C s.vertices h else h, ?_⟩
  intro f hf a ha
  change f ∈ insert e q.search.chosen at hf
  change a ∈ insert v C
  rcases mem_insert.mp hf with rfl | prev
  · rw [inc] at ha
    rcases Sym2.mem_iff.mp ha with rfl | rfl
    · exact mem_insert_of_mem hu
    · exact mem_insert_self ..
  · exact mem_insert_of_mem (q.inside f prev a ha)

/-- Execute at most `ticks` extractions and add at most `extra` vertices. Dead vertices
terminate the current component as soon as they are reached. -/
@[expose] def grow (t : ℕ) (dead : Finset V) :
    ℕ → ℕ → State ends w S → State ends w S
  | 0, _, q | _, 0, q => q
  | ticks + 1, extra + 1, q =>
    match Forest.extract w t q.heap with
    | none => q
    | some ((e, rep), h) =>
      if active : e ∈ S then
        match out : orient q.search.vertices (ends e) with
        | none => grow t dead ticks (extra + 1) {q with heap := h}
        | some (u, v) =>
          if v ∈ dead ∨ extra = 0 then advance q t e rep u v active out h false
          else grow t dead ticks extra (advance q t e rep u v active out h true)
      else grow t dead ticks (extra + 1) {q with heap := h}

theorem grow_bound (t : ℕ) (dead : Finset V) (ticks extra : ℕ) (q : State ends w S) :
    (grow t dead ticks extra q).search.vertices.card ≤ q.search.vertices.card + extra := by
  induction ticks generalizing extra q with
  | zero => simp [grow]
  | succ ticks ih =>
    cases extra with
    | zero => simp [grow]
    | succ extra =>
      rw [grow]
      split
      · omega
      next e rep h _ =>
        split
        · next active =>
          split
          · exact ih _ _
          next u v out =>
            have card (more : Bool) :
                (advance q t e rep u v active out h more).search.vertices.card =
                q.search.vertices.card + 1 := card_insert_of_notMem (orient_eq_some.mp out).2.2
            split
            · rw [card]; omega
            · exact (ih extra _).trans (by rw [card]; omega)
        · exact ih _ _

/-- The soft-heap component grower for the Pettie–Ramachandran live/dead partition. -/
@[expose] def grower (t : ℕ) (w : E → W) : Grower V E W w where
  run ends S extra dead seed := (grow t dead S.card extra (start ends w t S seed)).search
  bound ends S extra dead seed := by
    simpa [start, SearchState.start, Nat.add_comm] using
      grow_bound t dead S.card extra (start ends w t S seed)

end Cslib.Multigraph.PrimPartition.HeapPrim
