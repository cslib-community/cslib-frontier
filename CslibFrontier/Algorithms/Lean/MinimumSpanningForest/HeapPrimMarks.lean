/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.HeapPrim
public import CslibFrontier.Algorithms.Lean.SoftHeap.Keys
import all CslibFrontier.Algorithms.Lean.MinimumSpanningForest.GrowingPartition

/-!
# Charging marked boundary labels to the concrete soft heap

Every live outgoing label is in the heap. When a search stops before exposing its last
vertex, newly outgoing edges still have their input keys. A marked outgoing edge therefore
has a live occurrence whose recorded key exceeds its input key. The rank-based corruption
bound applies to these occurrences at the end of the search.
-/

public section

namespace Cslib.Multigraph.PrimPartition.HeapPrim

open Finset Cslib.SoftHeap

variable {V E W : Type} [DecidableEq V] [LinearOrder E] [LinearOrder W]
  {ends : E → Sym2 V} {S : Finset E} {w : E → W}

/-- One pass of the exposure loop preserves old occurrences, inserts every newly exposed
edge, and preserves the forest invariants when the inserted labels still have original keys. -/
theorem expose_spec (ends : E → Sym2 V) (w k : E → W) (t : ℕ) (S : Finset E)
    (C D : Finset V) (h : Forest E) (val : h.Valid w t) (cov : h.Covers w k)
    (clean : ∀ e ∈ S, (orient D (ends e)).isSome → (orient C (ends e)).isNone → k e ≤ w e) :
    let q := expose ends w t S C D h
    q.Valid w t ∧ q.Covers w k ∧ ∀ e, e ∈ q.items ↔ e ∈ h.items ∨
      e ∈ S ∧ (orient D (ends e)).isSome ∧ (orient C (ends e)).isNone := by
  let flag (e : E) := (orient D (ends e)).isSome && (orient C (ends e)).isNone
  let step (heap : Forest E) (e : E) := if flag e then Forest.insert w t e heap else heap
  have aux (xs : List E) (sub : ∀ e ∈ xs, e ∈ S) (heap : Forest E)
      (v : heap.Valid w t) (c : heap.Covers w k) :
      let result := xs.foldl step heap
      result.Valid w t ∧ result.Covers w k ∧ ∀ e, e ∈ result.items ↔
        e ∈ heap.items ∨ e ∈ xs ∧ flag e := by
    induction xs generalizing heap with
    | nil => simpa using And.intro v c
    | cons a xs ih =>
      have sub' : ∀ e ∈ xs, e ∈ S := fun e he => sub e (List.mem_cons_of_mem _ he)
      by_cases f : flag a = true
      · have active := Bool.and_eq_true_iff.mp f
        obtain ⟨v', c', pop⟩ := ih sub' (Forest.insert w t a heap)
          (Forest.insert_spec w t a heap v).1
          (Forest.insert_covers t _ _ (clean a (sub a (by simp)) active.1 active.2) c)
        change _ ∧ _ ∧ _
        simp only [List.foldl_cons, step, f, ite_true]
        refine ⟨v', c', fun e => ?_⟩
        rw [pop, Forest.insert_items]
        simp only [Multiset.mem_add, Multiset.mem_singleton, List.mem_cons]
        grind
      · obtain ⟨v', c', pop⟩ := ih sub' heap v c
        simp only [List.foldl_cons, step, f, Bool.false_eq_true, ite_false]
        refine ⟨v', c', fun e => ?_⟩
        rw [pop]
        simp only [List.mem_cons]
        grind
  obtain ⟨valid, covered, pop⟩ := aux S.sort (fun e he => by simpa using he) h val cov
  refine ⟨valid, covered, fun e => ?_⟩
  have listed : e ∈ S.sort ↔ e ∈ S := by simp
  simpa only [listed, expose, step, flag, Bool.and_eq_true] using pop e

/-- Edges with neither endpoint reached could never have appeared on an earlier cut. -/
private def Unseen (C : Finset V) (z : Sym2 V) : Prop := ∀ a ∈ z, a ∉ C

private theorem unseen_of_new {C : Finset V} {v : V} {z : Sym2 V}
    (old : (orient C z).isNone) (new : (orient (insert v C) z).isSome) : Unseen C z := by
  obtain ⟨⟨a, b⟩, hit⟩ := Option.isSome_iff_exists.mp new
  obtain ⟨rfl, ha, hb⟩ := orient_eq_some.mp hit
  have hb' : b ∉ C := fun h => hb (mem_insert_of_mem h)
  have ha' : a ∉ C := by
    intro mem
    have eq := orient_eq_some.mpr (And.intro rfl (And.intro mem hb'))
    simp only [eq, Option.isNone_some, Bool.false_eq_true] at old
  intro u hu
  rcases Sym2.mem_iff.mp hu with rfl | rfl
  · exact ha'
  · exact hb'

private theorem orient_none_of_unseen {C : Finset V} {z : Sym2 V} (h : Unseen C z) :
    orient C z = none := by
  cases e : orient C z with
  | none => rfl
  | some p =>
    obtain ⟨x, y⟩ := p
    obtain ⟨eq, mem, _⟩ := orient_eq_some.mp e
    exact False.elim (h x (eq ▸ Sym2.mem_mk_left ..) mem)

private structure OK (t : ℕ) (full : Bool) (q : State ends w S) : Prop where
  valid : q.heap.Valid w t
  covered : q.heap.Covers w q.search.key
  fresh : ∀ f ∈ S, Unseen q.search.vertices (ends f) → q.search.key f = w f
  boundary : ∀ f ∈ S, (orient q.search.vertices (ends f)).isSome →
    full = true ∨ q.search.key f ≠ w f → f ∈ q.heap.items

private theorem start_ok (ends : E → Sym2 V) (w : E → W) (S : Finset E) (t : ℕ) (v : V) :
    OK t true (start ends w t S v) := by
  have hv : Forest.Valid w t ([] : Forest E) := by simp [Forest.Valid]
  have hc : Forest.Covers w w ([] : Forest E) := by simp [Forest.Covers]
  obtain ⟨vh, ch, pop⟩ := expose_spec ends w w t S ∅ {v} [] hv hc (fun _ _ _ _ => le_rfl)
  refine ⟨vh, ch, fun _ _ _ => rfl, ?_⟩
  intro f hf out _
  exact (pop f).mpr (Or.inr ⟨hf, out, by
    rw [orient_none_of_unseen (show Unseen ∅ (ends f) from fun _ _ => notMem_empty _)]; rfl⟩)

omit [LinearOrder E] in
private theorem skip_ok {t : ℕ} {q : State ends w S} (ok : OK t true q) {e rep : E}
    {h : Forest E} (hit : Forest.extract w t q.heap = some ((e, rep), h))
    (stale : e ∉ S ∨ (orient q.search.vertices (ends e)).isNone) :
    OK t true {q with heap := h} := by
  have ⟨_, vh, _⟩ := Forest.extract_spec ok.valid hit
  have ⟨_, cover⟩ := Forest.extract_covers ok.covered hit
  refine ⟨vh, cover _ (fun _ => le_max_left ..), ok.fresh, ?_⟩
  intro f hf out _
  have live := ok.boundary f hf out (.inl rfl)
  rw [← Forest.extract_items hit, Multiset.mem_add, Multiset.mem_singleton] at live
  rcases live with rfl | h
  · rcases stale with ne | ne
    · exact False.elim (ne hf)
    · simp_all
  · exact h

private theorem advance_ok {t : ℕ} {q : State ends w S} (ok : OK t true q) {e rep : E}
    {h : Forest E} (hit : Forest.extract w t q.heap = some ((e, rep), h)) {u v : V} (he : e ∈ S)
    (out : orient q.search.vertices (ends e) = some (u, v)) (more : Bool) :
    OK t more (advance q t e rep u v he out h more) := by
  let C := q.search.vertices
  let D := insert v C
  let old := q.search.key
  let k := liftCut ends C old (max (old e) (w rep))
  obtain ⟨le, covered⟩ := Forest.extract_covers ok.covered hit
  obtain ⟨_, val, _⟩ := Forest.extract_spec ok.valid hit
  have cov : h.Covers w k := covered k fun f => by
    simp only [k, old, liftCut, max_eq_right le]
    split
    · exact le_rfl
    · exact le_max_left ..
  have orig (f : E) (hf : f ∈ S) (unseen : Unseen C (ends f)) : k f = w f := by
    simp [k, liftCut, orient_none_of_unseen unseen, old, ok.fresh f hf unseen]
  have clean (f : E) (hf : f ∈ S) (new : (orient D (ends f)).isSome)
      (prev : (orient C (ends f)).isNone) : k f = w f :=
    orig f hf (unseen_of_new prev new)
  have fresh (f : E) (hf : f ∈ S) (unseen : Unseen D (ends f)) : k f = w f :=
    orig f hf (fun a ha hC => unseen a ha (mem_insert_of_mem hC))
  have old_live (f : E) (hf : f ∈ S) (new : (orient D (ends f)).isSome)
      (prev : (orient C (ends f)).isSome) : f ∈ h.items := by
    have mem := ok.boundary f hf prev (.inl rfl)
    rw [← Forest.extract_items hit, Multiset.mem_add, Multiset.mem_singleton] at mem
    rcases mem with rfl | hmem
    · obtain ⟨inc, hu, hv⟩ := orient_eq_some.mp out
      rw [inc] at new
      simp [orient, D, C, hu] at new
    · exact hmem
  cases more with
  | false =>
    refine ⟨val, cov, fresh, ?_⟩
    intro f hf new need
    obtain eq := need.resolve_left (by decide)
    cases prev : orient C (ends f) with
    | none => exact False.elim (eq (clean f hf new (by rw [prev]; rfl)))
    | some p => exact old_live f hf new (by rw [prev]; rfl)
  | true =>
    obtain ⟨v', c', pop⟩ := expose_spec ends w k t S C D h val cov
      (fun f hf n o => (clean f hf n o).le)
    refine ⟨v', c', fresh, ?_⟩
    intro f hf new _
    apply (pop f).mpr
    cases prev : orient C (ends f) with
    | none => exact Or.inr ⟨hf, new, rfl⟩
    | some p => exact Or.inl (old_live f hf new (by rw [prev]; rfl))

private theorem grow_ok (t : ℕ) (dead : Finset V) (ticks extra : ℕ) (q : State ends w S)
    (ok : OK t true q) : ∃ full, OK t full (grow t dead ticks extra q) := by
  induction ticks generalizing extra q with
  | zero => exact ⟨true, ok⟩
  | succ ticks ih =>
    cases extra with
    | zero => exact ⟨true, ok⟩
    | succ extra =>
      rw [grow]
      split
      · exact ⟨true, ok⟩
      next e rep h hit =>
        split
        · next he =>
          split
          · next stale => exact ih _ _ (skip_ok ok hit (Or.inr (by rw [stale]; rfl)))
          next u v out =>
            split
            · exact ⟨false, advance_ok ok hit he out false⟩
            · exact ih _ _ (advance_ok ok hit he out true)
        · next inactive => exact ih _ _ (skip_ok ok hit (Or.inl inactive))

/-- The marked boundary labels at search termination are charged to distinct currently
corrupted heap items. The denominator counts historical insertions into this component heap. -/
theorem marks_le_insertions (ends : E → Sym2 V) (w : E → W) (S : Finset E) (t extra : ℕ)
    (dead : Finset V) (seed : V) :
    let q := grow t dead S.card extra (start ends w t S seed)
    (q.search.part.marks ends w S).card * 4 ^ t ≤ q.heap.insertions := by
  let q := grow t dead S.card extra (start ends w t S seed)
  obtain ⟨full, ok⟩ := grow_ok t dead S.card extra (start ends w t S seed) (start_ok ..)
  have sub : (q.search.part.marks ends w S).val ≤
      q.heap.items.filter (fun e => w e < q.search.key e) := by
    apply (Multiset.le_iff_subset (q.search.part.marks ends w S).nodup).mpr
    intro f hf
    obtain ⟨active, cut, ne⟩ := (q.search.part.mem_marks ends w S).mp hf
    obtain ⟨a, b, hab, ha, hb⟩ := Graph.mem_edgeCut_iff.mp cut
    have out : orient q.search.vertices (ends f) = some (a, b) := orient_eq_some.mpr ⟨hab, ha, hb⟩
    have live := ok.boundary f active (Option.isSome_of_eq_some out) (.inr ne)
    have lt : w f < q.search.key f := lt_of_le_of_ne (q.search.raised f active) (Ne.symm ne)
    exact Multiset.mem_filter.mpr ⟨live, lt⟩
  exact (Nat.mul_le_mul_right _ ((Multiset.card_le_card sub).trans
    (Forest.count_raised_le q.heap ok.covered))).trans (Forest.corruptions_bound q.heap ok.valid)

private noncomputable def unseenLabels (ends : E → Sym2 V) (S : Finset E) (C : Finset V) :
    Finset E := by classical exact S.filter fun e => Unseen C (ends e)

omit [DecidableEq V] [LinearOrder E] in
private theorem mem_unseenLabels {C : Finset V} {e : E} :
    e ∈ unseenLabels ends S C ↔ e ∈ S ∧ Unseen C (ends e) := by
  classical exact mem_filter

/-- Exposing a new vertex transfers previously unseen labels into the heap. Their number
cannot increase the sum of unseen labels and live heap occurrences. -/
private theorem expose_potential (t : ℕ) (C : Finset V) (v : V) (h : Forest E) :
    (expose ends w t S C (insert v C) h).items.card +
      (unseenLabels ends S (insert v C)).card ≤ h.items.card + (unseenLabels ends S C).card := by
  classical
  let D := insert v C
  let flag (e : E) := (orient D (ends e)).isSome && (orient C (ends e)).isNone
  let used := S.filter (fun e => flag e)
  let step (heap : Forest E) (e : E) := if flag e then Forest.insert w t e heap else heap
  have fold (l : List E) (heap : Forest E) :
      (l.foldl step heap).items.card = heap.items.card + l.countP flag := by
    induction l generalizing heap with
    | nil => simp
    | cons e es ih =>
      by_cases yes : flag e
      · simp [step, yes, ih, Forest.insert_items, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · simp [step, yes, ih]
  have count : used.card = S.sort.countP flag := by
    simpa only [used, sort_toFinset, Bool.decide_eq_true] using
      (S.sort_nodup (· ≤ ·)).card_eq_countP (P := fun x => flag x)
  have mass : (expose ends w t S C D h).items.card = h.items.card + used.card := by
    rw [count]
    exact fold S.sort h
  have dis : Disjoint used (unseenLabels ends S D) := by
    apply disjoint_left.mpr
    intro e he hu
    have flag' := (mem_filter.mp he).2
    have hit := (Bool.and_eq_true_iff.mp flag').1
    rw [orient_none_of_unseen (mem_unseenLabels.mp hu).2] at hit
    contradiction
  have sub : used ∪ unseenLabels ends S D ⊆ unseenLabels ends S C := by
    intro e he
    rcases mem_union.mp he with u | fresh
    · obtain ⟨inS, f⟩ := mem_filter.mp u
      obtain ⟨n, o⟩ := Bool.and_eq_true_iff.mp f
      exact mem_unseenLabels.mpr ⟨inS, unseen_of_new o n⟩
    · obtain ⟨inS, hf⟩ := mem_unseenLabels.mp fresh
      exact mem_unseenLabels.mpr ⟨inS, fun a ha hc => hf a ha (mem_insert_of_mem hc)⟩
  have charge := card_le_card sub
  rw [card_union_of_disjoint dis] at charge
  change (expose ends w t S C D h).items.card + (unseenLabels ends S D).card ≤ _
  rw [mass]
  omega

omit [LinearOrder E] in
private theorem closed_of_empty {t : ℕ} {q : State ends w S} (ok : OK t true q)
    (empty : q.heap.items = 0) :
    ∀ e ∈ S, e ∉ (toGraph ends).edgeCut (q.search.vertices : Set V) := by
  intro e he hc
  obtain ⟨a, b, hab, ha, hb⟩ := Graph.mem_edgeCut_iff.mp hc
  have ex : orient q.search.vertices (ends e) = some (a, b) := orient_eq_some.mpr ⟨hab, ha, hb⟩
  have live := ok.boundary e he (Option.isSome_of_eq_some ex) (.inl rfl)
  simp [empty] at live

private theorem completes {t : ℕ} (dead : Finset V) (ticks extra : ℕ) (q : State ends w S)
    (ok : OK t true q)
    (budget : q.heap.items.card + (unseenLabels ends S q.search.vertices).card ≤ ticks) :
    let out := (grow t dead ticks extra q).search.vertices
    q.search.vertices ⊆ out ∧
    (out.card = q.search.vertices.card + extra ∨ (∃ v ∈ out, v ∈ dead) ∨
      ∀ e ∈ S, e ∉ (toGraph ends).edgeCut (out : Set V)) := by
  induction ticks generalizing extra q with
  | zero =>
    rw [grow]
    have no : q.heap.items.card = 0 := by omega
    exact ⟨Subset.rfl, Or.inr (Or.inr (closed_of_empty ok (Multiset.card_eq_zero.mp no)))⟩
  | succ ticks ih =>
    cases extra with
    | zero => exact ⟨Subset.rfl, Or.inl rfl⟩
    | succ extra =>
      simp only [grow]
      split
      · next empty => exact ⟨Subset.rfl, Or.inr (Or.inr
          (closed_of_empty ok (Forest.items_eq_zero_of_extract_none ok.covered empty)))⟩
      next e rep h hit =>
        have balance : 1 + h.items.card = q.heap.items.card := by
          simpa only [Multiset.card_add, Multiset.card_singleton] using
            congrArg Multiset.card (Forest.extract_items hit)
        have left : h.items.card + (unseenLabels ends S q.search.vertices).card ≤ ticks := by omega
        split
        · next he =>
          split
          · next stale => exact ih _ _ (skip_ok ok hit (Or.inr (by rw [stale]; rfl))) left
          next u v out =>
            have fresh := (orient_eq_some.mp out).2.2
            have hcard := card_insert_of_notMem fresh
            split
            · next stop =>
              simp only [advance_vertices]
              refine ⟨subset_insert .., ?_⟩
              rcases stop with died | rfl
              · exact Or.inr (Or.inl ⟨v, mem_insert_self .., died⟩)
              · exact Or.inl hcard
            · have pot := expose_potential (ends := ends) (S := S) (w := w) t q.search.vertices v h
              have outOk := advance_ok ok hit he out true
              have fuel := pot.trans left
              obtain ⟨mono, stop⟩ := ih extra _ outOk (by
                simpa only [advance_vertices, advance_heap, ite_true] using fuel)
              refine ⟨(subset_insert ..).trans mono, ?_⟩
              rcases stop with cap | rest
              · exact Or.inl (by rw [advance_vertices, hcard] at cap; omega)
              · exact Or.inr rest
        · next inactive => exact ih _ _ (skip_ok ok hit (Or.inl inactive)) left

/-- The actual search includes its seed and can terminate only at the quota, at a previously
dead vertex, or after exhausting its outgoing cut. The tick budget cannot truncate a search. -/
theorem grower_complete (w : E → W) (t : ℕ) (ends : E → Sym2 V) (S : Finset E)
    (extra : ℕ) (dead : Finset V) (v : V) :
    let q := (grower t w).run ends S extra dead v
    v ∈ q.vertices ∧ (q.vertices.card = extra + 1 ∨ (∃ x ∈ q.vertices, x ∈ dead) ∨
      ∀ e ∈ S, e ∉ (toGraph ends).edgeCut (q.vertices : Set V)) := by
  have init := expose_potential (ends := ends) (S := S) (w := w) t ∅ v []
  have un : unseenLabels ends S ∅ = S := by ext e; simp [unseenLabels, Unseen]
  rw [un] at init
  have ticks : (start ends w t S v).heap.items.card +
      (unseenLabels ends S (start ends w t S v).search.vertices).card ≤ S.card := by
    simpa only [start, SearchState.start, insert_empty_eq, Forest.items, List.map_nil,
      List.sum_nil, Multiset.card_zero, zero_add] using init
  obtain ⟨mono, stop⟩ := completes dead S.card extra _ (start_ok ends w S t v) ticks
  refine ⟨mono (mem_singleton_self _), ?_⟩
  rcases stop with size | rest
  · exact Or.inl (by simpa [start, SearchState.start, Nat.add_comm, grower] using size)
  · exact Or.inr rest

end Cslib.Multigraph.PrimPartition.HeapPrim
