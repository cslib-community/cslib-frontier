/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Relation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Depth-first search

Depth-first search on a directed graph given by adjacency lists `adj : V → List V`, with the
finishing order of the vertices, after [Tarjan][Tarjan1972] and [Cormen et al., Section
22.3][CLRS2009].

`Cslib.Algorithms.Lean.DFS.visit adj k u s` visits `u` from the state `s` (the discovered vertices
and the finished vertices, most recently finished first): if `u` is undiscovered it is discovered,
its successors are visited in turn, and it is finished. The recursion budget `k` makes the
definition structural; `Fintype.card V ≤ k` suffices, because each nested call discovers a new
vertex. `Cslib.Algorithms.Lean.DFS.dfs adj k roots` visits the roots in turn from the empty
state. Linear-time iterative execution on the standard-basis word RAM is proved in
`CslibFrontier.Algorithms.WordRAM.DFS`.

## Main definitions

* `Cslib.Algorithms.Lean.DFS.Edge`: the edge relation of adjacency lists.
* `Cslib.Algorithms.Lean.DFS.StronglyConnected`: mutual reachability in `Edge adj`.
* `Cslib.Algorithms.Lean.DFS.State`: discovered-set and finishing-list state of depth-first search.
* `Cslib.Algorithms.Lean.DFS.visit`, `Cslib.Algorithms.Lean.DFS.dfs`: depth-first search.
* `Cslib.Algorithms.Lean.DFS.outDegreeSum`: total out-degree of a list of vertices.

## Main results

* `Cslib.Algorithms.Lean.DFS.mem_dfs_visited_iff`, `Cslib.Algorithms.Lean.DFS.mem_dfs_finished_iff`:
  depth-first search discovers and finishes exactly the vertices reachable from the roots.
* `Cslib.Algorithms.Lean.DFS.nodup_dfs_finished`: each vertex finishes at most once.
* `Cslib.Algorithms.Lean.DFS.dfs_finished_order`: for every edge `u → v` out of a finished vertex,
  either `u` finishes after `v` or `v` reaches `u`, so that the edge closes a cycle. This is the
  finishing-time argument in the proof of [Cormen et al., Theorem 22.12][CLRS2009], which rests on
  the absence of back edges in acyclic graphs (Lemma 22.11 there).
* `Cslib.Algorithms.Lean.DFS.dfs_scc_finished_order`: if a finished vertex `u` reaches `v` while
  `v` does not reach `u`, some vertex mutually reachable with `u` finishes after `v` (the
  component finishing-time property underlying Kosaraju's algorithm [Cormen et al.][CLRS2009]).

## References

* [R. E. Tarjan, *Depth-first search and linear graph algorithms*][Tarjan1972]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.DFS

open scoped List

variable {V : Type*}

/-- The edge relation of adjacency lists: `Edge adj u v` when `v` is listed among the successors
of `u`. -/
def Edge (adj : V → List V) (u v : V) : Prop := v ∈ adj u

instance [DecidableEq V] (adj : V → List V) : DecidableRel (Edge adj) := fun u v =>
  inferInstanceAs (Decidable (v ∈ adj u))

/-- Two vertices lie in the same strongly connected component when each reaches the other. -/
def StronglyConnected (adj : V → List V) (u v : V) : Prop :=
  Relation.ReflTransGen (Edge adj) u v ∧ Relation.ReflTransGen (Edge adj) v u

namespace StronglyConnected

variable {adj : V → List V}

theorem refl (u : V) : StronglyConnected adj u u := ⟨.refl, .refl⟩

theorem symm {u v : V} (h : StronglyConnected adj u v) : StronglyConnected adj v u :=
  ⟨h.2, h.1⟩

theorem trans {u v w : V} (h₁ : StronglyConnected adj u v) (h₂ : StronglyConnected adj v w) :
    StronglyConnected adj u w :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

end StronglyConnected

/-- The state of depth-first search. -/
structure State (V : Type*) where
  /-- The discovered vertices. -/
  visited : Finset V
  /-- The finished vertices, most recently finished first. -/
  finished : List V

/-- Visit `u` with recursion budget `k`. -/
def visit [DecidableEq V] (adj : V → List V) : ℕ → V → State V → State V
  | 0, _, s => s
  | k + 1, u, s =>
    if u ∈ s.visited then s
    else
      let t := (adj u).foldl (fun t v => visit adj k v t) ⟨insert u s.visited, s.finished⟩
      ⟨t.visited, u :: t.finished⟩

/-- Depth-first search from each root in turn. -/
def dfs [DecidableEq V] (adj : V → List V) (k : ℕ) (roots : List V) : State V :=
  roots.foldl (fun s u => visit adj k u s) ⟨∅, []⟩

/-- The total out-degree of a list of vertices. -/
def outDegreeSum (adj : V → List V) (l : List V) : ℕ := (l.map fun v => (adj v).length).sum

variable {adj : V → List V}

section Unfold

variable [DecidableEq V]

theorem visit_zero (u : V) (s : State V) : visit adj 0 u s = s := rfl

theorem visit_of_mem {k : ℕ} {u : V} {s : State V} (h : u ∈ s.visited) :
    visit adj (k + 1) u s = s := by
  simp [visit, h]

theorem visit_of_notMem {k : ℕ} {u : V} {s : State V} (h : u ∉ s.visited) :
    visit adj (k + 1) u s =
      ⟨((adj u).foldl (fun t v => visit adj k v t) ⟨insert u s.visited, s.finished⟩).visited,
        u :: ((adj u).foldl (fun t v => visit adj k v t)
          ⟨insert u s.visited, s.finished⟩).finished⟩ := by
  simp [visit, h]

/-- `visit` only prepends newly finished vertices onto `s.finished`, without reading it. -/
theorem visit_eq_of_nil :
    ∀ (k : ℕ) (u : V) (vis : Finset V) (fin : List V),
      visit adj k u ⟨vis, fin⟩ =
        ⟨(visit adj k u ⟨vis, []⟩).visited, (visit adj k u ⟨vis, []⟩).finished ++ fin⟩
  | 0, _, _, _ => rfl
  | k + 1, u, vis, fin => by
    by_cases hu : u ∈ vis
    · simp [visit, hu]
    · have hfold : ∀ (l : List V) (v₀ : Finset V) (f₀ : List V),
          l.foldl (fun t v => visit adj k v t) ⟨v₀, f₀ ++ fin⟩ =
            ⟨(l.foldl (fun t v => visit adj k v t) ⟨v₀, f₀⟩).visited,
              (l.foldl (fun t v => visit adj k v t) ⟨v₀, f₀⟩).finished ++ fin⟩ := by
        intro l
        induction l with
        | nil => intro v₀ f₀; rfl
        | cons w l ih =>
          intro v₀ f₀
          simp only [List.foldl_cons, visit_eq_of_nil k w v₀ (f₀ ++ fin)]
          rw [← List.append_assoc, ih, ← visit_eq_of_nil k w v₀ f₀]
      simp only [visit, hu, ↓reduceIte]
      simpa using congrArg (fun s : State V => State.mk s.visited (u :: s.finished))
        (hfold (adj u) (insert u vis) [])

end Unfold

section Proof

private theorem exists_step_notMem {R : V → V → Prop} {S : Finset V} {x y : V}
    (hxy : Relation.ReflTransGen R x y) (hx : x ∈ S) (hy : y ∉ S) :
    ∃ w w', w ∈ S ∧ w' ∉ S ∧ Relation.ReflTransGen R x w ∧ R w w' := by
  induction hxy with
  | refl => exact absurd hx hy
  | @tail b c hab hbc ih =>
    by_cases hb : b ∈ S
    · exact ⟨b, c, hb, hy, hab, hbc⟩
    · exact ih hb

/-- The invariant of depth-first search. -/
private structure Inv (adj : V → List V) (s : State V) : Prop where
  nodup : s.finished.Nodup
  finished_subset : ∀ x ∈ s.finished, x ∈ s.visited
  closed : ∀ x ∈ s.finished, ∀ y ∈ adj x, y ∈ s.visited
  order : ∀ x ∈ s.finished, ∀ y ∈ adj x,
    [x, y] <+ s.finished ∨ Relation.ReflTransGen (Edge adj) y x
  scc_order : ∀ x ∈ s.finished, ∀ y, Relation.ReflTransGen (Edge adj) x y →
    ¬ Relation.ReflTransGen (Edge adj) y x →
    (∃ z, StronglyConnected adj x z ∧ [z, y] <+ s.finished) ∨
      ∃ z ∈ s.visited, z ∉ s.finished ∧ StronglyConnected adj x z

/-- Finishing prepends distinct vertices that were undiscovered in the starting state. -/
private def Ext (s s' : State V) : Prop :=
  ∃ new : List V, s'.finished = new ++ s.finished ∧ new.Nodup ∧
    (∀ x ∈ new, x ∉ s.visited) ∧ ∀ x, x ∈ s'.visited ↔ x ∈ s.visited ∨ x ∈ new

private theorem Ext.refl (s : State V) : Ext s s :=
  ⟨[], rfl, List.nodup_nil, by simp, by simp⟩

private theorem Ext.visited_subset {s s' : State V} (h : Ext s s') : s.visited ⊆ s'.visited := by
  obtain ⟨_, _, _, _, hv⟩ := h
  exact fun x hx => (hv x).mpr (.inl hx)

private theorem Ext.trans {s₁ s₂ s₃ : State V} (h₁ : Ext s₁ s₂) (h₂ : Ext s₂ s₃) : Ext s₁ s₃ := by
  obtain ⟨n₁, hf₁, hn₁, hd₁, hv₁⟩ := h₁
  obtain ⟨n₂, hf₂, hn₂, hd₂, hv₂⟩ := h₂
  have hnd : (n₂ ++ n₁).Nodup := List.nodup_append.mpr ⟨hn₂, hn₁,
    fun x hx y hy hxy => hd₂ x hx ((hv₁ x).mpr (.inr (by simpa only [hxy] using hy)))⟩
  refine ⟨n₂ ++ n₁, by rw [hf₂, hf₁, List.append_assoc], hnd, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact fun h => hd₂ x hx ((hv₁ x).mpr (.inl h))
    · exact hd₁ x hx
  · intro x
    rw [hv₂, hv₁, List.mem_append]
    tauto

private theorem Ext.finish [DecidableEq V] {s t : State V} {u : V}
    (hu : u ∉ s.visited) (ht : Ext ⟨insert u s.visited, s.finished⟩ t) :
    Ext s ⟨t.visited, u :: t.finished⟩ := by
  obtain ⟨new, hnew, hnd, hdis, hvis⟩ := ht
  refine ⟨u :: new, congrArg (u :: ·) hnew, List.nodup_cons.mpr
    ⟨fun hm => hdis u hm (Finset.mem_insert_self _ _), hnd⟩, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hu
    · exact fun h => hdis x hx (Finset.mem_insert_of_mem h)
  · intro x
    simp only [hvis, Finset.mem_insert, List.mem_cons]
    tauto

private theorem foldl_ext {f : State V → V → State V} (hf : ∀ s v, Ext s (f s v))
    (roots : List V) (s : State V) : Ext s (roots.foldl f s) :=
  roots.foldlRecOn f (Ext.refl s) fun t ht v _ => ht.trans (hf t v)

private theorem visit_ext [DecidableEq V] (adj : V → List V) :
    ∀ k u s, Ext s (visit adj k u s)
  | 0, _, s => Ext.refl s
  | k + 1, u, s => by
    by_cases hu : u ∈ s.visited
    · rw [visit_of_mem hu]
      exact Ext.refl s
    · rw [visit_of_notMem hu]
      exact Ext.finish hu (foldl_ext (fun t v => visit_ext adj k v t) (adj u) _)

/-- Starting with an empty finishing list, the visit lists each newly discovered vertex
exactly once. This holds for every fuel and starting visited set. -/
theorem visit_nil_struct [DecidableEq V] (adj : V → List V) (k : ℕ) (u : V) (vis : Finset V) :
    let s := visit adj k u ⟨vis, []⟩
    s.finished.Nodup ∧ (∀ x ∈ s.finished, x ∉ vis) ∧
      (∀ x, x ∈ s.visited ↔ x ∈ vis ∨ x ∈ s.finished) := by
  obtain ⟨new, hnew, hnd, hdis, hvis⟩ := visit_ext adj k u ⟨vis, []⟩
  simp only [List.append_nil] at hnew
  exact ⟨hnew ▸ hnd, hnew ▸ hdis, hnew ▸ hvis⟩

/-- A visit increases the visited cardinality by the number of newly finished vertices. -/
theorem card_visit_nil [DecidableEq V] (adj : V → List V) (k : ℕ) (u : V) (vis : Finset V) :
    (visit adj k u ⟨vis, []⟩).visited.card =
      vis.card + (visit adj k u ⟨vis, []⟩).finished.length := by
  obtain ⟨hnd, hdis, hvis⟩ := visit_nil_struct adj k u vis
  have hdisj : Disjoint vis (visit adj k u ⟨vis, []⟩).finished.toFinset :=
    Finset.disjoint_right.mpr fun x hx => hdis x (List.mem_toFinset.mp hx)
  have hunion : (visit adj k u ⟨vis, []⟩).visited =
      vis ∪ (visit adj k u ⟨vis, []⟩).finished.toFinset := by
    ext x
    simp [hvis x]
  rw [hunion, Finset.card_union_of_disjoint hdisj, List.toFinset_card_of_nodup hnd]

/-- A gray vertex of `s'` (discovered, unfinished) was already gray in `s`. -/
private theorem Ext.gray {s s' : State V} (h : Ext s s') {x : V} (hx : x ∈ s'.visited)
    (hxf : x ∉ s'.finished) : x ∈ s.visited ∧ x ∉ s.finished := by
  obtain ⟨n, hf, _, _, hv⟩ := h
  rw [hf, List.mem_append, not_or] at hxf
  rcases (hv x).1 hx with h | h
  · exact ⟨h, hxf.2⟩
  · exact absurd h hxf.1

private theorem visit_spec [DecidableEq V] [Fintype V] :
    ∀ (k : ℕ) (u : V) (s : State V), Inv adj s →
      Fintype.card V - s.visited.card ≤ k →
      (∀ x ∈ s.visited, x ∉ s.finished → Relation.ReflTransGen (Edge adj) x u) →
      Inv adj (visit adj k u s) ∧ u ∈ (visit adj k u s).visited ∧
        ∀ x ∈ (visit adj k u s).visited, x ∈ s.visited ∨ Relation.ReflTransGen (Edge adj) u x
  | 0, u, s, hI, hk, _ => by
    have huniv : s.visited = Finset.univ :=
      Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) (by omega))
    exact ⟨hI, (huniv ▸ Finset.mem_univ u : u ∈ s.visited), fun x hx => .inl hx⟩
  | k + 1, u, s, hI, hk, hgray => by
    by_cases hu : u ∈ s.visited
    · rw [visit_of_mem hu]
      exact ⟨hI, hu, fun x hx => .inl hx⟩
    have hfold : ∀ l : List V, (∀ v ∈ l, v ∈ adj u) → ∀ t : State V, Inv adj t →
        Fintype.card V - t.visited.card ≤ k →
        (∀ x ∈ t.visited, x ∉ t.finished → Relation.ReflTransGen (Edge adj) x u) →
        Inv adj (l.foldl (fun t v => visit adj k v t) t) ∧
          (∀ v ∈ l, v ∈ (l.foldl (fun t v => visit adj k v t) t).visited) ∧
          ∀ x ∈ (l.foldl (fun t v => visit adj k v t) t).visited,
            x ∈ t.visited ∨ Relation.ReflTransGen (Edge adj) u x := by
      intro l
      induction l with
      | nil => intro _ t hI _ _; exact ⟨hI, by simp, fun x hx => .inl hx⟩
      | cons v l ih =>
        intro hl t hIt hkt hgt
        have hv : Edge adj u v := hl v List.mem_cons_self
        obtain ⟨hI₁, hv₁, hr₁⟩ := visit_spec k v t hIt hkt fun x hx hxf =>
          (hgt x hx hxf).tail hv
        have hE₁ := visit_ext adj k v t
        have hk₁ : Fintype.card V - (visit adj k v t).visited.card ≤ k := by
          have := Finset.card_le_card hE₁.visited_subset
          omega
        obtain ⟨hI₂, hv₂, hr₂⟩ := ih (fun w hw => hl w (List.mem_cons_of_mem _ hw)) _ hI₁
          hk₁ fun x hx hxf => by
            obtain ⟨hx', hxf'⟩ := hE₁.gray hx hxf
            exact hgt x hx' hxf'
        have hE₂ := foldl_ext (fun t v => visit_ext adj k v t) l (visit adj k v t)
        rw [List.foldl_cons]
        exact ⟨hI₂, List.forall_mem_cons.2 ⟨hE₂.visited_subset hv₁, hv₂⟩,
          fun x hx => (hr₂ x hx).elim (fun hx => (hr₁ x hx).imp id (.head hv)) .inr⟩
    rw [visit_of_notMem hu]
    set s₀ : State V := ⟨insert u s.visited, s.finished⟩ with hs₀
    have hI₀ : Inv adj s₀ :=
      { nodup := hI.nodup
        finished_subset := fun x hx => Finset.mem_insert_of_mem (hI.finished_subset x hx)
        closed := fun x hx y hy => Finset.mem_insert_of_mem (hI.closed x hx y hy)
        order := hI.order
        scc_order := fun x hx y hxy hnyx =>
          (hI.scc_order x hx y hxy hnyx).imp id fun ⟨z, hz, hzf, hxz⟩ =>
            ⟨z, Finset.mem_insert_of_mem hz, hzf, hxz⟩ }
    have hk₀ : Fintype.card V - s₀.visited.card ≤ k := by
      have := Finset.card_insert_of_notMem hu
      simp only [s₀]
      omega
    have hg₀ : ∀ x ∈ s₀.visited, x ∉ s₀.finished → Relation.ReflTransGen (Edge adj) x u := by
      intro x hx hxf
      obtain rfl | hx := Finset.mem_insert.1 hx
      exacts [.refl, hgray x hx hxf]
    obtain ⟨hIt, hvt, hrt⟩ := hfold (adj u) (fun v hv => hv) s₀ hI₀ hk₀ hg₀
    have hEt := foldl_ext (fun t v => visit_ext adj k v t) (adj u) s₀
    set t := (adj u).foldl (fun t v => visit adj k v t) s₀ with ht
    obtain ⟨new, hnew, -, hdis, hvis⟩ := id hEt
    have hut : u ∉ t.finished := by
      rw [hnew, List.mem_append, not_or]
      exact ⟨fun h => hdis u h (Finset.mem_insert_self _ _), fun h => hu (hI.finished_subset u h)⟩
    have hut' : u ∈ t.visited := (hvis u).2 (.inl (Finset.mem_insert_self _ _))
    have hf_sub' : ∀ x ∈ u :: t.finished, x ∈ t.visited :=
      List.forall_mem_cons.2 ⟨hut', hIt.finished_subset⟩
    have hclosed' : ∀ x ∈ u :: t.finished, ∀ y ∈ adj x, y ∈ t.visited :=
      List.forall_mem_cons.2 ⟨hvt, hIt.closed⟩
    refine ⟨?_, hut', ?_⟩
    · refine ⟨List.nodup_cons.2 ⟨hut, hIt.nodup⟩, hf_sub', hclosed', ?_, ?_⟩
      · intro x hx y hy
        rcases List.mem_cons.1 hx with rfl | hx
        · by_cases hyf : y ∈ t.finished
          · exact .inl ((List.singleton_sublist.2 hyf).cons_cons x)
          · obtain ⟨hy₀, hyf₀⟩ := hEt.gray (hvt y hy) hyf
            exact .inr (hg₀ y hy₀ hyf₀)
        · exact (hIt.order x hx y hy).imp (·.cons u) id
      · intro x hx y hxy hnyx
        by_cases hyt : y ∈ t.visited
        · by_cases hyf : y ∈ t.finished
          · rcases List.mem_cons.1 hx with rfl | hxt
            · exact .inl ⟨x, ⟨.refl, .refl⟩, (List.singleton_sublist.2 hyf).cons_cons x⟩
            · rcases hIt.scc_order x hxt y hxy hnyx with ⟨z, hxz, hsub⟩ | ⟨z, hzv, hzf, hxz⟩
              · exact .inl ⟨z, hxz, hsub.cons u⟩
              · by_cases hzu : z = u
                · exact .inl ⟨u, hzu ▸ hxz, (List.singleton_sublist.2 hyf).cons_cons u⟩
                · exact .inr ⟨z, hzv, List.not_mem_cons_of_ne_of_not_mem hzu hzf, hxz⟩
          · obtain ⟨hy₀, hyf₀⟩ := hEt.gray hyt hyf
            have hyu : Relation.ReflTransGen (Edge adj) y u := hg₀ y hy₀ hyf₀
            rcases List.mem_cons.1 hx with rfl | hxt
            · exact absurd hyu hnyx
            · rcases hIt.scc_order x hxt y hxy hnyx with ⟨z, _, hsub⟩ | ⟨z, hzv, hzf, hxz⟩
              · exact absurd (hsub.subset (by simp)) hyf
              · have hzu : z ≠ u := fun hzu => hnyx (hyu.trans (hzu ▸ hxz.2))
                exact .inr ⟨z, hzv, List.not_mem_cons_of_ne_of_not_mem hzu hzf, hxz⟩
        · obtain ⟨w, w', hwv, hw'v, hxw, hww'⟩ := exists_step_notMem hxy (hf_sub' x hx) hyt
          have hw_nf : w ∉ u :: t.finished := fun hwf => hw'v (hclosed' w hwf w' hww')
          have hw_tf : w ∉ t.finished := fun hwf => hw_nf (List.mem_cons_of_mem u hwf)
          obtain ⟨hw₀, hwf₀⟩ := hEt.gray hwv hw_tf
          have hwu : Relation.ReflTransGen (Edge adj) w u := hg₀ w hw₀ hwf₀
          rcases List.mem_cons.1 hx with rfl | hxt
          · exact .inr ⟨w, hwv, hw_nf, hxw, hwu⟩
          · rw [hnew, List.mem_append] at hxt
            rcases hxt with hxnew | hxs
            · have hxt' : x ∈ t.finished := by rw [hnew]; exact List.mem_append_left _ hxnew
              have hux : Relation.ReflTransGen (Edge adj) u x :=
                (hrt x (hIt.finished_subset x hxt')).resolve_left (hdis x hxnew)
              exact .inr ⟨w, hwv, hw_nf, hxw, hwu.trans hux⟩
            · rcases hI.scc_order x hxs y hxy hnyx with ⟨z, _, hsub⟩ | ⟨z, hzv, hzf, hxz⟩
              · exact absurd (hEt.visited_subset (Finset.mem_insert_of_mem
                  (hI.finished_subset y (hsub.subset (by simp))))) hyt
              · have hzu : z ≠ u := fun h => hu (h ▸ hzv)
                have hzn : z ∉ new := fun hzn => hdis z hzn (Finset.mem_insert_of_mem hzv)
                have hzf' : z ∉ u :: t.finished := by
                  simp only [List.mem_cons, hnew, List.mem_append, not_or]
                  exact ⟨hzu, hzn, hzf⟩
                exact .inr ⟨z, hEt.visited_subset (Finset.mem_insert_of_mem hzv), hzf', hxz⟩
    · intro x hx
      obtain hx | hx := hrt x hx
      · obtain rfl | hx := Finset.mem_insert.1 hx
        exacts [.inr .refl, .inl hx]
      · exact .inr hx

private theorem foldl_visit_spec [DecidableEq V] [Fintype V] {k : ℕ} (hk : Fintype.card V ≤ k) :
    ∀ (roots : List V) (s : State V), Inv adj s → (∀ x ∈ s.visited, x ∈ s.finished) →
      Inv adj (roots.foldl (fun s u => visit adj k u s) s) ∧
        (∀ x ∈ (roots.foldl (fun s u => visit adj k u s) s).visited,
          x ∈ (roots.foldl (fun s u => visit adj k u s) s).finished) ∧
        (∀ u ∈ roots, u ∈ (roots.foldl (fun s u => visit adj k u s) s).visited) ∧
        ∀ x ∈ (roots.foldl (fun s u => visit adj k u s) s).visited,
          x ∈ s.visited ∨ ∃ r ∈ roots, Relation.ReflTransGen (Edge adj) r x
  | [], s, hI, hb => ⟨hI, hb, by simp, fun x hx => .inl hx⟩
  | r :: roots, s, hI, hb => by
    obtain ⟨hI₁, hr₁, hR₁⟩ := visit_spec k r s hI (by omega) fun x hx hxf =>
      absurd (hb x hx) hxf
    have hE₁ := visit_ext adj k r s
    have hb₁ : ∀ x ∈ (visit adj k r s).visited, x ∈ (visit adj k r s).finished := by
      intro x hx
      by_contra hxf
      obtain ⟨hx', hxf'⟩ := hE₁.gray hx hxf
      exact hxf' (hb x hx')
    obtain ⟨hI₂, hb₂, hr₂, hR₂⟩ := foldl_visit_spec hk roots _ hI₁ hb₁
    have hE₂ := foldl_ext (fun t v => visit_ext adj k v t) roots (visit adj k r s)
    rw [List.foldl_cons]
    refine ⟨hI₂, hb₂, List.forall_mem_cons.2 ⟨hE₂.visited_subset hr₁, hr₂⟩, ?_⟩
    intro x hx
    rcases hR₂ x hx with hx | ⟨r', hr', hx⟩
    · exact (hR₁ x hx).imp id fun hx => ⟨r, List.mem_cons_self, hx⟩
    · exact .inr ⟨r', List.mem_cons_of_mem _ hr', hx⟩

private theorem dfs_spec [DecidableEq V] [Fintype V] {k : ℕ} (hk : Fintype.card V ≤ k)
    (roots : List V) :
    Inv adj (dfs adj k roots) ∧
      (∀ x ∈ (dfs adj k roots).visited, x ∈ (dfs adj k roots).finished) ∧
      (∀ u ∈ roots, u ∈ (dfs adj k roots).visited) ∧
      ∀ x ∈ (dfs adj k roots).visited, ∃ r ∈ roots, Relation.ReflTransGen (Edge adj) r x := by
  obtain ⟨hI, hb, hr, hR⟩ := foldl_visit_spec (adj := adj) hk roots ⟨∅, []⟩
    ⟨List.nodup_nil, by simp, by simp, by simp, by simp⟩ (by simp)
  exact ⟨hI, hb, hr, fun x hx => (hR x hx).resolve_left (by simp)⟩

end Proof

section Results

variable [DecidableEq V] [Fintype V] {k : ℕ}

/-- **Depth-first search finds the reachable vertices.** -/
theorem mem_dfs_visited_iff (hk : Fintype.card V ≤ k) (roots : List V) (v : V) :
    v ∈ (dfs adj k roots).visited ↔ ∃ r ∈ roots, Relation.ReflTransGen (Edge adj) r v := by
  obtain ⟨hI, hb, hr, hR⟩ := dfs_spec (adj := adj) hk roots
  refine ⟨hR v, ?_⟩
  rintro ⟨r, hr', hrv⟩
  induction hrv with
  | refl => exact hr r hr'
  | tail _ hyz ih => exact hI.closed _ (hb _ ih) _ hyz

theorem mem_dfs_finished_iff (hk : Fintype.card V ≤ k) (roots : List V) (v : V) :
    v ∈ (dfs adj k roots).finished ↔ ∃ r ∈ roots, Relation.ReflTransGen (Edge adj) r v := by
  obtain ⟨hI, hb, -, -⟩ := dfs_spec (adj := adj) hk roots
  rw [← mem_dfs_visited_iff hk]
  exact ⟨hI.finished_subset v, hb v⟩

theorem nodup_dfs_finished (hk : Fintype.card V ≤ k) (roots : List V) :
    (dfs adj k roots).finished.Nodup :=
  (dfs_spec (adj := adj) hk roots).1.nodup

/-- **No back edges in the finishing order, up to cycles.** -/
theorem dfs_finished_order (hk : Fintype.card V ≤ k) (roots : List V) {u v : V}
    (hu : u ∈ (dfs adj k roots).finished) (huv : Edge adj u v) :
    [u, v] <+ (dfs adj k roots).finished ∨ Relation.ReflTransGen (Edge adj) v u :=
  (dfs_spec (adj := adj) hk roots).1.order u hu v huv

/-- **Component finishing order**: if a finished vertex `u` reaches `v` while `v` does not reach
`u`, then some vertex `z` mutually reachable with `u` finishes after `v` (appears before `v` in
`finished`). -/
theorem dfs_scc_finished_order (hk : Fintype.card V ≤ k) (roots : List V) {u v : V}
    (hu : u ∈ (dfs adj k roots).finished) (huv : Relation.ReflTransGen (Edge adj) u v)
    (hnvu : ¬ Relation.ReflTransGen (Edge adj) v u) :
    ∃ z, StronglyConnected adj u z ∧ [z, v] <+ (dfs adj k roots).finished := by
  obtain ⟨hI, hb, -, -⟩ := dfs_spec (adj := adj) hk roots
  exact (hI.scc_order u hu v huv hnvu).resolve_right fun ⟨z, hzv, hzf, _⟩ => hzf (hb z hzv)

end Results

end Cslib.Algorithms.Lean.DFS
