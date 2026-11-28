/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.DFS.TopologicalSort
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Strongly connected components

Kosaraju's algorithm for the strongly connected components of a directed graph given by adjacency
lists `adj : V → List V`, together with their condensation topological order, following
[Cormen et al.][CLRS2009] (see also [Tarjan][Tarjan1972]). Linear-time iterative execution on the
standard-basis word RAM is proved in `CslibFrontier.Algorithms.WordRAM.DFS`.

From a vertex list `vs` covering `V`, `Cslib.Algorithms.Lean.DFS.sccs adj vs`:
1. computes the finishing order `ord = topologicalSort adj vs` of depth-first search on `adj`;
2. builds the transpose adjacency lists `transposeAdj adj vs` by scanning `vs` and `adj u`;
3. traverses `ord` in the transpose graph (`peelSCCs`), emitting each newly reached tree as one
   strongly connected component.

Because the component finishing lemma (`dfs_scc_finished_order`) places at least one vertex of
every upstream component before every vertex of a downstream component in `ord`, each root peeled
in `transposeAdj adj vs` sees no unvisited upstream vertices and visits its exact strongly
connected component. Moreover, emitted components appear in forward topological order of the
condensation DAG: every edge `u → v` goes from a component of index `i` to a component of index
`j` with `i ≤ j`.

## Main definitions

* `Cslib.Algorithms.Lean.DFS.IsSCCCondensation`: specification of a duplicate-free partition of `V`
  into nonempty `StronglyConnected` classes ordered topologically.
* `Cslib.Algorithms.Lean.DFS.transposeAdj`: transpose adjacency lists.
* `Cslib.Algorithms.Lean.DFS.peelSCCs`, `Cslib.Algorithms.Lean.DFS.sccs`: Kosaraju's second pass
  and two-pass SCC decomposition.
* `Cslib.Algorithms.Lean.DFS.indexComponentsAux`, `Cslib.Algorithms.Lean.DFS.indexComponents`: map
  each vertex to its component's topological index.

## Main results

* `Cslib.Algorithms.Lean.DFS.sum_length_transposeAdj`: total length of transpose adjacency lists
  equals `outDegreeSum adj vs`.
* `Cslib.Algorithms.Lean.DFS.isSCCCondensation_sccs`: when `vs` lists every vertex, `sccs adj vs`
  satisfies `IsSCCCondensation adj`.
* `Cslib.Algorithms.Lean.DFS.IsSCCCondensation.indexComponents_eq_iff`,
  `Cslib.Algorithms.Lean.DFS.IsSCCCondensation.indexComponents_le_of_edge`: component-index
  equivalence and condensation monotonicity.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
* [R. E. Tarjan, *Depth-first search and linear graph algorithms*][Tarjan1972]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.DFS

open scoped List

variable {V : Type*}

/-! ### Condensation specification -/

/-- A topological decomposition of `(V, adj)` into strongly connected components: nonempty lists
partitioning `V` without duplicates, each an equivalence class of `StronglyConnected adj`, ordered
so every edge `u → v` has `u`'s component index at most `v`'s. -/
structure IsSCCCondensation (adj : V → List V) (comps : List (List V)) : Prop where
  /-- Every component is nonempty. -/
  ne_nil : ∀ c ∈ comps, c ≠ []
  /-- Across all components, no vertex appears twice. -/
  nodup_flatten : comps.flatten.Nodup
  /-- Every vertex appears in some component. -/
  mem_flatten : ∀ v, v ∈ comps.flatten
  /-- Two vertices share a component if and only if they are mutually reachable. -/
  same_comp_iff : ∀ u v, (∃ c ∈ comps, u ∈ c ∧ v ∈ c) ↔ StronglyConnected adj u v
  /-- Every edge `u → v` goes from component `i` to component `j` with `i ≤ j`. -/
  condensation_le : ∀ {i j : ℕ} (hi : i < comps.length) (hj : j < comps.length) {u v : V},
    u ∈ comps[i] → v ∈ comps[j] → Edge adj u v → i ≤ j

/-! ### Transpose adjacency lists -/

/-- Reverse every adjacency-list arc emanating from `vs`. -/
def transposeAdj [DecidableEq V] (adj : V → List V) (vs : List V) : V → List V :=
  vs.foldl (fun rev u => (adj u).foldl (fun rev v => Function.update rev v (u :: rev v)) rev)
    (fun _ => [])

section Transpose

variable [DecidableEq V] {adj : V → List V}

private theorem foldl_transpose_mem (u : V) :
    ∀ (l : List V) (rev : V → List V) (w x : V),
      x ∈ (l.foldl (fun rev v => Function.update rev v (u :: rev v)) rev) w ↔
        x ∈ rev w ∨ (x = u ∧ w ∈ l)
  | [], rev, w, x => by simp
  | v :: l, rev, w, x => by
    rw [List.foldl_cons, foldl_transpose_mem]
    by_cases hwv : w = v
    · subst hwv
      simp only [Function.update_self, List.mem_cons]
      tauto
    · simp only [Function.update_of_ne hwv, List.mem_cons]
      tauto

private theorem foldl_vs_transpose_mem :
    ∀ (vs : List V) (rev : V → List V) (w x : V),
      x ∈ (vs.foldl
          (fun rev u => (adj u).foldl (fun rev v => Function.update rev v (u :: rev v)) rev)
          rev) w ↔
        x ∈ rev w ∨ (x ∈ vs ∧ w ∈ adj x)
  | [], rev, w, x => by simp
  | u :: vs, rev, w, x => by
    rw [List.foldl_cons, foldl_vs_transpose_mem, foldl_transpose_mem]
    simp only [List.mem_cons]
    constructor
    · rintro ((hx | ⟨rfl, hw⟩) | ⟨hx, hw⟩)
      · exact .inl hx
      · exact .inr ⟨.inl rfl, hw⟩
      · exact .inr ⟨.inr hx, hw⟩
    · rintro (hx | ⟨rfl | hx, hw⟩)
      · exact .inl (.inl hx)
      · exact .inl (.inr ⟨rfl, hw⟩)
      · exact .inr ⟨hx, hw⟩

theorem mem_transposeAdj {vs : List V} {w x : V} :
    x ∈ transposeAdj adj vs w ↔ x ∈ vs ∧ w ∈ adj x := by
  simpa [transposeAdj] using foldl_vs_transpose_mem (adj := adj) vs (fun _ => []) w x

theorem edge_transposeAdj_iff {vs : List V} (hvs : ∀ v, v ∈ vs) {u v : V} :
    Edge (transposeAdj adj vs) u v ↔ Edge adj v u := by
  simp [Edge, mem_transposeAdj, hvs v]

theorem reflTransGen_edge_transposeAdj_iff {vs : List V} (hvs : ∀ v, v ∈ vs) {u v : V} :
    Relation.ReflTransGen (Edge (transposeAdj adj vs)) u v ↔
      Relation.ReflTransGen (Edge adj) v u := by
  have hrel : Edge (transposeAdj adj vs) = Function.swap (Edge adj) :=
    funext fun a => funext fun b => propext (edge_transposeAdj_iff hvs)
  rw [hrel, Relation.reflTransGen_swap]

omit [DecidableEq V] in
/-- Consing onto one adjacency-list entry increases the total adjacency-list length by `1`. -/
theorem sum_length_update_cons {α β : Type*} [DecidableEq α] [Fintype α] (f : α → List β)
    (u : α) (v : β) :
    (∑ w, (Function.update f u (v :: f u) w).length) = (∑ w, (f w).length) + 1 := by
  change (∑ w, (List.length ∘ Function.update f u (v :: f u)) w) = _
  rw [Function.comp_update List.length f u (v :: f u)]
  change (∑ w, Function.update (fun w => (f w).length) u (v :: f u).length w) = _
  rw [Finset.sum_update_of_mem (Finset.mem_univ u)]
  rw [← Finset.add_sum_erase _ (fun w => (f w).length) (Finset.mem_univ u)]
  rw [List.length_cons]
  rw [Finset.erase_eq]
  omega

private theorem sum_length_foldl_update [Fintype V] (u : V) :
    ∀ (l : List V) (rev : V → List V),
      (∑ w, ((l.foldl (fun rev v => Function.update rev v (u :: rev v)) rev) w).length) =
        (∑ w, (rev w).length) + l.length
  | [], rev => by simp
  | v :: l, rev => by
    rw [List.foldl_cons, sum_length_foldl_update u l, List.length_cons, sum_length_update_cons]
    omega

private theorem sum_length_foldl_vs [Fintype V] :
    ∀ (vs : List V) (rev : V → List V),
      (∑ w, ((vs.foldl
          (fun rev u => (adj u).foldl (fun rev v => Function.update rev v (u :: rev v)) rev)
          rev) w).length) =
        (∑ w, (rev w).length) + outDegreeSum adj vs
  | [], rev => by simp [outDegreeSum]
  | u :: vs, rev => by
    rw [List.foldl_cons, sum_length_foldl_vs, sum_length_foldl_update]
    simp only [outDegreeSum, List.map_cons, List.sum_cons]
    omega

theorem sum_length_transposeAdj [Fintype V] (adj : V → List V) (vs : List V) :
    (∑ w, (transposeAdj adj vs w).length) = outDegreeSum adj vs := by
  simpa [transposeAdj] using sum_length_foldl_vs (adj := adj) vs (fun _ => [])

end Transpose

/-- `outDegreeSum` is additive over list concatenation. -/
theorem outDegreeSum_append (g : V → List V) (a b : List V) :
    outDegreeSum g (a ++ b) = outDegreeSum g a + outDegreeSum g b := by
  simp [outDegreeSum, List.map_append, List.sum_append]

/-! ### Kosaraju's second pass -/

/-- Peel strongly connected components in `revAdj` along finishing order `rs`. -/
def peelSCCs [DecidableEq V] (revAdj : V → List V) (k : ℕ) :
    Finset V → List V → List (List V)
  | _, [] => []
  | vis, r :: rs =>
    let s := visit revAdj k r ⟨vis, []⟩
    if s.finished.isEmpty then peelSCCs revAdj k s.visited rs
    else s.finished :: peelSCCs revAdj k s.visited rs

/-- **Kosaraju's algorithm**: compute strongly connected components in condensation topological
order from a vertex list `vs`. -/
def sccs [DecidableEq V] (adj : V → List V) (vs : List V) : List (List V) :=
  peelSCCs (transposeAdj adj vs) vs.length ∅ (topologicalSort adj vs)

section KosarajuProof

variable [DecidableEq V] {adj : V → List V}

omit [DecidableEq V] in
private theorem reach_of_closed {g : V → List V} {vis : Finset V}
    (hcl : ∀ u ∈ vis, ∀ v ∈ g u, v ∈ vis) {u w : V} (hu : u ∈ vis)
    (h : Relation.ReflTransGen (Edge g) u w) : w ∈ vis := by
  induction h with
  | refl => exact hu
  | tail _ hbc ih => exact hcl _ ih _ hbc

private theorem dfs_visited_of_closed [Fintype V] {g : V → List V} {k : ℕ}
    (hk : Fintype.card V ≤ k) {vis : Finset V} (hcl : ∀ u ∈ vis, ∀ v ∈ g u, v ∈ vis) :
    (dfs g k vis.toList).visited = vis := by
  ext w
  rw [mem_dfs_visited_iff hk]
  simp only [Finset.mem_toList]
  exact ⟨fun ⟨u, hu, huw⟩ => reach_of_closed hcl hu huw, fun hw => ⟨w, hw, .refl⟩⟩

private theorem visit_nil_spec [Fintype V] {g : V → List V} {k : ℕ}
    (hk : Fintype.card V ≤ k) {vis : Finset V} (hcl : ∀ u ∈ vis, ∀ v ∈ g u, v ∈ vis) (r : V) :
    (∀ w, w ∈ (visit g k r ⟨vis, []⟩).visited ↔
        w ∈ vis ∨ Relation.ReflTransGen (Edge g) r w) ∧
      (visit g k r ⟨vis, []⟩).finished.Nodup ∧
      (∀ w, w ∈ (visit g k r ⟨vis, []⟩).finished ↔
        w ∉ vis ∧ Relation.ReflTransGen (Edge g) r w) := by
  have hd_eq : dfs g k vis.toList = ⟨vis, (dfs g k vis.toList).finished⟩ := by
    cases hd : dfs g k vis.toList with
    | mk v f =>
      have hv : v = vis := by simpa [hd] using dfs_visited_of_closed hk hcl
      simp [hv]
  have hsplit :
      dfs g k (vis.toList ++ [r]) =
        ⟨(visit g k r ⟨vis, []⟩).visited,
          (visit g k r ⟨vis, []⟩).finished ++ (dfs g k vis.toList).finished⟩ := by
    dsimp [dfs]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change visit g k r (dfs g k vis.toList) =
      ⟨(visit g k r ⟨vis, []⟩).visited,
        (visit g k r ⟨vis, []⟩).finished ++ (dfs g k vis.toList).finished⟩
    rw [hd_eq, visit_eq_of_nil]
  have hvis : ∀ w, w ∈ (visit g k r ⟨vis, []⟩).visited ↔
      w ∈ vis ∨ Relation.ReflTransGen (Edge g) r w := fun w => by
    have hm := mem_dfs_visited_iff (adj := g) hk (vis.toList ++ [r]) w
    simp only [hsplit, List.mem_append, Finset.mem_toList, List.mem_singleton] at hm
    rw [hm]
    exact ⟨fun ⟨u, hu, huw⟩ =>
        hu.elim (fun huv => .inl (reach_of_closed hcl huv huw)) (fun hur => .inr (hur ▸ huw)),
      fun h => h.elim (fun hw => ⟨w, .inl hw, .refl⟩) (fun hrw => ⟨r, .inr rfl, hrw⟩)⟩
  have hfin_prev : ∀ w, w ∈ (dfs g k vis.toList).finished ↔ w ∈ vis := fun w => by
    rw [mem_dfs_finished_iff hk, ← mem_dfs_visited_iff hk, dfs_visited_of_closed hk hcl]
  have hnd_all :
      ((visit g k r ⟨vis, []⟩).finished ++ (dfs g k vis.toList).finished).Nodup := by
    simpa only [hsplit] using nodup_dfs_finished (adj := g) hk (vis.toList ++ [r])
  refine ⟨hvis, hnd_all.of_append_left, fun w => ?_⟩
  have hdisj := List.disjoint_of_nodup_append hnd_all
  have hm := mem_dfs_finished_iff (adj := g) hk (vis.toList ++ [r]) w
  rw [← mem_dfs_visited_iff hk, hsplit, List.mem_append, hfin_prev, hvis] at hm
  refine ⟨fun hw => ?_, fun ⟨hnv, hrw⟩ => (hm.2 (.inr hrw)).resolve_right hnv⟩
  have hnv : w ∉ vis := fun hwv => hdisj hw ((hfin_prev w).2 hwv)
  exact ⟨hnv, (hm.1 (.inl hw)).resolve_left hnv⟩

omit [DecidableEq V] in
private theorem not_sublist_two_head {z r : V} {rs : List V} (hr : r ∉ rs) :
    ¬ [z, r] <+ r :: rs := by
  intro hsub
  rcases List.sublist_cons_iff.1 hsub with h | ⟨l, hl, hl_sub⟩
  · exact hr (h.subset (by simp))
  · injection hl with _ hlr
    subst hlr
    exact hr (hl_sub.subset (by simp))

private theorem peelSCCs_spec [Fintype V] {vs : List V} (hvs : ∀ v, v ∈ vs)
    {k : ℕ} (hk : Fintype.card V ≤ k) :
    ∀ (rs : List V) (vis : Finset V),
      rs.Nodup →
      (∀ u ∈ vis, ∀ v ∈ transposeAdj adj vs u, v ∈ vis) →
      (∀ r ∈ rs, ∀ w, Relation.ReflTransGen (Edge adj) w r →
        ¬ Relation.ReflTransGen (Edge adj) r w →
        w ∈ vis ∨ ∃ z ∈ rs, StronglyConnected adj w z ∧ [z, r] <+ rs) →
      let comps := peelSCCs (transposeAdj adj vs) k vis rs
      (∀ c ∈ comps, c ≠ []) ∧
        comps.flatten.Nodup ∧
        (∀ w, w ∈ comps.flatten ↔
          w ∉ vis ∧ ∃ r ∈ rs, Relation.ReflTransGen (Edge adj) w r) ∧
        (∀ c ∈ comps, ∃ r, ∀ w, w ∈ c ↔ StronglyConnected adj r w) ∧
        (∀ {i j : ℕ} (hi : i < comps.length) (hj : j < comps.length) {u v : V},
          u ∈ comps[i] → v ∈ comps[j] → Edge adj u v → i ≤ j)
  | [], vis, _, _, _ => by simp [peelSCCs]
  | r :: rs, vis, hnd, hcl, hord => by
    obtain ⟨hr_not_rs, hrs_nd⟩ := List.nodup_cons.1 hnd
    set rev := transposeAdj adj vs
    obtain ⟨hvis_s, hnd_s, hfin_s⟩ := visit_nil_spec (g := rev) hk hcl r
    set s := visit rev k r ⟨vis, []⟩
    have hvis_adj : ∀ w, w ∈ s.visited ↔ w ∈ vis ∨ Relation.ReflTransGen (Edge adj) w r :=
      fun w => by rw [hvis_s, reflTransGen_edge_transposeAdj_iff hvs]
    have hfin_adj : ∀ w, w ∈ s.finished ↔ w ∉ vis ∧ Relation.ReflTransGen (Edge adj) w r :=
      fun w => by rw [hfin_s, reflTransGen_edge_transposeAdj_iff hvs]
    have hcl' : ∀ u ∈ s.visited, ∀ v ∈ rev u, v ∈ s.visited := fun u hu v huv => by
      rw [hvis_adj] at hu ⊢
      exact hu.imp (hcl u · v huv) (.head ((edge_transposeAdj_iff hvs).1 huv))
    have hord' : ∀ r' ∈ rs, ∀ w, Relation.ReflTransGen (Edge adj) w r' →
        ¬ Relation.ReflTransGen (Edge adj) r' w →
        w ∈ s.visited ∨ ∃ z ∈ rs, StronglyConnected adj w z ∧ [z, r'] <+ rs := by
      intro r' hr' w hwr' hnr'w
      rcases hord r' (List.mem_cons_of_mem r hr') w hwr' hnr'w with
        hw_vis | ⟨z, hz_mem, hwz, hz_sub⟩
      · exact .inl ((hvis_adj w).2 (.inl hw_vis))
      obtain rfl | hz_rs := List.mem_cons.1 hz_mem
      · exact .inl ((hvis_adj w).2 (.inr hwz.1))
      refine .inr ⟨z, hz_rs, hwz, (List.sublist_cons_iff.1 hz_sub).resolve_right ?_⟩
      rintro ⟨l, hl, -⟩
      exact hr_not_rs ((List.cons.inj hl).1 ▸ hz_rs)
    obtain ⟨ih_ne, ih_nd, ih_mem, ih_scc, ih_cond⟩ := peelSCCs_spec hvs hk rs s.visited hrs_nd
      hcl' hord'
    rw [peelSCCs]
    change (let comps := if s.finished.isEmpty then peelSCCs rev k s.visited rs
      else s.finished :: peelSCCs rev k s.visited rs; _)
    dsimp only
    split_ifs with he
    · have hnil : s.finished = [] := List.isEmpty_iff.1 he
      have hall_vis : ∀ w, Relation.ReflTransGen (Edge adj) w r → w ∈ vis := fun w hwr =>
        Classical.byContradiction fun hnv => by simpa [hnil] using (hfin_adj w).2 ⟨hnv, hwr⟩
      refine ⟨ih_ne, ih_nd, fun w => ?_, ih_scc, ih_cond⟩
      rw [ih_mem, hvis_adj]
      by_cases hwr : Relation.ReflTransGen (Edge adj) w r
      · simp [hwr, hall_vis w hwr]
      · simp [hwr]
    · have hne : s.finished ≠ [] := fun hnil => he (List.isEmpty_iff.2 hnil)
      have hr_nvis : r ∉ vis := fun hrv => by
        obtain ⟨x₀, hx₀⟩ := List.exists_mem_of_ne_nil s.finished hne
        obtain ⟨hnx₀, hx₀r⟩ := (hfin_adj x₀).1 hx₀
        exact hnx₀ (reach_of_closed hcl hrv ((reflTransGen_edge_transposeAdj_iff hvs).2 hx₀r))
      have hs_scc : ∀ w, w ∈ s.finished ↔ StronglyConnected adj r w := fun w => by
        rw [hfin_adj]
        exact ⟨fun ⟨hnv, hwr⟩ => ⟨Classical.byContradiction fun hnrw =>
            (hord r List.mem_cons_self w hwr hnrw).elim hnv
              fun ⟨_, _, _, hsub⟩ => not_sublist_two_head hr_not_rs hsub, hwr⟩,
          fun ⟨hrw, hwr⟩ => ⟨fun hwv => hr_nvis (reach_of_closed hcl hwv
            ((reflTransGen_edge_transposeAdj_iff hvs).2 hrw)), hwr⟩⟩
      set rest := peelSCCs rev k s.visited rs
      refine ⟨List.forall_mem_cons.2 ⟨hne, ih_ne⟩, ?_, fun w => ?_,
        List.forall_mem_cons.2 ⟨⟨r, hs_scc⟩, ih_scc⟩, ?_⟩
      · rw [List.flatten_cons, List.nodup_append]
        refine ⟨hnd_s, ih_nd, fun w hw₁ _ hw₂ hww' => ?_⟩
        subst hww'
        exact ((ih_mem w).1 hw₂).1 ((hvis_adj w).2 (.inr ((hfin_adj w).1 hw₁).2))
      · rw [List.flatten_cons, List.mem_append, hfin_adj, ih_mem, hvis_adj]
        by_cases hwr : Relation.ReflTransGen (Edge adj) w r <;> simp [hwr]
      · intro i j hi hj u v hu hv huv
        rcases i with _ | i'
        · exact Nat.zero_le j
        rcases j with _ | j'
        · simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at hi hu hv
          exact absurd (hcl' v ((hvis_adj v).2 (.inr ((hfin_adj v).1 hv).2)) u
            ((edge_transposeAdj_iff hvs).2 huv))
            ((ih_mem u).1 (List.mem_flatten.2 ⟨_, List.getElem_mem _, hu⟩)).1
        · simp only [List.length_cons, List.getElem_cons_succ] at hi hj hu hv
          exact Nat.succ_le_succ (ih_cond (by omega) (by omega) hu hv huv)

/-- **Correctness of Kosaraju's algorithm** [Cormen et al.][CLRS2009]: when `vs` lists every
vertex of `V`, `sccs adj vs` partitions `V` into nonempty strongly connected components in forward
condensation topological order. -/
theorem isSCCCondensation_sccs {vs : List V} (hvs : ∀ v, v ∈ vs) :
    IsSCCCondensation adj (sccs adj vs) := by
  let _ : Fintype V := Fintype.ofList vs hvs
  have hk : Fintype.card V ≤ vs.length := card_le_length hvs
  have hnd : (topologicalSort adj vs).Nodup := nodup_topologicalSort hvs
  have hmem_ord : ∀ v, v ∈ topologicalSort adj vs := mem_topologicalSort hvs
  have hord : ∀ r ∈ topologicalSort adj vs, ∀ w, Relation.ReflTransGen (Edge adj) w r →
      ¬ Relation.ReflTransGen (Edge adj) r w →
      w ∈ (∅ : Finset V) ∨
        ∃ z ∈ topologicalSort adj vs,
          StronglyConnected adj w z ∧ [z, r] <+ topologicalSort adj vs := by
    intro r _ w hwr hnrw
    obtain ⟨z, hwz, hsub⟩ :=
      dfs_scc_finished_order (adj := adj) hk vs (hmem_ord w) hwr hnrw
    exact .inr ⟨z, hmem_ord z, hwz, hsub⟩
  obtain ⟨hne, hnd_flat, hmem_flat, hscc, hcond⟩ :=
    peelSCCs_spec (adj := adj) hvs hk (topologicalSort adj vs) ∅ hnd (by simp) hord
  refine ⟨hne, hnd_flat, ?_, ?_, hcond⟩
  · intro v
    exact (hmem_flat v).2 ⟨Finset.notMem_empty v, v, hmem_ord v, .refl⟩
  · intro u v
    constructor
    · rintro ⟨c, hc, hu, hv⟩
      obtain ⟨r, hr⟩ := hscc c hc
      exact ((hr u).1 hu).symm.trans ((hr v).1 hv)
    · intro huv
      have hu_flat : u ∈ (sccs adj vs).flatten :=
        (hmem_flat u).2 ⟨Finset.notMem_empty u, u, hmem_ord u, .refl⟩
      obtain ⟨c, hc, hu⟩ := List.mem_flatten.1 hu_flat
      obtain ⟨r, hr⟩ := hscc c hc
      exact ⟨c, hc, hu, (hr v).2 (((hr u).1 hu).trans huv)⟩

end KosarajuProof

/-! ### Component-index table -/

/-- Auxiliary pass assigning each vertex in `c` its component index `idx`. -/
def indexComponentsAux [DecidableEq V] : ℕ → List (List V) → (V → ℕ) → V → ℕ
  | _, [], f => f
  | idx, c :: cs, f =>
    indexComponentsAux (idx + 1) cs (c.foldl (fun f v => Function.update f v idx) f)

/-- Map every vertex to the topological index of its component in `comps`. -/
def indexComponents [DecidableEq V] (comps : List (List V)) : V → ℕ :=
  indexComponentsAux 0 comps (fun _ => 0)

section IndexComponents

variable [DecidableEq V] {adj : V → List V}

/-- Folding constant updates over `c` sets exactly the members of `c` to `idx`. -/
theorem foldl_update_const (idx : ℕ) :
    ∀ (c : List V) (f : V → ℕ) (u : V),
      (c.foldl (fun f v => Function.update f v idx) f) u = if u ∈ c then idx else f u
  | [], f, u => by simp
  | v :: c, f, u => by
    rw [List.foldl_cons, foldl_update_const]
    by_cases huv : u = v
    · subst huv
      by_cases huc : u ∈ c <;> simp [huc]
    · simp [huv]

private theorem indexComponentsAux_notMem :
    ∀ (idx : ℕ) (cs : List (List V)) (f : V → ℕ) {u : V},
      u ∉ cs.flatten → indexComponentsAux idx cs f u = f u
  | _, [], f, _, _ => rfl
  | idx, c :: cs, f, u, hnu => by
    rw [List.flatten_cons, List.mem_append, not_or] at hnu
    rw [indexComponentsAux, indexComponentsAux_notMem (idx + 1) cs _ hnu.2,
      foldl_update_const, ite_eq_right (fun h => absurd h hnu.1)]

private theorem indexComponentsAux_getElem :
    ∀ (idx : ℕ) (cs : List (List V)) (f : V → ℕ),
      cs.flatten.Nodup →
      ∀ {i : ℕ} (hi : i < cs.length) {u : V}, u ∈ cs[i] →
        indexComponentsAux idx cs f u = idx + i
  | _, [], _, _, i, hi, _, _ => by simp at hi
  | idx, c :: cs, f, hnd, i, hi, u, hu => by
    rw [List.flatten_cons, List.nodup_append] at hnd
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hu
      have hnu : u ∉ cs.flatten := fun h => hnd.2.2 u hu u h rfl
      rw [indexComponentsAux, indexComponentsAux_notMem _ _ _ hnu, foldl_update_const,
        ite_eq_left hu]
      omega
    | succ i' =>
      simp only [List.length_cons, List.getElem_cons_succ] at hi hu
      rw [indexComponentsAux, indexComponentsAux_getElem (idx + 1) cs _ hnd.2.1 (by omega) hu]
      omega

theorem indexComponents_eq_of_mem {comps : List (List V)} (hnd : comps.flatten.Nodup)
    {i : ℕ} (hi : i < comps.length) {u : V} (hu : u ∈ comps[i]) :
    indexComponents comps u = i := by
  simpa [indexComponents] using indexComponentsAux_getElem 0 comps (fun _ => 0) hnd hi hu

namespace IsSCCCondensation

omit [DecidableEq V] in
theorem length_flatten_eq_card [Fintype V] {comps : List (List V)}
    (h : IsSCCCondensation adj comps) : comps.flatten.length = Fintype.card V := by
  classical
  rw [← List.toFinset_card_of_nodup h.nodup_flatten]
  congr 1
  ext v
  simp [h.mem_flatten v]

omit [DecidableEq V] in
theorem length_le_card [Fintype V] {comps : List (List V)}
    (h : IsSCCCondensation adj comps) : comps.length ≤ Fintype.card V := by
  have h1 : comps.length ≤ comps.flatten.length := by
    have hpos : ∀ c ∈ comps, 1 ≤ c.length := fun c hc =>
      List.length_pos_of_ne_nil (h.ne_nil c hc)
    clear h
    induction comps with
    | nil => simp
    | cons c cs ih =>
      have hc1 : 1 ≤ c.length := hpos c List.mem_cons_self
      have hcs := ih fun c' hc' => hpos c' (List.mem_cons_of_mem c hc')
      simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega
  rwa [h.length_flatten_eq_card] at h1

theorem indexComponents_lt {comps : List (List V)} (h : IsSCCCondensation adj comps) (v : V) :
    indexComponents comps v < comps.length := by
  obtain ⟨c, hc, hv⟩ := List.mem_flatten.1 (h.mem_flatten v)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  rwa [indexComponents_eq_of_mem h.nodup_flatten hi hv]

theorem mem_getElem_indexComponents {comps : List (List V)} (h : IsSCCCondensation adj comps)
    (v : V) : v ∈ comps[indexComponents comps v]'(h.indexComponents_lt v) := by
  obtain ⟨c, hc, hv⟩ := List.mem_flatten.1 (h.mem_flatten v)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have heq : indexComponents comps v = i := indexComponents_eq_of_mem h.nodup_flatten hi hv
  simpa [heq] using hv

theorem indexComponents_eq_iff {comps : List (List V)} (h : IsSCCCondensation adj comps)
    (u v : V) : indexComponents comps u = indexComponents comps v ↔ StronglyConnected adj u v := by
  rw [← h.same_comp_iff]
  constructor
  · intro heq
    refine ⟨comps[indexComponents comps u]'(h.indexComponents_lt u),
      List.getElem_mem (h.indexComponents_lt u), h.mem_getElem_indexComponents u, ?_⟩
    have hv := h.mem_getElem_indexComponents v
    simpa [← heq] using hv
  · rintro ⟨c, hc, hu, hv⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    rw [indexComponents_eq_of_mem h.nodup_flatten hi hu,
      indexComponents_eq_of_mem h.nodup_flatten hi hv]

theorem indexComponents_le_of_edge {comps : List (List V)} (h : IsSCCCondensation adj comps)
    {u v : V} (huv : Edge adj u v) :
    indexComponents comps u ≤ indexComponents comps v :=
  h.condensation_le (h.indexComponents_lt u) (h.indexComponents_lt v)
    (h.mem_getElem_indexComponents u) (h.mem_getElem_indexComponents v) huv

theorem indexComponents_le_of_reach {comps : List (List V)} (h : IsSCCCondensation adj comps)
    {u v : V} (huv : Relation.ReflTransGen (Edge adj) u v) :
    indexComponents comps u ≤ indexComponents comps v := by
  induction huv with
  | refl => exact le_rfl
  | tail _ hbc ih => exact ih.trans (h.indexComponents_le_of_edge hbc)

theorem indexComponents_lt_of_edge {comps : List (List V)} (h : IsSCCCondensation adj comps)
    {u v : V} (huv : Edge adj u v) (hn : ¬ StronglyConnected adj u v) :
    indexComponents comps u < indexComponents comps v :=
  lt_of_le_of_ne (h.indexComponents_le_of_edge huv) fun heq =>
    hn ((h.indexComponents_eq_iff u v).1 heq)

end IsSCCCondensation

end IndexComponents

end Cslib.Algorithms.Lean.DFS
