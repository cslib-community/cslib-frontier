/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.Trees

/-!
# Forest invariants and pure state transitions for a Fibonacci heap

This file lifts the single-tree model of `Trees.lean` to the full multi-root forest invariant
`FibRawInv` and proves the structural transitions required by all priority-queue operations:

* **Subtree cutting (`exists_parent_info`, `ValidSubtree.exists_cut`):** Severing a non-root node
  `cur` from its parent `p` splits `T` into a new valid root tree `T_cut` rooted at `cur` and a
  modified tree `T'` with `pending = some p` while preserving the multiset of tree nodes.
* **Full heap invariant (`FibRawInv`):** Relates `s : IndexedMinPQ.State n` to `st : RawState n`
  with exact domain, key, size, root-count, marked-count, `minRoot`, and `cons`-zeroing invariants,
  proving `IndexedMinPQ.findMin` agreement (`FibRawInv.findMin_eq_some`) and scalar bounds.
* **Transient cut invariant (`CutInv`):** Loop invariant for cascading cuts during `decreaseKey`,
  allowing a single `pending` ancestor whose child was just severed.
* **Lowering a key (`ValidSubtree.lower_key_no_cut`, `CutInv.to_fibRawInv`):** a lowered key keeps
  a subtree valid while it does not precede its parent, and `CutInv` without a pending node
  becomes `FibRawInv` once `minRoot` is updated.
* **Consolidation table invariant (`SlotInv`):** the trees stored in `cons[0..maxDeg]` while
  consolidating at most `sz` nodes, with pairwise-distinct degrees,
  `maxDeg ≤ 2 * Nat.log 2 sz + 1`, and every unoccupied entry `cons[d]` (`d ≤ n`) zero.

## Main definitions

* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.FibRawInv`: full multi-root forest
  representation invariant relating `IndexedMinPQ.State n` to `RawState n`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.CutInv`: transient forest invariant
  during
  cascading cuts in `decreaseKey`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.SlotInv`: consolidation-table invariant
  tracking distinct-degree root trees in `cons[0..maxDeg]`.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.ValidSubtree.exists_cut`: severing a
  non-root node splits its enclosing tree into a valid root tree and a `pending`-parent tree.
* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.FibRawInv.findMin_eq_some`: `minRoot`
  identifies the exact `IndexedMinPQ.findMin` element.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci Heaps and Their Uses in Improved Network Optimization
  Algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 19][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue

/-! ## List surgery lemmas for child removal and replacement -/

theorem map_root_nodup {n : ℕ} {cs : List (FHTree n)} (hnd : (forestNodes cs).Nodup) :
    (cs.map FHTree.root).Nodup := by
  induction cs with
  | nil => exact List.nodup_nil
  | cons c rest ih =>
    obtain ⟨_, hnd_rest, hdisj⟩ := List.nodup_append.mp hnd
    refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih hnd_rest⟩
    obtain ⟨c', hc', heq⟩ := List.mem_map.mp hmem
    exact hdisj c.root c.root_mem_nodes c'.root
      (mem_forestNodes_iff.mpr ⟨c', hc', c'.root_mem_nodes⟩) heq.symm

theorem forestNodes_nodup_idx_disjoint {n : ℕ} {cs : List (FHTree n)}
    (hnd : (forestNodes cs).Nodup) {i j : ℕ} (hi : i < cs.length) (hj : j < cs.length)
    (hij : i ≠ j) {x : Fin n} (hxi : x ∈ (cs[i]).nodes) (hxj : x ∈ (cs[j]).nodes) : False := by
  have hne_tree : cs[i] ≠ cs[j] := fun heq => hij <|
    ((map_root_nodup hnd).getElem_inj_iff
      (hi := by simpa using hi) (hj := by simpa using hj)).mp (by simp [heq])
  exact forestNodes_nodup_disjoint hnd (List.getElem_mem hi) (List.getElem_mem hj) hne_tree hxi hxj

private theorem mem_set_exists_idx {α : Type*} (L : List α) (i : ℕ) (v x : α)
    (h : x ∈ L.set i v) :
    x = v ∨ ∃ (j : ℕ) (hj : j < L.length), j ≠ i ∧ L[j] = x := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h
  rw [List.length_set] at hj
  rcases eq_or_ne j i with rfl | hji
  · exact Or.inl (by simp)
  · exact Or.inr ⟨j, hj, hji, (List.getElem_set_ne (Ne.symm hji) _).symm⟩

private theorem root_mem_forestNodes {n : ℕ} {cs : List (FHTree n)} {c : FHTree n} (hc : c ∈ cs) :
    c.root ∈ forestNodes cs :=
  mem_forestNodes_iff.mpr ⟨c, hc, c.root_mem_nodes⟩

private theorem child_mem_node {n : ℕ} {u : Fin n} {cs : List (FHTree n)} {c : FHTree n}
    (hc : c ∈ cs) {x : Fin n} (hx : x ∈ c.nodes) : x ∈ (FHTree.node u cs).nodes :=
  List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨c, hc, hx⟩)

private theorem child_desc_mem_forestNodes {n : ℕ} {cs : List (FHTree n)} {c : FHTree n}
    (hc : c ∈ cs) {x : Fin n} (hx : x ∈ forestNodes c.children) : x ∈ forestNodes cs :=
  mem_forestNodes_iff.mpr ⟨c, hc, c.nodes_eq ▸ List.mem_cons_of_mem c.root hx⟩

theorem forestNodes_eraseIdx_perm {n : ℕ} :
    ∀ (cs : List (FHTree n)) (i : ℕ) (hi : i < cs.length),
      ((cs[i]).nodes ++ forestNodes (cs.eraseIdx i)).Perm (forestNodes cs)
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Perm.refl _
  | c :: rest, i + 1, hi =>
    have hi' : i < rest.length := Nat.lt_of_succ_lt_succ hi
    (List.perm_append_comm_assoc (rest[i]'hi').nodes c.nodes _).trans
      ((forestNodes_eraseIdx_perm rest i hi').append_left c.nodes)

theorem forestNodes_set_perm {n : ℕ} :
    ∀ (cs : List (FHTree n)) (i : ℕ) (hi : i < cs.length) (T_cut c' : FHTree n),
      (T_cut.nodes ++ c'.nodes).Perm (cs[i]).nodes →
      (T_cut.nodes ++ forestNodes (cs.set i c')).Perm (forestNodes cs)
  | [], _, hi, _, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: rest, 0, _, _, _, hp => by
    simp only [List.getElem_cons_zero, List.set_cons_zero, forestNodes, ← List.append_assoc] at hp ⊢
    exact hp.append_right (forestNodes rest)
  | c :: rest, i + 1, hi, T_cut, c', hp =>
    (List.perm_append_comm_assoc T_cut.nodes c.nodes _).trans
      ((forestNodes_set_perm rest i (Nat.lt_of_succ_lt_succ hi) T_cut c' hp).append_left c.nodes)

theorem map_root_set_eq {n : ℕ} :
    ∀ (cs : List (FHTree n)) (i : ℕ) (hi : i < cs.length) (c' : FHTree n),
      c'.root = (cs[i]).root → (cs.set i c').map FHTree.root = cs.map FHTree.root
  | [], _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, 0, _, _, hr => by simp only [List.set_cons_zero, List.map_cons, hr]; rfl
  | c :: rest, i + 1, hi, c', hr => by
    simp only [List.set_cons_succ, List.map_cons,
      map_root_set_eq rest i (Nat.lt_of_succ_lt_succ hi) c' hr]

/-! ## Parent witnesses and subtree cutting -/

/-- Every strict descendant `x` of `T` has `st.par x = q.val + 1` for some `q ∈ T.nodes`. -/
theorem ValidSubtree.par_of_mem_children {n : ℕ} {st : RawState n} {pending : Option (Fin n)}
    {T : FHTree n} (hT : ValidSubtree st pending T) :
    ∀ x ∈ forestNodes T.children, ∃ q ∈ T.nodes, st.par x = q.val + 1 := by
  induction hT with
  | @mk u cs _ _ _ _ hpar _ _ _ ih =>
    intro x hx
    obtain ⟨c, hc, hxc⟩ := mem_forestNodes_iff.mp hx
    rw [c.nodes_eq] at hxc
    rcases List.mem_cons.mp hxc with rfl | hdesc
    · exact ⟨u, List.mem_cons_self, hpar c hc⟩
    · obtain ⟨q, hq, hpq⟩ := ih c hc x hdesc
      exact ⟨q, List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨c, hc, hq⟩), hpq⟩

/-- Rebuild one level of `ValidSubtree` with the same root `u` and children `cs`, framing the
child-list circular pointers and parent pointers across `st → st'`. -/
private theorem ValidSubtree.rebuild {n : ℕ} {st st' : RawState n}
    {pending' : Option (Fin n)} {u : Fin n} {cs : List (FHTree n)}
    (hin : st.inHeap u ≠ 0) (hdeg : st.deg u = cs.length)
    (hchild :
      (cs = [] ∧ st.child u = 0) ∨
      (∃ (h : Fin n) (tail : List (Fin n)),
        st.child u = h.val + 1 ∧ IsCircList st.left st.right (h :: tail) ∧
        (h :: tail).Perm (cs.map FHTree.root)))
    (hpar : ∀ T ∈ cs, st.par T.root = u.val + 1)
    (hin' : st'.inHeap u = st.inHeap u) (hmark' : st'.mark u ≤ 1)
    (hdeg' : st'.deg u = st.deg u) (hchild' : st'.child u = st.child u)
    (hptr : ∀ c ∈ cs, st'.par c.root = st.par c.root ∧
      st'.left c.root = st.left c.root ∧ st'.right c.root = st.right c.root)
    (hprio' : ∀ c ∈ cs, IndexedMinPQ.PrioLT (u, st'.key u) (c.root, st'.key c.root))
    (hrank' : ∀ (i : ℕ) (hi : i < cs.length),
      i ≤ st'.deg (cs[i]).root + st'.mark (cs[i]).root +
        (if some (cs[i]).root = pending' then 1 else 0))
    (hsub' : ∀ c ∈ cs, ValidSubtree st' pending' c) :
    ValidSubtree st' pending' (.node u cs) := by
  refine ⟨hin'.trans_ne hin, hmark', hdeg'.trans hdeg, ?_,
    fun c hc => (hptr c hc).1.trans (hpar c hc), hprio', hrank', hsub'⟩
  rcases hchild with ⟨rfl, hc0⟩ | ⟨h, tail, hcu, hcirc, hperm⟩
  · exact Or.inl ⟨rfl, hchild'.trans hc0⟩
  · refine Or.inr ⟨h, tail, hchild'.trans hcu, hcirc.frame fun x hx => ?_, hperm⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (hperm.subset hx)
    exact ⟨(hptr c hc).2.1, (hptr c hc).2.2⟩

/-- Updating only the root's `mark` to a value `≤ 1` while keeping all other subtree fields fixed
preserves `ValidSubtree`. -/
theorem ValidSubtree.frame_root_mark {n : ℕ} {st st' : RawState n}
    {pending pending' : Option (Fin n)}
    {T : FHTree n} (hT : ValidSubtree st pending T) (hnd : T.nodes.Nodup)
    (hrm : st'.mark T.root ≤ 1)
    (hroot : st'.inHeap T.root = st.inHeap T.root ∧ st'.deg T.root = st.deg T.root ∧
      st'.child T.root = st.child T.root ∧ st'.key T.root = st.key T.root)
    (hdesc_node : ∀ x ∈ forestNodes T.children,
      st'.inHeap x = st.inHeap x ∧ st'.mark x = st.mark x ∧ st'.deg x = st.deg x ∧
      st'.child x = st.child x ∧ st'.key x = st.key x)
    (hdesc_ptr : ∀ x ∈ forestNodes T.children,
      st'.par x = st.par x ∧ st'.left x = st.left x ∧ st'.right x = st.right x ∧
      ((some x = pending') ↔ (some x = pending))) :
    ValidSubtree st' pending' T := by
  cases hT with
  | @mk u cs hin _ hdeg hchild hpar hprio hrank hsub =>
    simp only [FHTree.root_node, FHTree.children_node] at hrm hroot hdesc_node hdesc_ptr
    refine ValidSubtree.rebuild hin hdeg hchild hpar hroot.1 hrm hroot.2.1 hroot.2.2.1
      (fun c hc => let hd := hdesc_ptr c.root (root_mem_forestNodes hc); ⟨hd.1, hd.2.1, hd.2.2.1⟩)
      (fun c hc => by
        rw [hroot.2.2.2, (hdesc_node c.root (root_mem_forestNodes hc)).2.2.2.2]
        exact hprio c hc)
      (fun i hi => by
        have hcr := root_mem_forestNodes (List.getElem_mem hi)
        have hcn := hdesc_node (cs[i]).root hcr
        rw [hcn.2.2.1, hcn.2.1, (if_congr (hdesc_ptr (cs[i]).root hcr).2.2.2 rfl rfl)]
        exact hrank i hi)
      (fun c hc => (hsub c hc).frame
        (fun x hx => hdesc_node x (mem_forestNodes_iff.mpr ⟨c, hc, hx⟩))
        (fun x hx => hdesc_ptr x (child_desc_mem_forestNodes hc hx)))

/-- Pre-cut structural properties of `cur` and its parent `p` inside any valid subtree containing
`cur` as a strict descendant. -/
theorem exists_parent_info {n : ℕ} {st : RawState n} {pending : Option (Fin n)} {T : FHTree n}
    (hT : ValidSubtree st pending T) {cur p : Fin n}
    (hcur : cur ∈ forestNodes T.children) (hpar_cur : st.par cur = p.val + 1) :
    p ∈ T.nodes ∧ st.inHeap p ≠ 0 ∧ st.mark p ≤ 1 ∧ st.inHeap cur ≠ 0 ∧ st.mark cur ≤ 1 ∧
    1 ≤ st.deg p ∧
    (2 ≤ st.deg p →
      ∃ (h : Fin n) (tail : List (Fin n)),
        st.child p = h.val + 1 ∧
        IsCircList st.left st.right (h :: tail) ∧
        cur ∈ h :: tail ∧ 2 ≤ (h :: tail).length ∧
        ∀ x ∈ h :: tail, st.par x = p.val + 1) := by
  induction hT with
  | @mk u cs hin hmark hdeg hchild hpar _ _ hsub ih =>
    obtain ⟨c, hc, hx_c⟩ := mem_forestNodes_iff.mp hcur
    have hc_sub := hsub c hc
    rw [c.nodes_eq] at hx_c
    rcases List.mem_cons.mp hx_c with rfl | hdesc
    · obtain rfl : u = p := Fin.ext (by have := hpar c hc; omega)
      cases hc_sub with | mk hin_cur hm_cur _ _ _ _ _ _ =>
      have hlen_pos : 1 ≤ cs.length := List.length_pos_of_mem hc
      refine ⟨List.mem_cons_self, hin, hmark, hin_cur, hm_cur, by omega, fun hdeg2 => ?_⟩
      rcases hchild with ⟨rfl, _⟩ | ⟨h, tail, hcu, hcirc, hperm⟩
      · simp only [List.length_nil] at hdeg; omega
      · refine ⟨h, tail, hcu, hcirc, hperm.symm.subset (List.mem_map_of_mem hc),
          by rw [hperm.length_eq, List.length_map]; omega, fun x hx => ?_⟩
        obtain ⟨c', hc', rfl⟩ := List.mem_map.mp (hperm.subset hx)
        exact hpar c' hc'
    · obtain ⟨hp_in, rest⟩ := ih c hc hdesc
      exact ⟨child_mem_node hc hp_in, rest⟩

/-- Bundled state-transition hypotheses for `ValidSubtree.exists_cut`. -/
private structure CutStep {n : ℕ} (st st' : RawState n) (pending : Option (Fin n))
    (T : FHTree n) (cur p : Fin n) : Prop where
  pend : pending = none ∨ pending = some cur
  inKey : ∀ x ∈ T.nodes, st'.inHeap x = st.inHeap x ∧ st'.key x = st.key x
  mark : st'.mark cur = 0 ∧ ∀ x ∈ T.nodes, x ≠ cur → st'.mark x = st.mark x
  deg : st'.deg p + 1 = st.deg p ∧ ∀ x ∈ T.nodes, x ≠ p → st'.deg x = st.deg x
  par : st'.par cur = 0 ∧ ∀ x ∈ T.nodes, x ≠ cur → st'.par x = st.par x
  childP : (st.deg p = 1 → st'.child p = 0) ∧
    (∀ (h : Fin n) (tail : List (Fin n)),
      2 ≤ st.deg p → st.child p = h.val + 1 →
      IsCircList st.left st.right (h :: tail) → cur ∈ h :: tail →
      ∃ (r : Fin n) (rest : List (Fin n)),
        st'.child p = r.val + 1 ∧ IsCircList st'.left st'.right (r :: rest) ∧
        (r :: rest).Perm ((h :: tail).erase cur))
  childOther : ∀ x ∈ T.nodes, x ≠ p → st'.child x = st.child x
  lrOther : ∀ x ∈ T.nodes, st.par x ≠ p.val + 1 → st.par x ≠ 0 →
    st'.left x = st.left x ∧ st'.right x = st.right x

private theorem CutStep.restrict {n : ℕ} {st st' : RawState n} {pending : Option (Fin n)}
    {u : Fin n} {cs : List (FHTree n)} {cur p : Fin n}
    (hs : CutStep st st' pending (.node u cs) cur p) {c : FHTree n} (hc : c ∈ cs) :
    CutStep st st' pending c cur p where
  pend := hs.pend
  inKey _ hx := hs.inKey _ (child_mem_node hc hx)
  mark := ⟨hs.mark.1, fun _ hx => hs.mark.2 _ (child_mem_node hc hx)⟩
  deg := ⟨hs.deg.1, fun _ hx => hs.deg.2 _ (child_mem_node hc hx)⟩
  par := ⟨hs.par.1, fun _ hx => hs.par.2 _ (child_mem_node hc hx)⟩
  childP := hs.childP
  childOther _ hx := hs.childOther _ (child_mem_node hc hx)
  lrOther _ hx := hs.lrOther _ (child_mem_node hc hx)

private theorem CutStep.clear_pending {n : ℕ} {st st' : RawState n} {pending : Option (Fin n)}
    {T : FHTree n} {cur p : Fin n} (hs : CutStep st st' pending T cur p) {c : FHTree n}
    (hsub : ValidSubtree st pending c) (hnot : cur ∉ forestNodes c.children) :
    ValidSubtree st none c := by
  rcases hs.pend with rfl | rfl
  · exact hsub
  · exact hsub.clear_pending hnot

private theorem CutStep.pending_zero_of_ne {n : ℕ} {st st' : RawState n}
    {pending : Option (Fin n)} {T : FHTree n} {cur p : Fin n}
    (hs : CutStep st st' pending T cur p) {x : Fin n} (hx : x ≠ cur) :
    (if some x = pending then 1 else 0) = 0 := by
  rcases hs.pend with rfl | rfl <;> simp [hx]

private theorem CutStep.desc_ptr {n : ℕ} {st st' : RawState n} {pending : Option (Fin n)}
    {T c : FHTree n} {cur p : Fin n} (hs : CutStep st st' pending T cur p)
    (hc_sub : ValidSubtree st none c) (hsub_in : ∀ x ∈ c.nodes, x ∈ T.nodes)
    (hcur_not : cur ∉ forestNodes c.children) (hp_not : p ∉ c.nodes)
    {x : Fin n} (hx : x ∈ forestNodes c.children) :
    st'.par x = st.par x ∧ st'.left x = st.left x ∧ st'.right x = st.right x ∧
      ((some x = (none : Option (Fin n))) ↔ (some x = (none : Option (Fin n)))) := by
  have hx_c : x ∈ c.nodes := c.nodes_eq ▸ List.mem_cons_of_mem c.root hx
  have hx_in := hsub_in x hx_c
  obtain ⟨q, hq_c, hpq⟩ := hc_sub.par_of_mem_children x hx
  have hq_ne_p : q ≠ p := fun e => hp_not (e ▸ hq_c)
  have hlr := hs.lrOther x hx_in (by have := Fin.val_ne_of_ne hq_ne_p; omega) (by omega)
  exact ⟨hs.par.2 x hx_in fun e => hcur_not (e ▸ hx), hlr.1, hlr.2, Iff.rfl⟩

private theorem CutStep.frame_sibling {n : ℕ} {st st' : RawState n} {pending : Option (Fin n)}
    {u : Fin n} {cs : List (FHTree n)} {cur p : Fin n}
    (hs : CutStep st st' pending (.node u cs) cur p) {c : FHTree n} (hc : c ∈ cs)
    (hsub : ValidSubtree st pending c) (hcur_not : cur ∉ c.nodes) (hp_not : p ∉ c.nodes)
    (pending' : Option (Fin n)) : ValidSubtree st' pending' c := by
  have hcur_desc : cur ∉ forestNodes c.children :=
    fun hm => hcur_not (c.nodes_eq ▸ List.mem_cons_of_mem c.root hm)
  have hc_none := hs.clear_pending hsub hcur_desc
  refine (hc_none.frame (pending' := none) (fun x hx => ?_)
    (fun _ hx => hs.desc_ptr hc_none (fun _ hx' => child_mem_node hc hx') hcur_desc hp_not
      hx)).weaken_pending pending'
  have hx_in : x ∈ (FHTree.node u cs).nodes := child_mem_node hc hx
  have hnc : x ≠ cur := fun e => hcur_not (e ▸ hx)
  have hnp : x ≠ p := fun e => hp_not (e ▸ hx)
  exact ⟨(hs.inKey x hx_in).1, hs.mark.2 x hx_in hnc, hs.deg.2 x hx_in hnp,
    hs.childOther x hx_in hnp, (hs.inKey x hx_in).2⟩

private theorem CutStep.frame_cut_root {n : ℕ} {st st' : RawState n} {pending : Option (Fin n)}
    {u : Fin n} {cs : List (FHTree n)} {cur : Fin n}
    (hs : CutStep st st' pending (.node u cs) cur u) {c : FHTree n} (hc : c ∈ cs)
    (hnd_c : c.nodes.Nodup) (hsub : ValidSubtree st pending c)
    (hroot : c.root = cur) (hu_not : u ∉ c.nodes) : ValidRoot st' none c := by
  have hcur_desc : cur ∉ forestNodes c.children := by
    rw [c.nodes_eq, hroot] at hnd_c; exact (List.nodup_cons.mp hnd_c).1
  have hc_none := hs.clear_pending hsub hcur_desc
  have hcur_in : cur ∈ (FHTree.node u cs).nodes := child_mem_node hc (hroot ▸ c.root_mem_nodes)
  have hcu : cur ≠ u := fun e => hu_not (e ▸ hroot ▸ c.root_mem_nodes)
  refine ⟨hc_none.frame_root_mark hnd_c (by rw [hroot, hs.mark.1]; omega) ?_ ?_ ?_,
    hroot ▸ hs.par.1, hroot ▸ hs.mark.1⟩
  · rw [hroot]
    exact ⟨(hs.inKey cur hcur_in).1, hs.deg.2 cur hcur_in hcu,
      hs.childOther cur hcur_in hcu, (hs.inKey cur hcur_in).2⟩
  · intro x hx
    have hx_c : x ∈ c.nodes := c.nodes_eq ▸ List.mem_cons_of_mem c.root hx
    have hx_in : x ∈ (FHTree.node u cs).nodes := child_mem_node hc hx_c
    exact ⟨(hs.inKey x hx_in).1, hs.mark.2 x hx_in (fun e => hcur_desc (e ▸ hx)),
      hs.deg.2 x hx_in (fun e => hu_not (e ▸ hx_c)),
      hs.childOther x hx_in (fun e => hu_not (e ▸ hx_c)), (hs.inKey x hx_in).2⟩
  · exact fun _ hx => hs.desc_ptr hc_none (fun _ hx' => child_mem_node hc hx') hcur_desc hu_not hx

private theorem CutStep.erase_child_valid {n : ℕ} {st st' : RawState n} {pending : Option (Fin n)}
    {u : Fin n} {cs : List (FHTree n)} {cur : Fin n} {i : ℕ} (hi : i < cs.length)
    (hnd : (FHTree.node u cs).nodes.Nodup) (hroot : (cs[i]).root = cur)
    (hs : CutStep st st' pending (.node u cs) cur u)
    (hT : ValidSubtree st pending (.node u cs)) :
    ValidSubtree st' (some u) (.node u (cs.eraseIdx i)) := by
  rcases hT with ⟨hin, hmark, hdeg, hchild, hpar, hprio, hrank, hsub⟩
  obtain ⟨hnd_u, hnd_cs⟩ := List.nodup_cons.mp hnd
  have hi_mem : cs[i] ∈ cs := List.getElem_mem hi
  have hu_in : u ∈ (FHTree.node u cs).nodes := List.mem_cons_self
  have hcur_mem : cur ∈ forestNodes cs := hroot ▸ root_mem_forestNodes hi_mem
  have hu_ne_cur : u ≠ cur := fun e => hnd_u (e ▸ hcur_mem)
  have hlen_er : (cs.eraseIdx i).length + 1 = cs.length := List.length_eraseIdx_add_one hi
  have hne_cur : ∀ (j : ℕ) (hj : j < cs.length), j ≠ i → (cs[j]).root ≠ cur := fun j hj hji e =>
    forestNodes_nodup_idx_disjoint hnd_cs hi hj hji.symm
      (hroot ▸ (cs[i]).root_mem_nodes) (e ▸ (cs[j]).root_mem_nodes)
  refine ⟨(hs.inKey u hu_in).1.trans_ne hin, hs.mark.2 u hu_in hu_ne_cur ▸ hmark,
    by have := hs.deg.1; omega, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hd1 : st.deg u = 1
    · exact Or.inl ⟨List.length_eq_zero_iff.mp (by omega), hs.childP.1 hd1⟩
    · rcases hchild with ⟨rfl, _⟩ | ⟨h, tail, hcu, hcirc, hperm⟩
      · exact absurd hi (by simp)
      · obtain ⟨r, rest, hch_u', hcirc', hperm_er⟩ :=
          hs.childP.2 h tail (by omega) hcu hcirc
            (hperm.symm.subset (hroot ▸ List.mem_map_of_mem hi_mem))
        have hmap_er : (cs.eraseIdx i).map FHTree.root = (cs.map FHTree.root).erase cur := by
          rw [← List.eraseIdx_map,
            ← (map_root_nodup hnd_cs).erase_getElem i (by simpa using hi)]
          simp [hroot]
        exact Or.inr ⟨r, rest, hch_u', hcirc', hperm_er.trans (hmap_er ▸ hperm.erase cur)⟩
  · intro _ hTc
    obtain ⟨j, hj, hji, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hTc
    have hjm := List.getElem_mem hj
    exact (hs.par.2 _ (child_mem_node hjm (cs[j]).root_mem_nodes) (hne_cur j hj hji)).trans
      (hpar cs[j] hjm)
  · intro _ hTc
    obtain ⟨j, hj, _, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hTc
    have hjm := List.getElem_mem hj
    rw [(hs.inKey u hu_in).2, (hs.inKey _ (child_mem_node hjm (cs[j]).root_mem_nodes)).2]
    exact hprio cs[j] hjm
  · intro j hj
    have hrank_k (k : ℕ) (hk : k < cs.length) (hki : k ≠ i) :
        k ≤ st'.deg (cs[k]).root + st'.mark (cs[k]).root := by
      have hkm := List.getElem_mem hk
      have hr_in : (cs[k]).root ∈ (FHTree.node u cs).nodes :=
        child_mem_node hkm (cs[k]).root_mem_nodes
      have hro := hrank k hk
      rw [hs.pending_zero_of_ne (hne_cur k hk hki)] at hro
      rw [hs.deg.2 _ hr_in (fun e => hnd_u (e ▸ root_mem_forestNodes hkm)),
        hs.mark.2 _ hr_in (hne_cur k hk hki)]
      omega
    rw [List.getElem_eraseIdx]
    by_cases hji : j < i
    · rw [dite_eq_left hji]
      have := hrank_k j (hji.trans hi) hji.ne
      omega
    · rw [dite_eq_right hji]
      have := hrank_k (j + 1) (by omega) (by omega)
      omega
  · intro _ hTc
    obtain ⟨j, hj, hji, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hTc
    have hjm := List.getElem_mem hj
    exact hs.frame_sibling hjm (hsub cs[j] hjm)
      (fun hm => forestNodes_nodup_idx_disjoint hnd_cs hi hj hji.symm
        (hroot ▸ (cs[i]).root_mem_nodes) hm)
      (fun hm => hnd_u (mem_forestNodes_iff.mpr ⟨cs[j], hjm, hm⟩)) _

private theorem CutStep.replace_child_valid {n : ℕ} {st st' : RawState n} {pending : Option (Fin n)}
    {u : Fin n} {cs : List (FHTree n)} {cur p : Fin n} {i : ℕ} (hi : i < cs.length)
    (hnd : (FHTree.node u cs).nodes.Nodup) (hcur_i : cur ∈ (cs[i]).nodes) (hp_i : p ∈ (cs[i]).nodes)
    (hroot_ne : (cs[i]).root ≠ cur) {c' : FHTree n} (hc'_r : c'.root = (cs[i]).root)
    (hvalid_c' : ValidSubtree st' (some p) c')
    (hs : CutStep st st' pending (.node u cs) cur p)
    (hT : ValidSubtree st pending (.node u cs)) :
    ValidSubtree st' (some p) (.node u (cs.set i c')) := by
  rcases hT with ⟨hin, hmark, hdeg, hchild, hpar, hprio, hrank, hsub⟩
  obtain ⟨hnd_u, hnd_cs⟩ := List.nodup_cons.mp hnd
  have hi_mem : cs[i] ∈ cs := List.getElem_mem hi
  have hu_in : u ∈ (FHTree.node u cs).nodes := List.mem_cons_self
  have hu_ne_cur : u ≠ cur := fun e => hnd_u (e ▸ mem_forestNodes_iff.mpr ⟨cs[i], hi_mem, hcur_i⟩)
  have hu_ne_p : u ≠ p := fun e => hnd_u (e ▸ mem_forestNodes_iff.mpr ⟨cs[i], hi_mem, hp_i⟩)
  have hne_cur : ∀ (j : ℕ) (hj : j < cs.length), j ≠ i → (cs[j]).root ≠ cur := fun j hj hji e =>
    forestNodes_nodup_idx_disjoint hnd_cs hi hj hji.symm hcur_i (e ▸ (cs[j]).root_mem_nodes)
  have hroot_mem {T_c : FHTree n} (hTc : T_c ∈ cs.set i c') :
      ∃ c ∈ cs, c.root = T_c.root ∧ c.root ≠ cur := by
    rcases mem_set_exists_idx cs i c' T_c hTc with rfl | ⟨j, hj, hji, rfl⟩
    · exact ⟨cs[i], hi_mem, hc'_r.symm, hroot_ne⟩
    · exact ⟨cs[j], List.getElem_mem hj, rfl, hne_cur j hj hji⟩
  refine ⟨(hs.inKey u hu_in).1.trans_ne hin, hs.mark.2 u hu_in hu_ne_cur ▸ hmark,
    by rw [hs.deg.2 u hu_in hu_ne_p, List.length_set]; exact hdeg, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hchild with ⟨rfl, _⟩ | ⟨h, tail, hcu, hcirc, hperm⟩
    · exact absurd hi (Nat.not_lt_zero _)
    · refine Or.inr ⟨h, tail, (hs.childOther u hu_in hu_ne_p).trans hcu,
        hcirc.frame fun x hx => ?_, map_root_set_eq cs i hi c' hc'_r ▸ hperm⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (hperm.subset hx)
      have := hpar c hc
      exact hs.lrOther c.root (child_mem_node hc c.root_mem_nodes)
        (by have := Fin.val_ne_of_ne hu_ne_p; omega) (by omega)
  · intro T_c hTc
    obtain ⟨c, hc, hr_eq, hnc⟩ := hroot_mem hTc
    rw [← hr_eq]
    exact (hs.par.2 _ (child_mem_node hc c.root_mem_nodes) hnc).trans (hpar c hc)
  · intro T_c hTc
    obtain ⟨c, hc, hr_eq, _⟩ := hroot_mem hTc
    rw [← hr_eq, (hs.inKey u hu_in).2, (hs.inKey _ (child_mem_node hc c.root_mem_nodes)).2]
    exact hprio c hc
  · intro j hj_set
    have hj : j < cs.length := by simpa only [List.length_set] using hj_set
    have hroot_j : ((cs.set i c')[j]'hj_set).root = (cs[j]).root := by
      by_cases hji : i = j <;> simp [hji, hc'_r]
    have hnc : (cs[j]).root ≠ cur := if hji : j = i then hji ▸ hroot_ne else hne_cur j hj hji
    have hr_in : (cs[j]).root ∈ (FHTree.node u cs).nodes :=
      child_mem_node (List.getElem_mem hj) (cs[j]).root_mem_nodes
    have hro := hrank j hj
    rw [hs.pending_zero_of_ne hnc] at hro
    rw [hroot_j, hs.mark.2 _ hr_in hnc]
    by_cases hwp : (cs[j]).root = p
    · have := hs.deg.1
      simp only [hwp, ↓reduceIte] at hro ⊢; omega
    · simp only [Option.some.injEq, hwp, ↓reduceIte, hs.deg.2 _ hr_in hwp]; omega
  · intro T_c hTc
    rcases mem_set_exists_idx cs i c' T_c hTc with rfl | ⟨j, hj, hji, rfl⟩
    · exact hvalid_c'
    · have hjm := List.getElem_mem hj
      exact hs.frame_sibling hjm (hsub cs[j] hjm)
        (fun hm => forestNodes_nodup_idx_disjoint hnd_cs hi hj hji.symm hcur_i hm)
        (fun hm => forestNodes_nodup_idx_disjoint hnd_cs hi hj hji.symm hp_i hm) _

/-- Cutting a strict descendant `cur` (with `st.par cur = p.val + 1`) from `T` splits `T` into a
new root tree `T_cut` (`T_cut.root = cur`) and a pruned tree `T'` (`T'.root = T.root`,
`p ∈ T'.nodes`) satisfying `ValidRoot st' none T_cut` and `ValidSubtree st' (some p) T'`. -/
theorem ValidSubtree.exists_cut {n : ℕ} {st st' : RawState n} {pending : Option (Fin n)}
    {T : FHTree n} (hT : ValidSubtree st pending T) (hnd : T.nodes.Nodup)
    {cur p : Fin n} (hcur : cur ∈ forestNodes T.children) (hpar_cur : st.par cur = p.val + 1)
    (hpend : pending = none ∨ pending = some cur)
    (hin_eq : ∀ x ∈ T.nodes, st'.inHeap x = st.inHeap x ∧ st'.key x = st.key x)
    (hmark' : st'.mark cur = 0 ∧ ∀ x ∈ T.nodes, x ≠ cur → st'.mark x = st.mark x)
    (hdeg' : st'.deg p + 1 = st.deg p ∧ ∀ x ∈ T.nodes, x ≠ p → st'.deg x = st.deg x)
    (hpar' : st'.par cur = 0 ∧ ∀ x ∈ T.nodes, x ≠ cur → st'.par x = st.par x)
    (hchild_p :
      (st.deg p = 1 → st'.child p = 0) ∧
      (∀ (h : Fin n) (tail : List (Fin n)),
        2 ≤ st.deg p → st.child p = h.val + 1 →
        IsCircList st.left st.right (h :: tail) → cur ∈ h :: tail →
        ∃ (r : Fin n) (rest : List (Fin n)),
          st'.child p = r.val + 1 ∧
          IsCircList st'.left st'.right (r :: rest) ∧
          (r :: rest).Perm ((h :: tail).erase cur)))
    (hchild_other : ∀ x ∈ T.nodes, x ≠ p → st'.child x = st.child x)
    (hlr_other : ∀ x ∈ T.nodes, st.par x ≠ p.val + 1 → st.par x ≠ 0 →
      st'.left x = st.left x ∧ st'.right x = st.right x) :
    ∃ (T_cut T' : FHTree n),
      T_cut.root = cur ∧ T'.root = T.root ∧ p ∈ T'.nodes ∧
      (T_cut.nodes ++ T'.nodes).Perm T.nodes ∧
      ValidRoot st' none T_cut ∧
      ValidSubtree st' (some p) T' := by
  let rec go {T : FHTree n} (hT : ValidSubtree st pending T) (hnd : T.nodes.Nodup)
      (hcur : cur ∈ forestNodes T.children) (hs : CutStep st st' pending T cur p) :
      ∃ (T_cut T' : FHTree n),
        T_cut.root = cur ∧ T'.root = T.root ∧ p ∈ T'.nodes ∧
        (T_cut.nodes ++ T'.nodes).Perm T.nodes ∧
        ValidRoot st' none T_cut ∧ ValidSubtree st' (some p) T' := by
    cases hT with | @mk u cs hin hmark hdeg hchild hpar hprio hrank hsub =>
    simp only [FHTree.children_node] at hcur
    have hT0 : ValidSubtree st pending (.node u cs) :=
      ⟨hin, hmark, hdeg, hchild, hpar, hprio, hrank, hsub⟩
    obtain ⟨hnd_u, hnd_cs⟩ := List.nodup_cons.mp hnd
    obtain ⟨cw, hcw_mem, hx_in_cw⟩ := mem_forestNodes_iff.mp hcur
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hcw_mem
    have hi_mem : cs[i] ∈ cs := List.getElem_mem hi
    have hnd_ci := forestNodes_nodup_tree hnd_cs hi_mem
    by_cases hroot_eq : (cs[i]).root = cur
    · obtain rfl : u = p := Fin.ext (by have := hpar cs[i] hi_mem; rw [hroot_eq] at this; omega)
      refine ⟨cs[i], .node u (cs.eraseIdx i), hroot_eq, rfl, List.mem_cons_self,
        List.perm_middle.trans (List.Perm.cons u (forestNodes_eraseIdx_perm cs i hi)),
        hs.frame_cut_root hi_mem hnd_ci (hsub cs[i] hi_mem) hroot_eq
          (fun hm => hnd_u (mem_forestNodes_iff.mpr ⟨cs[i], hi_mem, hm⟩)),
        hs.erase_child_valid hi hnd hroot_eq hT0⟩
    · have hcur_desc : cur ∈ forestNodes (cs[i]).children := by
        rw [(cs[i]).nodes_eq] at hx_in_cw
        exact (List.mem_cons.mp hx_in_cw).resolve_left (Ne.symm hroot_eq)
      obtain ⟨T_cut, c', hcut_r, hc'_r, hp_in_c', hperm_ci, hvalid_cut, hvalid_c'⟩ :=
        go (hsub cs[i] hi_mem) hnd_ci hcur_desc (hs.restrict hi_mem)
      have hc'_mem : c' ∈ cs.set i c' := List.mem_iff_getElem.mpr
        ⟨i, by simpa only [List.length_set] using hi, by simp⟩
      refine ⟨T_cut, .node u (cs.set i c'), hcut_r, rfl,
        child_mem_node hc'_mem hp_in_c',
        List.perm_middle.trans (List.Perm.cons u (forestNodes_set_perm cs i hi T_cut c' hperm_ci)),
        hvalid_cut,
        hs.replace_child_valid hi hnd hx_in_cw
          (hperm_ci.subset (List.mem_append_right _ hp_in_c'))
          hroot_eq hc'_r hvalid_c' hT0⟩
  exact go hT hnd hcur
    ⟨hpend, hin_eq, hmark', hdeg', hpar', hchild_p, hchild_other, hlr_other⟩

/-- Marking an unmarked `pending = some z` node (`st.mark z = 0`, `st'.mark z = 1`) absorbs the
transient rank slack and restores `ValidSubtree st' none T`. -/
theorem ValidSubtree.mark_pending {n : ℕ} {st st' : RawState n} {z : Fin n} {T : FHTree n}
    (hT : ValidSubtree st (some z) T) (hm0 : st.mark z = 0) (hm1 : st'.mark z = 1)
    (hm_other : ∀ x ∈ T.nodes, x ≠ z → st'.mark x = st.mark x)
    (hunch : ∀ x ∈ T.nodes,
      st'.inHeap x = st.inHeap x ∧ st'.deg x = st.deg x ∧ st'.child x = st.child x ∧
      st'.key x = st.key x)
    (hptr : ∀ x ∈ forestNodes T.children,
      st'.par x = st.par x ∧ st'.left x = st.left x ∧ st'.right x = st.right x) :
    ValidSubtree st' none T := by
  induction hT with
  | @mk u cs hin hmark hdeg hchild hpar hprio hrank _ ih =>
    have hu := hunch u List.mem_cons_self
    refine ValidSubtree.rebuild hin hdeg hchild hpar hu.1
      (by
        by_cases huz : u = z
        · subst huz; omega
        · rw [hm_other u List.mem_cons_self huz]; exact hmark)
      hu.2.1 hu.2.2.1
      (fun c hc => hptr c.root (root_mem_forestNodes hc))
      (fun c hc => by
        rw [hu.2.2.2, (hunch c.root (child_mem_node hc c.root_mem_nodes)).2.2.2]
        exact hprio c hc)
      (fun i hi => by
        have hci : (cs[i]).root ∈ (FHTree.node u cs).nodes :=
          child_mem_node (List.getElem_mem hi) (cs[i]).root_mem_nodes
        have hr := hrank i hi
        rw [(hunch (cs[i]).root hci).2.1]
        by_cases hwz : (cs[i]).root = z
        · simp only [hwz, reduceCtorEq, ↓reduceIte, Nat.add_zero] at hr ⊢; omega
        · simpa only [Option.some.injEq, hwz, reduceCtorEq, ↓reduceIte, Nat.add_zero,
            hm_other _ hci hwz] using hr)
      (fun c hc => ih c hc
        (fun x hx => hm_other x (child_mem_node hc hx))
        (fun x hx => hunch x (child_mem_node hc hx))
        (fun x hx => hptr x (child_desc_mem_forestNodes hc hx)))

/-! ## Full heap representation invariant and core consequences -/

/-- Full structural, key, counter, and root-list invariant relating `s : IndexedMinPQ.State n` to
`st : RawState n`. -/
def FibRawInv (n K_max : ℕ) (s : IndexedMinPQ.State n) (st : RawState n) : Prop :=
  ∃ ts : List (FHTree n),
    (∀ T ∈ ts, ValidRoot st none T) ∧
    (forestNodes ts).Nodup ∧
    (∀ v : Fin n, v ∈ forestNodes ts ↔ (s v).isSome) ∧
    (∀ v : Fin n, (st.inHeap v ≠ 0 ↔ (s v).isSome) ∧ st.inHeap v ≤ 1) ∧
    (∀ v : Fin n, ∀ k : ℕ, s v = some k → st.key v = k ∧ k ≤ K_max) ∧
    st.sz = (IndexedMinPQ.dom s).card ∧
    st.numRoots = ts.length ∧
    st.numMarked = markedCount st ∧
    (∀ d ≤ n, st.cons d = 0) ∧
    ((ts = [] ∧ st.minRoot = 0) ∨
      ∃ (m : Fin n) (rtail : List (Fin n)),
        st.minRoot = m.val + 1 ∧
        IsCircList st.left st.right (m :: rtail) ∧
        (m :: rtail).Perm (ts.map FHTree.root) ∧
        ∀ T ∈ ts, IndexedMinPQ.PrioLE (m, st.key m) (T.root, st.key T.root))

/-- Transient forest invariant during `decreaseKey v k` while cascading cuts propagate from
`pending`. -/
def CutInv (n K_max : ℕ) (s : IndexedMinPQ.State n) (st : RawState n) (v m : Fin n)
    (pending : Option (Fin n)) : Prop :=
  ∃ ts : List (FHTree n),
    (∀ T ∈ ts, ValidRoot st pending T) ∧
    (forestNodes ts).Nodup ∧
    (∀ x : Fin n, x ∈ forestNodes ts ↔ (s x).isSome) ∧
    (∀ x : Fin n, (st.inHeap x ≠ 0 ↔ (s x).isSome) ∧ st.inHeap x ≤ 1) ∧
    (∀ x : Fin n, ∀ kx : ℕ, s x = some kx → st.key x = kx ∧ kx ≤ K_max) ∧
    st.sz = (IndexedMinPQ.dom s).card ∧
    st.numRoots = ts.length ∧
    st.numMarked = markedCount st ∧
    (∀ d ≤ n, st.cons d = 0) ∧
    (∃ rtail : List (Fin n),
      st.minRoot = m.val + 1 ∧
      IsCircList st.left st.right (m :: rtail) ∧
      (m :: rtail).Perm (ts.map FHTree.root)) ∧
    (∃ T_v ∈ ts, T_v.root = v) ∧
    (∀ T ∈ ts, T.root ≠ v → IndexedMinPQ.PrioLE (m, st.key m) (T.root, st.key T.root))

/-- `FibRawInv` holds on the empty priority queue whenever `inHeap` and `cons[0..n]` are zeroed and
the four scalar counters are `0`. -/
theorem FibRawInv.empty {n K_max : ℕ} {st : RawState n}
    (hin : ∀ v : Fin n, st.inHeap v = 0)
    (hcons : ∀ d ≤ n, st.cons d = 0)
    (hmin : st.minRoot = 0) (hnr : st.numRoots = 0) (hnm : st.numMarked = 0) (hsz : st.sz = 0) :
    FibRawInv n K_max (IndexedMinPQ.empty n) st := by
  refine ⟨[], fun _ h => absurd h List.not_mem_nil, List.nodup_nil,
    fun v => by simp [forestNodes, IndexedMinPQ.empty],
    fun v => ⟨by simp [hin v, IndexedMinPQ.empty], by rw [hin v]; omega⟩,
    fun _ _ h => by simp [IndexedMinPQ.empty] at h,
    by simp [hsz, IndexedMinPQ.dom_empty], hnr, ?_, hcons, Or.inl ⟨rfl, hmin⟩⟩
  have hm0 : markedCount st = 0 := by simp [markedCount, markedSet, hin]
  omega

/-- All scalar counters of a valid Fibonacci heap are bounded by `n`. -/
theorem FibRawInv.bounds {n K_max : ℕ} {s : IndexedMinPQ.State n} {st : RawState n}
    (h : FibRawInv n K_max s st) :
    st.sz ≤ n ∧ st.numRoots ≤ n ∧ st.numMarked ≤ n ∧ st.minRoot ≤ n := by
  obtain ⟨ts, _, hnd, _, _, _, hsz, hnr, hnm, _, hrl⟩ := h
  have hts_le : ts.length ≤ n :=
    (forestNodes_length_ge ts).trans (by simpa using hnd.length_le_card)
  have hdom_le : (IndexedMinPQ.dom s).card ≤ n := by simpa using (IndexedMinPQ.dom s).card_le_univ
  have hm_le : markedCount st ≤ n := markedCount_le_n st
  rcases hrl with ⟨_, hm0⟩ | ⟨m, _, hm, _, _, _⟩ <;> [skip; have := m.isLt] <;> omega

/-- Concrete state uniquely determines the represented `IndexedMinPQ.State n`. -/
theorem FibRawInv.unique {n K_max : ℕ} {s₁ s₂ : IndexedMinPQ.State n} {st : RawState n}
    (h₁ : FibRawInv n K_max s₁ st) (h₂ : FibRawInv n K_max s₂ st) : s₁ = s₂ := by
  obtain ⟨_, _, _, _, hin₁, hkeys₁, _, _, _, _, _⟩ := h₁
  obtain ⟨_, _, _, _, hin₂, hkeys₂, _, _, _, _, _⟩ := h₂
  funext v
  have hiff : (s₁ v).isSome ↔ (s₂ v).isSome := (hin₁ v).1.symm.trans (hin₂ v).1
  cases hs₁ : s₁ v <;> cases hs₂ : s₂ v
  · rfl
  · simp [hs₁, hs₂] at hiff
  · simp [hs₁, hs₂] at hiff
  · exact congrArg some ((hkeys₁ v _ hs₁).1.symm.trans (hkeys₂ v _ hs₂).1)

/-- When `st.minRoot = 0`, `dom s = ∅` and `IndexedMinPQ.findMin s = none`. -/
theorem FibRawInv.findMin_eq_none {n K_max : ℕ} {s : IndexedMinPQ.State n} {st : RawState n}
    (h : FibRawInv n K_max s st) (h0 : st.minRoot = 0) :
    IndexedMinPQ.dom s = ∅ ∧ IndexedMinPQ.findMin s = none := by
  obtain ⟨ts, _, _, hdom, _, _, _, _, _, _, ⟨rfl, _⟩ | ⟨_, _, hm, _, _, _⟩⟩ := h
  · have hemp : IndexedMinPQ.dom s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun v hv => by
      obtain ⟨k, hsk⟩ := IndexedMinPQ.mem_dom_iff.mp hv
      exact List.not_mem_nil ((hdom v).mpr (by simp [hsk]))
    exact ⟨hemp, IndexedMinPQ.findMin_eq_none_iff.mpr hemp⟩
  · omega

/-- When `st.minRoot = z.val + 1`, `IndexedMinPQ.findMin s = some (z, st.key z)`. -/
theorem FibRawInv.findMin_eq_some {n K_max : ℕ} {s : IndexedMinPQ.State n} {st : RawState n}
    (h : FibRawInv n K_max s st) {z : Fin n} (hz : st.minRoot = z.val + 1) :
    IndexedMinPQ.findMin s = some (z, st.key z) ∧ s z = some (st.key z) ∧ st.key z ≤ K_max := by
  obtain ⟨ts, hroots, _, hdom, _, hkeys, _, _, _, _, hrl⟩ := h
  rcases hrl with ⟨_, hm0⟩ | ⟨m, _, hm, _, hperm, hmin_le⟩
  · omega
  · obtain rfl : m = z := Fin.ext (by omega)
    obtain ⟨T_m, hTm, hm_root⟩ := List.mem_map.mp (hperm.subset List.mem_cons_self)
    obtain ⟨km, hsm⟩ := Option.isSome_iff_exists.mp
      ((hdom m).mp (hm_root ▸ root_mem_forestNodes hTm))
    obtain ⟨rfl, hkm_le⟩ := hkeys m km hsm
    refine ⟨IndexedMinPQ.findMin_eq_some_iff.mpr ⟨hsm, fun v kv hsv => ?_⟩, hsm, hkm_le⟩
    obtain ⟨T_v, hTv, hv_in_Tv⟩ :=
      mem_forestNodes_iff.mp ((hdom v).mpr (by simp [hsv]))
    obtain ⟨rfl, _⟩ := hkeys v kv hsv
    exact (hmin_le T_v hTv).trans ((hroots T_v hTv).1.prioLE_of_mem hv_in_Tv)

/-! ## Forest facts used by several operations -/

/-- In any `Nodup` forest `ts`, no strict descendant `x ∈ forestNodes T.children` (`T ∈ ts`) can
equal the root of any tree `R ∈ ts`. -/
theorem descendant_ne_root_of_nodup {n : ℕ} {ts : List (FHTree n)} (hnd : (forestNodes ts).Nodup)
    {T R : FHTree n} (hT : T ∈ ts) (hR : R ∈ ts) {x : Fin n} (hx : x ∈ forestNodes T.children) :
    x ≠ R.root := by
  rintro rfl
  rcases eq_or_ne T R with rfl | hTR
  · exact (List.nodup_cons.mp (T.nodes_eq ▸ forestNodes_nodup_tree hnd hT)).1 hx
  · exact forestNodes_nodup_disjoint hnd hT hR hTR
      (T.nodes_eq ▸ List.mem_cons_of_mem T.root hx) R.root_mem_nodes

/-- A tree is rebuilt from its root and children. -/
theorem FHTree.eta {n : ℕ} (T : FHTree n) : FHTree.node T.root T.children = T := by
  cases T
  rfl

/-! ## Framing and pure-`ℕ` degree bounds during consolidation -/

/-- Framing `ValidRoot st none T` across a state transition preserving node fields on `T.nodes` and
pointer fields on strict descendants `forestNodes T.children`. -/
theorem ValidRoot.frame_tree {n : ℕ} {st st' : RawState n} {T : FHTree n}
    (hT : ValidRoot st none T)
    (hnode : ∀ u ∈ T.nodes,
      st'.inHeap u = st.inHeap u ∧ st'.mark u = st.mark u ∧ st'.deg u = st.deg u ∧
      st'.child u = st.child u ∧ st'.key u = st.key u ∧ st'.par u = st.par u)
    (hlr : ∀ u ∈ forestNodes T.children,
      st'.left u = st.left u ∧ st'.right u = st.right u) :
    ValidRoot st' none T :=
  let ⟨_, hm, _, _, _, hp⟩ := hnode T.root T.root_mem_nodes
  ⟨hT.1.frame
    (fun u hu => let ⟨hi, hm, hd, hc, hk, _⟩ := hnode u hu; ⟨hi, hm, hd, hc, hk⟩)
    (fun u hu =>
      let ⟨_, _, _, _, _, hp⟩ := hnode u (T.nodes_eq ▸ List.mem_cons_of_mem T.root hu)
      let ⟨hl, hr⟩ := hlr u hu
      ⟨hp, hl, hr, Iff.rfl⟩),
    hp.trans hT.2.1, hm.trans hT.2.2⟩

/-- Framing `ValidRoot st none T` when all eight vertex arrays agree on `T.nodes`. -/
theorem ValidRoot.frame_nodes {n : ℕ} {st st' : RawState n} {T : FHTree n}
    (hT : ValidRoot st none T)
    (h : ∀ u ∈ T.nodes,
      st'.inHeap u = st.inHeap u ∧ st'.mark u = st.mark u ∧ st'.deg u = st.deg u ∧
      st'.child u = st.child u ∧ st'.key u = st.key u ∧ st'.par u = st.par u ∧
      st'.left u = st.left u ∧ st'.right u = st.right u) :
    ValidRoot st' none T :=
  hT.frame_tree
    (fun u hu => let ⟨hi, hm, hd, hc, hk, hp, _⟩ := h u hu; ⟨hi, hm, hd, hc, hk, hp⟩)
    (fun u hu =>
      let ⟨_, _, _, _, _, _, hl, hr⟩ := h u (T.nodes_eq ▸ List.mem_cons_of_mem T.root hu)
      ⟨hl, hr⟩)

/-- Every valid subtree `T` with `T.size ≤ sz` disjoint from at least one other handle `z : Fin n`
satisfies both `T.deg ≤ 2 * Nat.log 2 sz + 1` and `T.deg + 2 ≤ n`. -/
theorem deg_bounds_of_extra {n sz : ℕ} {st : RawState n} {T : FHTree n} {z : Fin n}
    (hsz : T.size ≤ sz) (hT : ValidSubtree st none T) (hnd : (z :: T.nodes).Nodup) :
    T.deg ≤ 2 * Nat.log 2 sz + 1 ∧ T.deg + 2 ≤ n := by
  have hlen : (z :: T.nodes).length ≤ n := by simpa using hnd.length_le_card
  have hds : T.deg + 1 ≤ T.size := (deg_add_one_le_fib T.deg).trans hT.fib_le_size
  exact ⟨(hT.deg_bounds hsz).1, by rw [List.length_cons] at hlen; unfold FHTree.size at hds; omega⟩

/-! ## Consolidation table invariant `SlotInv` -/

/-- Invariant for the degree consolidation table `st.cons` holding `slotTrees` within
`0 .. maxDeg`, where `sz` bounds the total number of nodes being consolidated. -/
def SlotInv (n sz : ℕ) (st : RawState n) (slotTrees : List (FHTree n)) (maxDeg : ℕ) : Prop :=
  (slotTrees.map FHTree.deg).Nodup ∧
  (∀ T ∈ slotTrees, ValidRoot st none T ∧ T.deg ≤ maxDeg) ∧
  (∀ T ∈ slotTrees, st.cons T.deg = T.root.val + 1) ∧
  (∀ d ≤ n, (∀ T ∈ slotTrees, T.deg ≠ d) → st.cons d = 0) ∧
  maxDeg ≤ 2 * Nat.log 2 sz + 1 ∧
  (maxDeg = 0 ∨ maxDeg + 2 ≤ n)

/-- Initial empty consolidation table when `∀ d ≤ n, st.cons d = 0`. -/
theorem SlotInv.empty {n sz : ℕ} {st : RawState n} (hcons : ∀ d ≤ n, st.cons d = 0) :
    SlotInv n sz st [] 0 :=
  ⟨List.nodup_nil, nofun, nofun, fun d hd _ => hcons d hd, Nat.zero_le _, Or.inl rfl⟩

/-- Framing `SlotInv` across a transition preserving `cons` and `ValidRoot` on `slotTrees`. -/
theorem SlotInv.frame {n sz maxDeg : ℕ} {st st' : RawState n} {slotTrees : List (FHTree n)}
    (hs : SlotInv n sz st slotTrees maxDeg)
    (hcons : st'.cons = st.cons)
    (hvalid : ∀ T ∈ slotTrees, ValidRoot st' none T) :
    SlotInv n sz st' slotTrees maxDeg := by
  obtain ⟨hnd, htr, hhit, hemp, hmd1, hmd2⟩ := hs
  exact ⟨hnd,
    fun T hT => ⟨hvalid T hT, (htr T hT).2⟩,
    fun T hT => hcons ▸ hhit T hT,
    fun d hd hnone => hcons ▸ hemp d hd hnone,
    hmd1, hmd2⟩

/-- Lookup in `st.cons d` (`d ≤ n`): either `st.cons d = 0` and no tree in `slotTrees` has degree
`d`, or a unique index `i < slotTrees.length` has `(slotTrees[i]).deg = d` and
`st.cons d = (slotTrees[i]).root.val + 1`. -/
theorem SlotInv.lookup {n sz maxDeg : ℕ} {st : RawState n} {slotTrees : List (FHTree n)}
    (hs : SlotInv n sz st slotTrees maxDeg) {d : ℕ} (hd : d ≤ n) :
    (st.cons d = 0 ∧ ∀ T ∈ slotTrees, T.deg ≠ d) ∨
    ∃ (i : ℕ) (hi : i < slotTrees.length),
      (slotTrees[i]).deg = d ∧
      st.cons d = (slotTrees[i]).root.val + 1 ∧
      (slotTrees.eraseIdx i).length + 1 = slotTrees.length ∧
      (∀ R ∈ slotTrees.eraseIdx i, R.deg ≠ d) := by
  obtain ⟨hnd, _, hhit, hemp, _, _⟩ := hs
  by_cases hex : ∃ T ∈ slotTrees, T.deg = d
  · obtain ⟨T, hT_mem, hT_deg⟩ := hex
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT_mem
    refine Or.inr ⟨i, hi, hT_deg, hT_deg ▸ hhit slotTrees[i] (List.getElem_mem hi),
      List.length_eraseIdx_add_one hi, fun R hR hR_deg => ?_⟩
    obtain ⟨j, hj, hji, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hR
    exact hji ((hnd.getElem_inj_iff (hi := by simp [hj]) (hj := by simp [hi])).mp
      (by simp [hR_deg, hT_deg]))
  · have hnone : ∀ T ∈ slotTrees, T.deg ≠ d := fun T hT e => hex ⟨T, hT, e⟩
    exact Or.inl ⟨hemp d hd hnone, hnone⟩

/-- Clearing slot `d = (slotTrees[i]).deg` (`d ≤ n`) removes `slotTrees[i]` from `SlotInv`. -/
theorem SlotInv.step_collision {n sz maxDeg : ℕ} {st st' : RawState n} {slotTrees : List (FHTree n)}
    (hs : SlotInv n sz st slotTrees maxDeg) {i d : ℕ} (hi : i < slotTrees.length)
    (hdeg_i : (slotTrees[i]).deg = d) (_hd : d ≤ n)
    (hno_other : ∀ R ∈ slotTrees.eraseIdx i, R.deg ≠ d)
    (hcons' : st'.cons = Function.update st.cons d 0)
    (hvalid' : ∀ R ∈ slotTrees.eraseIdx i, ValidRoot st' none R) :
    SlotInv n sz st' (slotTrees.eraseIdx i) maxDeg := by
  obtain ⟨hnd, htr, hhit, hemp, hmd1, hmd2⟩ := hs
  refine ⟨List.eraseIdx_map _ _ _ ▸ hnd.eraseIdx i, fun R hR => ?_, fun R hR => ?_,
    fun d' hd' hnone' => ?_, hmd1, hmd2⟩
  · exact ⟨hvalid' R hR, (htr R (List.mem_of_mem_eraseIdx hR)).2⟩
  · rw [hcons', Function.update_of_ne (hno_other R hR)]
    exact hhit R (List.mem_of_mem_eraseIdx hR)
  · rw [hcons']
    rcases eq_or_ne d' d with rfl | hdd
    · exact Function.update_self _ _ _
    · rw [Function.update_of_ne hdd]
      refine hemp d' hd' fun T hT hTd' => ?_
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hT
      rcases eq_or_ne k i with rfl | hki
      · exact hdd (hTd'.symm.trans hdeg_i)
      · exact hnone' slotTrees[k] (List.mem_eraseIdx_iff_getElem.mpr ⟨k, hk, hki, rfl⟩) hTd'

/-- Storing a consolidated tree `T_cur` of unoccupied degree `d` into `st.cons d` and updating
`maxDeg` to `max maxDeg d` inserts `T_cur` into `SlotInv`. -/
theorem SlotInv.insert_empty {n sz maxDeg : ℕ} {st : RawState n} {slotTrees : List (FHTree n)}
    (hs : SlotInv n sz st slotTrees maxDeg) {T_cur : FHTree n} {d : ℕ}
    (_hd_n : d + 2 ≤ n) (hd_log : d ≤ 2 * Nat.log 2 sz + 1)
    (hT_deg : T_cur.deg = d)
    (hnone : ∀ R ∈ slotTrees, R.deg ≠ d)
    (hT_valid : ValidRoot st none T_cur) :
    SlotInv n sz { st with cons := Function.update st.cons d (T_cur.root.val + 1) }
      (T_cur :: slotTrees) (max maxDeg d) := by
  obtain ⟨hnd, htr, hhit, hemp, hmd1, _⟩ := hs
  let st' : RawState n := { st with cons := Function.update st.cons d (T_cur.root.val + 1) }
  have hv_all (R : FHTree n) (hR : ValidRoot st none R) : ValidRoot st' none R :=
    hR.frame_nodes fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨List.nodup_cons.mpr ⟨fun hm => ?_, hnd⟩, fun R hR => ?_, fun R hR => ?_,
    fun d' hd' hnone' => ?_, by omega, Or.inr (by omega)⟩
  · obtain ⟨R, hR, hR_eq⟩ := List.mem_map.mp hm
    exact hnone R hR (hR_eq.trans hT_deg)
  · rcases List.mem_cons.mp hR with rfl | hR_tl
    · exact ⟨hv_all R hT_valid, by omega⟩
    · exact ⟨hv_all R (htr R hR_tl).1, (htr R hR_tl).2.trans (Nat.le_max_left maxDeg d)⟩
  · rcases List.mem_cons.mp hR with rfl | hR_tl
    · exact hT_deg ▸ Function.update_self d _ st.cons
    · exact (Function.update_of_ne (hnone R hR_tl) _ st.cons).trans (hhit R hR_tl)
  · have hne_d : d' ≠ d := fun e => hnone' T_cur List.mem_cons_self (hT_deg.trans e.symm)
    rw [show st'.cons = Function.update st.cons d _ from rfl, Function.update_of_ne hne_d]
    exact hemp d' hd' fun R hR => hnone' R (List.mem_cons_of_mem T_cur hR)

/-- Once every degree `< maxDeg + 1` has been cleared from `SlotInv`, `slotTrees = []` and all
entries `st.cons d` (`d ≤ n`) are `0`. -/
theorem SlotInv.done_of_cleared {n sz maxDeg : ℕ} {st : RawState n} {slotTrees : List (FHTree n)}
    (hs : SlotInv n sz st slotTrees maxDeg)
    (hcleared : ∀ d < maxDeg + 1, ∀ T ∈ slotTrees, T.deg ≠ d) :
    slotTrees = [] ∧ ∀ d ≤ n, st.cons d = 0 := by
  obtain ⟨_, htr, _, hemp, _, _⟩ := hs
  rcases slotTrees with _ | ⟨T, _⟩
  · exact ⟨rfl, fun d hd => hemp d hd fun _ h => absurd h List.not_mem_nil⟩
  · exact absurd rfl
      (hcleared T.deg (Nat.lt_succ_of_le (htr T List.mem_cons_self).2) T List.mem_cons_self)

/-! ## Lemmas for `decreaseKey` -/

/-- Inside a valid root tree `T`, `st.par u = 0` holds iff `u = T.root`. -/
theorem ValidRoot.par_eq_zero_iff_root {n : ℕ} {st : RawState n} {pending : Option (Fin n)}
    {T : FHTree n} (hT : ValidRoot st pending T) {u : Fin n} (hu : u ∈ T.nodes) :
    st.par u = 0 ↔ u = T.root := by
  refine ⟨fun hp0 => ?_, fun h => h ▸ hT.2.1⟩
  rw [T.nodes_eq] at hu
  rcases List.mem_cons.mp hu with rfl | hdesc
  · rfl
  · obtain ⟨q, _, hpq⟩ := hT.1.par_of_mem_children u hdesc
    omega

/-- In a valid subtree with `Nodup` nodes, no strict descendant `v` is its own parent. -/
theorem ValidSubtree.par_ne_self {n : ℕ} {st : RawState n} {pending : Option (Fin n)}
    {U : FHTree n} (hU : ValidSubtree st pending U) (hnd : U.nodes.Nodup) {v : Fin n}
    (hv : v ∈ forestNodes U.children) : st.par v ≠ v.val + 1 :=
  match U, hU with
  | .node u cs, .mk _ _ _ _ hpar _ _ hsub => by
    intro hpv
    have hu_not : u ∉ forestNodes cs := (List.nodup_cons.mp hnd).1
    obtain ⟨c, hc, hv_c⟩ := mem_forestNodes_iff.mp hv
    rw [c.nodes_eq] at hv_c
    rcases List.mem_cons.mp hv_c with rfl | hv_desc_c
    · have hpc := hpar c hc
      obtain rfl : u = c.root := Fin.ext (by omega)
      exact hu_not hv
    · exact (hsub c hc).par_ne_self (forestNodes_nodup_tree (List.nodup_cons.mp hnd).2 hc)
        hv_desc_c hpv

/-- Lowering `key[v]` to `k ≤ st.key v` preserves `ValidSubtree st' none T` whenever `v = T.root` or
`v` has parent `p` (`st.par v = p.val + 1`) with `¬IndexedMinPQ.PrioLT (v, k) (p, st.key p)`. -/
theorem ValidSubtree.lower_key_no_cut {n : ℕ} {st st' : RawState n} {T : FHTree n}
    (hT : ValidSubtree st none T) (hnd : T.nodes.Nodup) {v : Fin n} {k : ℕ}
    (hv : v ∈ T.nodes) (hle : k ≤ st.key v)
    (hk_v : st'.key v = k) (hk_other : ∀ x ∈ T.nodes, x ≠ v → st'.key x = st.key x)
    (hunch : ∀ x ∈ T.nodes,
      st'.inHeap x = st.inHeap x ∧ st'.mark x = st.mark x ∧ st'.deg x = st.deg x ∧
      st'.child x = st.child x)
    (hptr : ∀ x ∈ forestNodes T.children,
      st'.par x = st.par x ∧ st'.left x = st.left x ∧ st'.right x = st.right x)
    (hord : v = T.root ∨ ∃ p : Fin n, st.par v = p.val + 1 ∧
      ¬IndexedMinPQ.PrioLT (v, k) (p, st.key p)) :
    ValidSubtree st' none T := by
  induction hT with
  | @mk u cs hin hmark hdeg hchild hpar hprio hrank hsub ih =>
    have hu := hunch u List.mem_cons_self
    obtain ⟨hnd_u, hnd_cs⟩ := List.nodup_cons.mp hnd
    refine ValidSubtree.rebuild hin hdeg hchild hpar hu.1 (hu.2.1 ▸ hmark) hu.2.2.1 hu.2.2.2
      (fun c hc => hptr c.root (root_mem_forestNodes hc)) ?_ ?_ ?_
    · intro c hc
      have hcr_in : c.root ∈ (FHTree.node u cs).nodes := child_mem_node hc c.root_mem_nodes
      have hu_ne_cr : u ≠ c.root := fun e => hnd_u (e ▸ root_mem_forestNodes hc)
      rcases eq_or_ne v u with rfl | hvu
      · rw [hk_v, hk_other c.root hcr_in hu_ne_cr.symm]
        exact IndexedMinPQ.PrioLT.of_le_of_lt
          (by dsimp only [IndexedMinPQ.PrioLE]; omega) (hprio c hc)
      · rw [hk_other u List.mem_cons_self hvu.symm]
        rcases eq_or_ne c.root v with hcv | hv_cr
        · rw [hcv, hk_v]
          rcases hord with hroot | ⟨p, hpv, hnlt⟩
          · exact absurd hroot hvu
          · obtain rfl : u = p := Fin.ext (by have := hpar c hc; rw [hcv, hpv] at this; omega)
            exact (IndexedMinPQ.prioLT_or_prioLT_of_ne (hcv ▸ hu_ne_cr) (st.key u) k).resolve_right
              hnlt
        · rw [hk_other c.root hcr_in hv_cr]; exact hprio c hc
    · intro i hi
      have hci := hunch (cs[i]).root (child_mem_node (List.getElem_mem hi) (cs[i]).root_mem_nodes)
      rw [hci.2.2.1, hci.2.1]
      exact hrank i hi
    · intro c hc
      by_cases hvc : v ∈ c.nodes
      · refine ih c hc (forestNodes_nodup_tree hnd_cs hc) hvc
          (fun x hx => hk_other x (child_mem_node hc hx))
          (fun x hx => hunch x (child_mem_node hc hx))
          (fun x hx => hptr x (child_desc_mem_forestNodes hc hx)) ?_
        rcases eq_or_ne v c.root with hvr | _
        · exact Or.inl hvr
        · exact hord.elim (fun hroot =>
            absurd ((hroot.trans (FHTree.root_node u cs)) ▸ mem_forestNodes_iff.mpr ⟨c, hc, hvc⟩)
              hnd_u) Or.inr
      · refine (hsub c hc).frame (fun x hx => ?_) (fun x hx => ?_)
        · let hxn := hunch x (child_mem_node hc hx)
          exact ⟨hxn.1, hxn.2.1, hxn.2.2.1, hxn.2.2.2,
            hk_other x (child_mem_node hc hx) fun e => hvc (e ▸ hx)⟩
        · let hxp := hptr x (child_desc_mem_forestNodes hc hx)
          exact ⟨hxp.1, hxp.2.1, hxp.2.2, Iff.rfl⟩

/-- Once cascading cuts finish (`pending = none`) and `minRoot` is updated against `(v, st.key v)`,
`CutInv` upgrades back to `FibRawInv`. -/
theorem CutInv.to_fibRawInv {n K_max : ℕ} {s : IndexedMinPQ.State n} {st st' : RawState n}
    {v m : Fin n} (h : CutInv n K_max s st v m none)
    (heq : st'.key = st.key ∧ st'.par = st.par ∧ st'.child = st.child ∧
      st'.left = st.left ∧ st'.right = st.right ∧ st'.deg = st.deg ∧
      st'.mark = st.mark ∧ st'.inHeap = st.inHeap ∧ st'.cons = st.cons ∧
      st'.numRoots = st.numRoots ∧ st'.numMarked = st.numMarked ∧ st'.sz = st.sz)
    (hmin : (IndexedMinPQ.PrioLT (v, st.key v) (m, st.key m) ∧ st'.minRoot = v.val + 1) ∨
      (¬IndexedMinPQ.PrioLT (v, st.key v) (m, st.key m) ∧ st'.minRoot = m.val + 1)) :
    FibRawInv n K_max s st' := by
  obtain ⟨ts, hts, hnd, hdom, hin, hkeys, hsz, hnr, hnm, hcons,
    ⟨rtail, _, hcirc, hperm⟩, ⟨T_v, hTv, hTv_r⟩, hmin_other⟩ := h
  rcases heq with ⟨hk, hp, hch, hl, hr, hd, hmk, hinh, hco, hnrr, hnmr, hszr⟩
  have hts' (T : FHTree n) (hT : T ∈ ts) : ValidRoot st' none T :=
    (hts T hT).frame_nodes fun _ _ =>
      ⟨congrFun hinh _, congrFun hmk _, congrFun hd _, congrFun hch _,
        congrFun hk _, congrFun hp _, congrFun hl _, congrFun hr _⟩
  refine ⟨ts, hts', hnd, hdom, fun x => hinh ▸ hin x, fun x kx => hk ▸ hkeys x kx,
    hszr.trans hsz, hnrr.trans hnr,
    hnmr.trans (hnm.trans (markedCount_congr fun u => by rw [hinh, hmk]).symm),
    fun d => hco ▸ hcons d, ?_⟩
  rw [hl, hr]
  rcases hmin with ⟨hlt, hmin_v⟩ | ⟨hnlt, hmin_m⟩
  · obtain ⟨vtail, hcirc_v, hperm_v⟩ :=
      hcirc.exists_head (hperm.symm.subset (hTv_r ▸ List.mem_map_of_mem (f := FHTree.root) hTv))
    refine Or.inr ⟨v, vtail, hmin_v, hcirc_v, hperm_v.trans hperm, fun T hT => hk ▸ ?_⟩
    exact if hTr : T.root = v then hTr ▸ .refl _ else hlt.le.trans (hmin_other T hT hTr)
  · refine Or.inr ⟨m, rtail, hmin_m, hcirc, hperm, fun T hT => hk ▸ ?_⟩
    exact if hTr : T.root = v then hTr ▸ IndexedMinPQ.not_prioLT_iff_prioLE.mp hnlt
      else hmin_other T hT hTr

end Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap
