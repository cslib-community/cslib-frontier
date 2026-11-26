/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Events
public import CslibFrontier.Logics.Propositional.CSP.Edge.Walk.Visits
import CslibFrontier.Foundations.Data.Finset.SymmDiff

/-!
# Blossoms returned by chronological forest search

The two LCA cases of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, Section 5.3,
printed pp. 11–12, and Definition 39/Lemma 41, printed pp. 19–20. The cycle, preparation,
pivot, timestamps and child ports are those computed by `Meeting.blossomData`.

## Main results

* `Meeting.Trace.blossom_correct`: both raw extractor branches satisfy Definition 39.
* `Meeting.Trace.variable_prepare_empty`: a variable LCA is an inconsistent root.
* `search_blossom_correct`: an actual fresh-run blossom result supplies valid preparation,
  a source-strength blossom, and unchanged defect count, from instance hypotheses alone.

The proof uses chronological prefix transfer as an alternative to the source's repeated
graph surgery, followed by its Lemma 37 rerooting at a constraint LCA. No contraction or
lifting algorithm, encoded runtime bound, or planar dichotomy is claimed here.
-/

public section

namespace Cslib.Logic.PL.CSP.Forest.Meeting

open DAG

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]
  {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool} {m : Meeting F}

/-- The two actual ancestral suffixes and their incoming terminal meeting ports. Shared
root-side copies before step `k` are omitted. This is the graph used in Lemma 41's preparation. -/
@[expose] def forkDAG (m : Meeting F) (k : ℕ) : DAG F :=
  ((pathDAG (m.left.walk.drop k) m.older.stamp).union
    (pathDAG (m.right.walk.drop k) m.older.stamp)).union
      (terminalPair ⟨m.current.input, m.older.length, true⟩ ⟨m.output, m.older.length, true⟩)

/-- Every fork arc is an actual ancestral arc or one of the two incoming meeting ports. -/
@[simp] theorem mem_forkDAG_arcs (m : Meeting F) (k : ℕ) (a : Arc F) :
    a ∈ (m.forkDAG k).arcs ↔
      a ∈ pathArcs (m.left.walk.drop k) m.older.stamp ∨
      a ∈ pathArcs (m.right.walk.drop k) m.older.stamp ∨
      a = ⟨m.current.input, m.older.length, true⟩ ∨ a = ⟨m.output, m.older.length, true⟩ := by
  simp only [forkDAG, DAG.union, terminalPair, pathDAG, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The suffix fork is a supported subgraph of the actual terminal pruned forest. -/
theorem Trace.fork_subgraph (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (k : ℕ) :
    (m.forkDAG k).Subgraph m.prunedDAG ∧ (m.forkDAG k).Supported := by
  have hT := h.pruned_isFDAG hF hf
  have hw := h.left_directed.drop hT.supported k
  have hz := h.right_directed.drop hT.supported k
  have ha : (⟨m.current.input, m.older.length, true⟩ : Arc F) ∈ m.prunedDAG.arcs := by
    rw [h.pruned_arcs]; simp
  have hb : (⟨m.output, m.older.length, true⟩ : Arc F) ∈ m.prunedDAG.arcs := by
    rw [h.pruned_arcs]; simp
  have hc : (⟨m.current.input, m.older.length, true⟩ : Arc F).copy =
      (⟨m.output, m.older.length, true⟩ : Arc F).copy :=
    Prod.ext ((mem_partners sem f _ _).mp h.partner).1 rfl
  let Q := terminalPair (⟨m.current.input, m.older.length, true⟩ : Arc F)
    ⟨m.output, m.older.length, true⟩
  have hQ : ∀ a ∈ Q.arcs, a = ⟨m.current.input, m.older.length, true⟩ ∨
      a = ⟨m.output, m.older.length, true⟩ := fun a ham => by
    simpa only [Q, terminalPair, Finset.mem_insert, Finset.mem_singleton] using ham
  have hqs : Q.Supported := fun a ham => by
    rcases hQ a ham with rfl | rfl <;> simp [Q, terminalPair, hc.symm]
  have hq : Q.Subgraph m.prunedDAG :=
    ⟨fun v hv => by
      rcases (show v = m.current.input.var ∨ v = m.output.var by simpa [Q, terminalPair] using hv)
        with rfl | rfl
      exacts [(hT.supported _ ha).1, (hT.supported _ hb).1],
    fun c hc' => Finset.mem_singleton.mp hc' ▸ (hT.supported _ ha).2,
    fun a ham => (hQ a ham).elim (· ▸ ha) (· ▸ hb)⟩
  exact ⟨((hw.subgraph hT.supported).union (hz.subgraph hT.supported)).union hq,
    ((pathDAG_supported _ _).union (pathDAG_supported _ _)).union hqs⟩

/-- Flipping the shared root prefix preserves the full f-DAG invariant on the actual
remaining suffix fork. Unused earlier branches are discarded, and original constraints
may recur later at different timestamps. -/
theorem Trace.prepare_fork_isFDAG (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F)
    (k : ℕ) (hk : 2 * k + 1 ≤ m.commonNodes.length) :
    (m.forkDAG k).IsFDAG sem ((m.left.walk.take k).flip f) := by
  have hT := h.pruned_isFDAG hF hf
  obtain ⟨hsub, hsup⟩ := h.fork_subgraph hF hf k
  have hw := h.left_directed.drop hT.supported k
  have hz := h.right_directed.drop hT.supported k
  have hchron := (h.expansion.grown.ancestry_chronological m.current.input.var).sublist
    (List.take_sublist k _)
  apply (h.left_directed.take k).flip_later_subgraph hT hM hchron hsub hsup
  intro c hc s hs
  change c ∈ ((pathDAG _ _).copies ∪ (pathDAG _ _).copies) ∪ {_} at hc
  simp only [Finset.mem_union, Finset.mem_singleton] at hc
  rcases hc with (hc | hc) | rfl
  · obtain ⟨t, ht, he⟩ := hw.mem_copies.mp hc
    exact (congrArg Prod.snd he) ▸
      (h.expansion.grown.ancestry_chronological _).rel_of_mem_take_of_mem_drop hs ht
  · obtain ⟨t, ht, he⟩ := hz.mem_copies.mp hc
    exact (congrArg Prod.snd he) ▸ h.prefix_time_lt_right_drop k hk hs ht
  · exact (m.older.mem_arcs
      (h.expansion.grown.ancestry_arcs _ (List.mem_of_mem_take hs)).1).2

/-- A constraint LCA ends the shared node prefix immediately before its two children. -/
theorem ancestor_constraint_length (m : Meeting F) {c : Copy F}
    (hc : m.ancestor? = some (.inr c)) :
    m.commonNodes.length = 2 * ((m.commonNodes.length - 1) / 2) + 2 := by
  have hpos : 0 < m.commonNodes.length := by
    cases he : m.commonNodes <;> simp_all [ancestor?]
  have hstep := (m.ancestor_constraint_index_lt hc).1
  by_cases hm : (m.commonNodes.length - 1) % 2 = 1
  · omega
  · have hh := (m.ancestor_at_common_index hc).1
    rw [show m.commonNodes.length - 1 = 2 * ((m.commonNodes.length - 1) / 2) by omega,
      m.left.nodes_getElem?_even (m.older.ancestry_length _) _ (Nat.le_of_lt hstep)] at hh
    cases hh

/-- The two steps selected by the raw constraint-LCA branch use that actual copied node. -/
theorem Trace.constraint_first_copies (h : Trace sem f m) {c : Copy F}
    (hc : m.ancestor? = some (.inr c)) {s t : Occurrence F × Occurrence F}
    (hs : m.left.walk.steps[(m.commonNodes.length - 1) / 2]? = some s)
    (ht : m.right.walk.steps[(m.commonNodes.length - 1) / 2]? = some t) :
    (inArc m.older.stamp s).copy = c ∧ (inArc m.older.stamp t).copy = c := by
  let k := (m.commonNodes.length - 1) / 2
  have hlen : m.commonNodes.length = 2 * k + 2 := m.ancestor_constraint_length hc
  have hside {u : V} {s : Occurrence F × Occurrence F}
      (hk : k < (m.older.ancestry u).walk.steps.length)
      (hn : (m.older.ancestry u).nodes[m.commonNodes.length - 1]? = some (.inr c))
      (hs : (m.older.ancestry u).walk.steps[k]? = some s) :
      (inArc m.older.stamp s).copy = c := by
    have hpl := m.older.ancestry_length u
    have hs' : (m.older.ancestry u).walk.steps[k] = s := by
      simpa only [List.getElem?_eq_getElem hk, Option.some.injEq] using hs
    have htime : (m.older.ancestry u).times[k]'(by omega) =
        m.older.stamp ((m.older.ancestry u).walk.steps[k]).1 := by
      simp only [h.expansion.grown.ancestry_times_eq_stamp u, List.getElem_map]
    rw [show m.commonNodes.length - 1 = 2 * k + 1 by omega,
      (m.older.ancestry u).nodes_getElem?_odd hpl k hk] at hn
    simpa only [htime, hs', inArc, Arc.copy] using Sum.inr.inj (Option.some.inj hn)
  exact ⟨hside (m.ancestor_constraint_index_lt hc).1 (m.ancestor_at_common_index hc).1 hs,
    hside (m.ancestor_constraint_index_lt hc).2 (m.ancestor_at_common_index hc).2 ht⟩

private theorem Trace.ancestry_times_drop (h : Trace sem f m) (u : V) (n : ℕ) :
    (m.older.ancestry u).times.drop n =
      ((m.older.ancestry u).walk.drop n).steps.map fun s => m.older.stamp s.1 := by
  simpa only [Walk.drop, List.map_drop] using
    congrArg (List.drop n) (h.expansion.grown.ancestry_times_eq_stamp u)

private theorem Trace.stamp_gt_of_drop_succ (h : Trace sem f m) {u : V} {k : ℕ}
    {s t : Occurrence F × Occurrence F}
    (hs : (m.older.ancestry u).walk.steps[k]? = some s)
    (ht : t ∈ ((m.older.ancestry u).walk.drop (k + 1)).steps) :
    m.older.stamp s.1 < m.older.stamp t.1 := by
  have hp := (h.expansion.grown.ancestry_chronological u).sublist (List.drop_sublist k _)
  change ((m.older.ancestry u).walk.drop k).steps.Pairwise _ at hp
  rw [Walk.steps_drop_of_getElem? hs] at hp
  exact (List.pairwise_cons.mp hp).1 t ht

/-- The child ports at a constraint LCA name distinct variables. Otherwise their common
child would extend the computed common-node prefix, contradicting maximality. -/
theorem Trace.constraint_children_ne (h : Trace sem f m) {c : Copy F}
    (hc : m.ancestor? = some (.inr c)) {s t : Occurrence F × Occurrence F}
    (hs : m.left.walk.steps[(m.commonNodes.length - 1) / 2]? = some s)
    (ht : m.right.walk.steps[(m.commonNodes.length - 1) / 2]? = some t) :
    s.2.var ≠ t.2.var := by
  let k := (m.commonNodes.length - 1) / 2
  have hdl := Walk.steps_drop_of_getElem? hs
  have hsl := List.mem_of_getElem? hs
  have htr := List.mem_of_getElem? ht
  have hsd : s ∈ (m.left.walk.drop ((m.commonNodes.length - 1) / 2)).steps :=
    hdl ▸ List.mem_cons_self
  have hcopies := h.constraint_first_copies hc hs ht
  have hinput := Log.incoming_time_unique
    (h.expansion.grown.ancestry_arcs _ hsl).1 (h.expansion.grown.ancestry_arcs _ htr).1
    rfl rfl (congrArg Prod.snd (hcopies.1.trans hcopies.2.symm))
  intro hv
  have houtput := h.expansion.grown.indegree
    (h.expansion.grown.ancestry_arcs _ hsl).2 (h.expansion.grown.ancestry_arcs _ htr).2
    rfl rfl hv
  have he : s = t := Prod.ext (congrArg Arc.occurrence hinput) (congrArg Arc.occurrence houtput)
  cases he
  have hl := h.expansion.grown.ancestry_step_full_nodes_prefix hsl
  have hr := h.expansion.grown.ancestry_step_full_nodes_prefix htr
  have hb := m.commonNodes_maximal _ hl hr
  have hnodes := (m.older.ancestry s.1.var).nodes_length (m.older.ancestry_length _)
  simp only [List.length_append, List.length_cons, List.length_nil, hnodes] at hb
  have hindex := h.expansion.grown.ancestry_step_prefix_length hsd
  have hlength : m.commonNodes.length = 2 * k + 2 := m.ancestor_constraint_length hc
  omega

/-- The copied constraint selected as the LCA is the earliest copy of the remaining fork. -/
theorem Trace.constraint_fork_earliest (h : Trace sem f m) {c : Copy F}
    (hc : m.ancestor? = some (.inr c)) {s t : Occurrence F × Occurrence F}
    (hs : m.left.walk.steps[(m.commonNodes.length - 1) / 2]? = some s)
    (ht : m.right.walk.steps[(m.commonNodes.length - 1) / 2]? = some t) :
    (m.forkDAG ((m.commonNodes.length - 1) / 2)).Earliest c := by
  let k := (m.commonNodes.length - 1) / 2
  have hdl := Walk.steps_drop_of_getElem? hs
  have hsl := List.mem_of_getElem? hs
  have hdr := Walk.steps_drop_of_getElem? ht
  have hw := (h.expansion.grown.ancestry_directed h.expansion.visited).drop
    (m.older.toDAG_supported m.roots) k
  have hz := (h.expansion.grown.ancestry_directed h.old_visited).drop
    (m.older.toDAG_supported m.roots) k
  have hcs := h.constraint_first_copies hc hs ht
  have hsm : s ∈ (m.left.walk.drop k).steps := hdl ▸ List.mem_cons_self
  have hmin (p : Walk F) (s : Occurrence F × Occurrence F) (tail)
      (hp : DirectedPath (m.older.toDAG m.roots) p m.older.stamp) (he : p.steps = s :: tail)
      (ho : p.steps.Pairwise (fun s t => m.older.stamp s.1 < m.older.stamp t.1))
      (hs : (inArc m.older.stamp s).copy = c) (d) (hd : d ∈ (pathDAG p m.older.stamp).copies) :
      c.2 ≤ d.2 := by
    obtain ⟨u, hu, heq⟩ := hp.mem_copies.mp hd
    rw [he] at hu ho
    rw [← congrArg Prod.snd hs, ← congrArg Prod.snd heq]
    exact (List.mem_cons.mp hu).elim (fun h => h ▸ le_rfl) fun hu =>
      ((List.pairwise_cons.mp ho).1 u hu).le
  refine ⟨Finset.mem_union_left _ (Finset.mem_union_left _ (hw.mem_copies.mpr ⟨s, hsm, hcs.1⟩)),
    fun d hd => ?_⟩
  change d ∈ ((pathDAG _ _).copies ∪ (pathDAG _ _).copies) ∪ {_} at hd
  simp only [Finset.mem_union, Finset.mem_singleton] at hd
  rcases hd with (hd | hd) | rfl
  · exact hmin _ s _ hw hdl ((h.expansion.grown.ancestry_chronological _).sublist
      (List.drop_sublist k _)) hcs.1 d hd
  · exact hmin _ t _ hz hdr ((h.expansion.grown.ancestry_chronological _).sublist
      (List.drop_sublist k _)) hcs.2 d hd
  · exact ((show (inArc m.older.stamp s).time = c.2 from congrArg Prod.snd hcs.1) ▸
      (m.older.mem_arcs (h.expansion.grown.ancestry_arcs _ hsl).1).2).le

/-- The root-side input at a constraint LCA is a leaf of the selected suffix fork. -/
theorem Trace.constraint_fork_leaf (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) {c : Copy F} (hc : m.ancestor? = some (.inr c))
    {s t : Occurrence F × Occurrence F}
    (hs : m.left.walk.steps[(m.commonNodes.length - 1) / 2]? = some s)
    (ht : m.right.walk.steps[(m.commonNodes.length - 1) / 2]? = some t) :
    ∀ a ∈ (m.forkDAG ((m.commonNodes.length - 1) / 2)).arcs,
      a.occurrence.var = s.1.var → a = inArc m.older.stamp s := by
  let k := (m.commonNodes.length - 1) / 2
  have hT := h.pruned_isFDAG hF hf
  have hdl := Walk.steps_drop_of_getElem? hs
  have hsl := List.mem_of_getElem? hs
  have hdr := Walk.steps_drop_of_getElem? ht
  have htr := List.mem_of_getElem? ht
  have hw := h.left_directed.drop hT.supported k
  have hz := h.right_directed.drop hT.supported k
  have hcs := h.constraint_first_copies hc hs ht
  have haeq := Log.incoming_time_unique (h.expansion.grown.ancestry_arcs _ hsl).1
    (h.expansion.grown.ancestry_arcs _ htr).1 rfl rfl
    (congrArg Prod.snd (hcs.1.trans hcs.2.symm))
  have hin : s.1 = t.1 := congrArg Arc.occurrence haeq
  have hls : s.1.var = (m.left.walk.drop k).start := by
    have hh := hw.walk.1; rw [hdl] at hh; exact hh.1
  have hrs : t.1.var = (m.right.walk.drop k).start := by
    have hh := hz.walk.1; rw [hdr] at hh; exact hh.1
  have hneL := hw.finish_ne_start hT (by rw [hdl]; simp)
  have hneR := hz.finish_ne_start hT (by rw [hdr]; simp)
  simp only [Walk.finish_drop, Meeting.left, Meeting.right, Log.ancestry_finish] at hneL hneR
  intro a ha hv
  rcases (mem_forkDAG_arcs _ _ _).mp ha with ha | ha | rfl | rfl
  · exact hw.start_arc_eq hT hdl ha (hv.trans hls)
  · exact (hz.start_arc_eq hT hdr ha (hv.trans ((congrArg Occurrence.var hin).trans hrs))).trans
      haeq.symm
  · exact False.elim (hneL (hv.trans hls))
  · exact False.elim (hneR (hv.trans ((congrArg Occurrence.var hin).trans hrs)))

/-- At the step selected at `(m.commonNodes.length - 1) / 2`, the suffix fork has precisely
its original single incoming port. The second incoming meeting port is at the strictly later
terminal copy. -/
theorem Trace.constraint_fork_incoming_eq (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) {s : Occurrence F × Occurrence F}
    (hs : m.left.walk.steps[(m.commonNodes.length - 1) / 2]? = some s) :
    ∀ a ∈ (m.forkDAG ((m.commonNodes.length - 1) / 2)).arcs,
      a.incoming = true → a.copy = (inArc m.older.stamp s).copy →
      a = inArc m.older.stamp s := by
  let k := (m.commonNodes.length - 1) / 2
  have hA := (h.expansion.grown.ancestry_arcs _ (List.mem_of_getElem? hs)).1
  have hbound : m.older.stamp s.1 < m.older.length := (m.older.mem_arcs hA).2
  have hsub := (h.fork_subgraph hF hf k).1
  intro a ha hi hac
  have haT := hsub.2.2 ha
  simp only [h.pruned_arcs, Finset.mem_insert, List.mem_toFinset] at haT
  rcases haT with rfl | rfl | haT
  · exact absurd (congrArg Prod.snd hac) hbound.ne'
  · exact absurd (congrArg Prod.snd hac) hbound.ne'
  · exact Log.incoming_time_unique haT hA hi rfl (congrArg Prod.snd hac)

/-- Source Lemma 41's constraint-LCA surgery: flip the actual root-to-left-child path,
remove its root-side input, and reverse that child's LCA incidence. The full remaining
fork is an f-DAG for the prepared labeling. -/
theorem Trace.reroot_constraint_fork (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F)
    {c : Copy F} (hc : m.ancestor? = some (.inr c))
    {s t : Occurrence F × Occurrence F}
    (hs : m.left.walk.steps[(m.commonNodes.length - 1) / 2]? = some s)
    (ht : m.right.walk.steps[(m.commonNodes.length - 1) / 2]? = some t) :
    ((m.forkDAG ((m.commonNodes.length - 1) / 2)).reroot
      (inArc m.older.stamp s) (outArc m.older.stamp s)).IsFDAG sem
      ((m.left.walk.take ((m.commonNodes.length - 1) / 2 + 1)).flip f) := by
  let k := (m.commonNodes.length - 1) / 2
  obtain ⟨hkl, hsval⟩ := List.getElem?_eq_some_iff.mp hs
  have hdl := Walk.steps_drop_of_getElem? hs
  have hsm : s ∈ (m.left.walk.drop k).steps := hdl ▸ List.mem_cons_self
  have hlink := (h.left_directed.walk.drop k).1
  rw [hdl] at hlink
  have hcopy : (inArc m.older.stamp s).copy = (outArc m.older.stamp s).copy :=
    Prod.ext hlink.2.1 rfl
  have hA : inArc m.older.stamp s ∈ (m.forkDAG k).arcs :=
    (mem_forkDAG_arcs _ _ _).mpr (Or.inl (Finset.mem_biUnion.mpr
      ⟨s, List.mem_toFinset.mpr hsm, by simp⟩))
  have hB : outArc m.older.stamp s ∈ (m.forkDAG k).arcs :=
    (mem_forkDAG_arcs _ _ _).mpr (Or.inl (Finset.mem_biUnion.mpr
      ⟨s, List.mem_toFinset.mpr hsm, by simp⟩))
  have hlen : m.commonNodes.length = 2 * k + 2 := m.ancestor_constraint_length hc
  have hY := h.prepare_fork_isFDAG hF hf hM k (by omega)
  have hfirst : (m.forkDAG k).Earliest (inArc m.older.stamp s).copy :=
    (h.constraint_first_copies hc hs ht).1.symm ▸ h.constraint_fork_earliest hc hs ht
  have hR := hY.reroot_earliest hM hA hB rfl rfl hcopy hfirst
    (h.constraint_fork_leaf hF hf hc hs ht) (h.constraint_fork_incoming_eq hF hf hs)
  have hflip : (m.left.walk.take (k + 1)).flip f =
      pairFlip ((m.left.walk.take k).flip f) s.1 s.2 := by
    simpa only [hsval] using h.left_directed.walk.flip_take_succ f hkl
  exact hflip.symm ▸ hR

/-- The constraint-LCA cycle, with its actual terminal and LCA timestamps, embeds into
the prepared rerooted fork. This proves the complete Definition 39 graph condition. -/
theorem Trace.constraint_cycle_isFDAG (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F)
    {c : Copy F} (hc : m.ancestor? = some (.inr c))
    {s t : Occurrence F × Occurrence F}
    (hs : m.left.walk.steps[(m.commonNodes.length - 1) / 2]? = some s)
    (ht : m.right.walk.steps[(m.commonNodes.length - 1) / 2]? = some t) :
    let k := (m.commonNodes.length - 1) / 2
    let w := m.left.walk.drop (k + 1)
    let z := m.right.walk.drop (k + 1)
    (blossomDAG (((w.snoc m.current.input m.output).append z.reverse).snoc t.2 s.2)
      (w.steps.map (fun u => m.older.stamp u.1) ++ [m.older.length] ++
        (z.steps.map fun u => m.older.stamp u.1).reverse ++ [c.2]) (w.steps.length + 1)).IsFDAG
      sem ((m.left.walk.take (k + 1)).flip f) := by
  let k := (m.commonNodes.length - 1) / 2
  let w := m.left.walk.drop (k + 1)
  let z := m.right.walk.drop (k + 1)
  let R := (m.forkDAG k).reroot (inArc m.older.stamp s) (outArc m.older.stamp s)
  have hR : R.IsFDAG sem ((m.left.walk.take (k + 1)).flip f) :=
    h.reroot_constraint_fork hF hf hM hc hs ht
  have hdl := Walk.steps_drop_of_getElem? hs
  have hsm := List.mem_of_getElem? hs
  have hdr := Walk.steps_drop_of_getElem? ht
  have hcs := h.constraint_first_copies hc hs ht
  have hst : m.older.stamp s.1 = c.2 := congrArg Prod.snd hcs.1
  have htt : m.older.stamp t.1 = c.2 := congrArg Prod.snd hcs.2
  have hnew : (outArc m.older.stamp s).reverse ∈ R.arcs :=
    mem_reroot_arcs.mpr (Or.inl rfl)
  have hbase : s.2.var ∈ R.vars := (hR.supported _ hnew).1
  have hwlt : ∀ u ∈ w.steps, c.2 < m.older.stamp u.1 :=
    fun u hu => hst ▸ h.stamp_gt_of_drop_succ hs hu
  have hzlt : ∀ u ∈ z.steps, c.2 < m.older.stamp u.1 :=
    fun u hu => htt ▸ h.stamp_gt_of_drop_succ ht hu
  have hlate : c.2 < m.older.length :=
    hst ▸ (m.older.mem_arcs (h.expansion.grown.ancestry_arcs _ hsm).1).2
  have hsurvive : ∀ a ∈ (m.forkDAG k).arcs, c.2 < a.time → a ∈ R.arcs := fun a ha hl =>
    mem_reroot_arcs.mpr (.inr ⟨ha, fun he => hl.ne' ((congrArg Arc.time he).trans hst),
      fun he => hl.ne' ((congrArg Arc.time he).trans hst)⟩)
  have hpathArcs : ∀ {p : Walk F} {u}, u ∈ p.steps →
      inArc m.older.stamp u ∈ pathArcs p m.older.stamp ∧
      outArc m.older.stamp u ∈ pathArcs p m.older.stamp := fun hu =>
    ⟨Finset.mem_biUnion.mpr ⟨_, List.mem_toFinset.mpr hu, by simp⟩,
      Finset.mem_biUnion.mpr ⟨_, List.mem_toFinset.mpr hu, by simp⟩⟩
  have hleftU : ∀ u ∈ w.steps,
      inArc m.older.stamp u ∈ (m.forkDAG k).arcs ∧
      outArc m.older.stamp u ∈ (m.forkDAG k).arcs := fun u hu => by
    obtain ⟨hi, ho⟩ := hpathArcs (p := m.left.walk.drop k) (hdl ▸ List.mem_cons_of_mem s hu)
    exact ⟨(mem_forkDAG_arcs _ _ _).mpr (Or.inl hi), (mem_forkDAG_arcs _ _ _).mpr (Or.inl ho)⟩
  have hrightU : ∀ u ∈ z.steps,
      inArc m.older.stamp u ∈ (m.forkDAG k).arcs ∧
      outArc m.older.stamp u ∈ (m.forkDAG k).arcs := fun u hu => by
    obtain ⟨hi, ho⟩ := hpathArcs (p := m.right.walk.drop k) (hdr ▸ List.mem_cons_of_mem t hu)
    exact ⟨(mem_forkDAG_arcs _ _ _).mpr (Or.inr (Or.inl hi)),
      (mem_forkDAG_arcs _ _ _).mpr (Or.inr (Or.inl ho))⟩
  have hrightPort : outArc m.older.stamp t ∈ R.arcs := by
    apply mem_reroot_arcs.mpr
    refine Or.inr ⟨(mem_forkDAG_arcs _ _ _).mpr
      (Or.inr (Or.inl (hpathArcs (p := m.right.walk.drop k) (hdr ▸ List.mem_cons_self)).2)), ?_, ?_⟩
    · exact fun he => by cases congrArg Arc.incoming he
    · intro he
      exact h.constraint_children_ne hc hs ht (congrArg (fun a : Arc F => a.occurrence.var) he).symm
  apply hR.subgraph (S := blossomDAG _ _ _) ?_ (blossomDAG_supported _ _ _)
  apply blossomDAG_subgraph_of_arcs _ _ _
    (by change (m.left.walk.take (k + 1)).finish ∈ R.vars
        rwa [Walk.finish_take_succ_of_getElem? hs]) hR.supported
  intro a ham
  have hlen :
      (w.steps.map (fun u => m.older.stamp u.1) ++ [m.older.length] ++
        (z.steps.map fun u => m.older.stamp u.1).reverse).length =
      ((w.snoc m.current.input m.output).append z.reverse).steps.length := by
    simp only [Walk.append, Walk.snoc, Walk.reverse, List.length_append, List.length_map,
      List.length_reverse, List.length_singleton]
  have hpivot : w.steps.length + 1 ≤
      ((w.snoc m.current.input m.output).append z.reverse).steps.length := by
    simp only [Walk.append, Walk.snoc, Walk.reverse, List.length_append, List.length_map,
      List.length_reverse, List.length_singleton]
    omega
  change a ∈ blossomArcs
    (((w.snoc m.current.input m.output).append z.reverse).steps ++ [(t.2, s.2)])
    ((w.steps.map (fun u => m.older.stamp u.1) ++ [m.older.length] ++
      (z.steps.map fun u => m.older.stamp u.1).reverse) ++ [c.2]) (w.steps.length + 1) at ham
  rw [blossomArcs_append_after _ _ _ hlen hpivot] at ham
  rcases List.mem_append.mp ham with ham | ham
  · have hclass := blossomArcs_meeting_mem m.older.stamp m.older.stamp w.steps z.steps
      m.current.input m.output m.older.length (by
        simpa only [Walk.append, Walk.snoc, Walk.reverse, List.append_assoc, List.singleton_append]
          using ham)
    rcases hclass with ⟨u, hu, rfl | rfl⟩ | rfl | rfl | ⟨u, hu, rfl | rfl⟩
    · exact hsurvive _ (hleftU u hu).1 (hwlt u hu)
    · exact hsurvive _ (hleftU u hu).2 (hwlt u hu)
    · exact hsurvive _ ((mem_forkDAG_arcs _ _ _).mpr (Or.inr (Or.inr (Or.inl rfl)))) hlate
    · exact hsurvive _ ((mem_forkDAG_arcs _ _ _).mpr (Or.inr (Or.inr (Or.inr rfl)))) hlate
    · exact hsurvive _ (hrightU u hu).1 (hzlt u hu)
    · exact hsurvive _ (hrightU u hu).2 (hzlt u hu)
  · rcases (show a = ⟨t.2, c.2, false⟩ ∨ a = ⟨s.2, c.2, true⟩ by simpa using ham) with rfl | rfl
    · simpa only [outArc, htt] using hrightPort
    · simpa only [Arc.reverse, outArc, hst, Bool.not_false] using hnew

/-- Past the common prefix, joining the two actual ancestral suffixes at the terminal
pair gives an incidence trail. This applies to both LCA branches. -/
theorem Trace.drop_join_isWalk (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (k : ℕ) (hk : m.commonNodes.length < 2 * k + 2) :
    (((m.left.walk.drop k).snoc m.current.input m.output).append
      (m.right.walk.drop k).reverse).IsWalk := by
  have hT := h.pruned_isFDAG hF hf
  have hw := h.left_directed.drop hT.supported k
  have hz := h.right_directed.drop hT.supported k
  have hd := (h.left_drop_disjoint_right k hk).mono_right
    (h.right_directed.drop_copies_subset hT.supported k)
  have hpair := (mem_partners sem f _ _).mp h.partner
  have hused : ∀ v n o, o ∈ ((m.older.ancestry v).walk.drop n).edges → o ∈ m.older.used :=
    fun v n o ho => m.older.ancestry_edges_subset v
      (((List.drop_sublist n (m.older.ancestry v).walk.steps).flatMap
        (fun s => [s.1, s.2])).subset ho)
  apply hw.walk.join_meeting hz.walk
    (by simp only [Walk.finish_drop, Meeting.left, Log.ancestry_finish])
    (by simp only [Walk.finish_drop, Meeting.right, Log.ancestry_finish]) hpair.1
    (fun he => hpair.2.1 (congrArg Occurrence.var he)) (hw.disjoint_edges hz hT hd)
  all_goals first
    | exact fun ho => h.expansion.unused (hused _ _ _ ho)
    | exact fun ho => h.output_unused (hused _ _ _ ho)

/-- The constraint-LCA branch closes its joined suffixes through the two distinct,
fresh LCA child incidences. No incidence is repeated by the resulting closed trail. -/
theorem Trace.constraint_cycle_isWalk (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) {c : Copy F} (hc : m.ancestor? = some (.inr c))
    {s t : Occurrence F × Occurrence F}
    (hs : m.left.walk.steps[(m.commonNodes.length - 1) / 2]? = some s)
    (ht : m.right.walk.steps[(m.commonNodes.length - 1) / 2]? = some t) :
    let k := (m.commonNodes.length - 1) / 2
    ((((m.left.walk.drop (k + 1)).snoc m.current.input m.output).append
      (m.right.walk.drop (k + 1)).reverse).snoc t.2 s.2).IsWalk := by
  let k := (m.commonNodes.length - 1) / 2
  let w := m.left.walk.drop (k + 1)
  let z := m.right.walk.drop (k + 1)
  have hsm := List.mem_of_getElem? hs
  have htm := List.mem_of_getElem? ht
  have hcs := h.constraint_first_copies hc hs ht
  have hT := h.pruned_isFDAG hF hf
  have hw := h.left_directed.drop hT.supported (k + 1)
  have hz := h.right_directed.drop hT.supported (k + 1)
  have hbound : m.commonNodes.length < 2 * (k + 1) + 2 :=
    (m.ancestor_constraint_length hc : m.commonNodes.length = 2 * k + 2).trans_lt (by omega)
  have hj : ((w.snoc m.current.input m.output).append z.reverse).IsWalk :=
    h.drop_join_isWalk hF hf (k + 1) hbound
  have hleftlate : ∀ u ∈ w.steps, c.2 < m.older.stamp u.1 :=
    fun u hu => congrArg Prod.snd hcs.1 ▸ h.stamp_gt_of_drop_succ hs hu
  have hrightlate : ∀ u ∈ z.steps, c.2 < m.older.stamp u.1 :=
    fun u hu => congrArg Prod.snd hcs.2 ▸ h.stamp_gt_of_drop_succ ht hu
  have hsa := h.left_directed.outgoing s hsm
  have hta := h.right_directed.outgoing t htm
  have hsused : s.2 ∈ m.older.used :=
    m.older.ancestry_edges_subset _ (List.mem_flatMap.mpr ⟨s, hsm, by simp⟩)
  have htused : t.2 ∈ m.older.used :=
    m.older.ancestry_edges_subset _ (List.mem_flatMap.mpr ⟨t, htm, by simp⟩)
  have hnot : ∀ a ∈ m.prunedDAG.arcs, a.time = c.2 → a.occurrence ∈ m.older.used →
      a.occurrence ∉ ((w.snoc m.current.input m.output).append z.reverse).edges := by
    intro a ha hat hau ho
    rw [Walk.edges_append, Walk.edges_reverse] at ho
    have haw := hw.occurrence_not_mem_of_earlier hT ha (by simpa only [hat] using hleftlate)
    have haz := hz.occurrence_not_mem_of_earlier hT ha (by simpa only [hat] using hrightlate)
    rcases List.mem_append.mp ho with ho | ho
    · change a.occurrence ∈ Walk.edgesOf (w.steps ++ [(m.current.input, m.output)]) at ho
      rw [Walk.edgesOf_append] at ho
      rcases List.mem_append.mp ho with ho | ho
      · exact haw ho
      · obtain he | he : a.occurrence = m.current.input ∨ a.occurrence = m.output := by
          simpa [Walk.edgesOf] using ho
        exacts [h.expansion.unused (he ▸ hau), h.output_unused (he ▸ hau)]
    · exact haz (List.mem_reverse.mp ho)
  apply hj.snoc
  · rw [Walk.finish_join_meeting _ _ _ _ hz.walk.1
      (by simp only [Walk.finish_drop, Meeting.right, Log.ancestry_finish])]
    exact (Walk.finish_take_succ_of_getElem? ht).symm
  · have hl := h.left_directed.walk.1
    have hr := h.right_directed.walk.1
    obtain ⟨pre, post, he⟩ := List.mem_iff_append.mp hsm
    rw [he, Walk.linked_append_iff] at hl
    obtain ⟨pre', post', he'⟩ := List.mem_iff_append.mp htm
    rw [he', Walk.linked_append_iff] at hr
    exact hr.2.2.1.symm.trans ((congrArg Prod.fst hcs.2).trans
      ((congrArg Prod.fst hcs.1).symm.trans hl.2.2.1))
  · exact fun he => h.constraint_children_ne hc hs ht (congrArg Occurrence.var he).symm
  · exact hnot (outArc m.older.stamp t) hta (congrArg Prod.snd hcs.2) htused
  · exact hnot (outArc m.older.stamp s) hsa (congrArg Prod.snd hcs.1) hsused

/-- The raw constraint-LCA extractor supplies precisely the rerooted cycle just proved
to be an f-DAG, with its actual timestamps and child incidences. -/
theorem Trace.constraint_blossom_isFDAG (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F)
    {c : Copy F} (hc : m.ancestor? = some (.inr c)) {b : BlossomData F}
    (hb : m.blossomData = some b) :
    (blossomDAG b.cycle b.times b.pivot).IsFDAG sem (b.prepare.flip f) := by
  rcases (m.blossomData_eq_some_iff b).mp hb with ⟨_, ha, _⟩ | ⟨c', s, t, ha, hs, ht, rfl⟩
  · rw [hc] at ha; cases ha
  · cases Sum.inr.inj (Option.some.inj (hc.symm.trans ha))
    dsimp only [Meeting.left, Meeting.right]
    rw [h.ancestry_times_drop, h.ancestry_times_drop]
    exact h.constraint_cycle_isFDAG hF hf hM hc hs ht

/-- Both LCA branches return the full timestamped f-DAG required in Definition 39,
under the labeling obtained by their actual preparatory root-path flip. -/
theorem Trace.blossom_isFDAG (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F)
    {b : BlossomData F} (hb : m.blossomData = some b) :
    (blossomDAG b.cycle b.times b.pivot).IsFDAG sem (b.prepare.flip f) := by
  match ha : m.ancestor? with
  | none => simp [blossomData, ha] at hb
  | some (.inl v) => exact h.variable_blossom_isFDAG hF hf hM ha hb
  | some (.inr c) => exact h.constraint_blossom_isFDAG hF hf hM ha hb

/-- Joining suffixes of actual ancestries preserves original internal consistency.
Reversal is used here only for internal consistency, not for f-walk prefix validity. -/
theorem Trace.drop_join_consistent (h : Trace sem f m) (k : ℕ) :
    Walk.InternallyConsistent f
      (((m.left.walk.drop k).snoc m.current.input m.output).append
        (m.right.walk.drop k).reverse).steps := by
  have hg : Grown sem f (Forest.roots f) m.older := h.roots_eq ▸ h.expansion.grown
  have hrc : Walk.InternallyConsistent f (m.right.walk.drop k).steps := by
    change Walk.InternallyConsistent f (m.right.walk.steps.drop k)
    simpa only [List.append_nil, Meeting.right] using Walk.InternallyConsistent.append_of_outputs
      (ts := []) (fun s hs => hg.ancestry_output_consistent _ (List.mem_of_mem_drop hs)) trivial
  have htail : Walk.InternallyConsistent f
      ((m.current.input, m.output) :: (m.right.walk.drop k).reverse.steps) := by
    refine ⟨?_, hrc.reverse (h.right_directed.walk.drop k).1⟩
    by_cases hz : (m.right.walk.drop k).steps = []
    · exact Or.inl (by simp [Walk.reverse, hz])
    · exact Or.inr (hg.ancestry_finish_consistent fun he =>
        hz (by simp [Walk.drop, Meeting.right, he]))
  change Walk.InternallyConsistent f
    (((m.left.walk.drop k).steps ++ [(m.current.input, m.output)]) ++
      (m.right.walk.drop k).reverse.steps)
  rw [List.append_assoc]
  exact Walk.InternallyConsistent.append_of_outputs
    (fun s hs => hg.ancestry_output_consistent _ (List.mem_of_mem_drop hs)) htail

/-- The actual cycle in either branch is internally consistent under the original
labeling. Only its base can be inconsistent after preparation. -/
theorem Trace.blossom_original_consistent (h : Trace sem f m) {b : BlossomData F}
    (hb : m.blossomData = some b) : Walk.InternallyConsistent f b.cycle.steps := by
  rcases (m.blossomData_eq_some_iff b).mp hb with ⟨_, _, rfl⟩ | ⟨_, s, t, _, _, ht, rfl⟩
  · exact h.drop_join_consistent _
  · let k := (m.commonNodes.length - 1) / 2
    have hg : Grown sem f (Forest.roots f) m.older := h.roots_eq ▸ h.expansion.grown
    apply (h.drop_join_consistent (k + 1)).snoc
      (m.left.walk.drop (k + 1)).start t.2 s.2 (Or.inr ?_)
    change ¬ Inconsistent f
      (((m.left.walk.drop (k + 1)).snoc m.current.input m.output).append
        (m.right.walk.drop (k + 1)).reverse).finish
    rw [Walk.finish_join_meeting _ _ _ _ (h.right_directed.walk.drop (k + 1)).1
      (by simp only [Walk.finish_drop, Meeting.right, Log.ancestry_finish]),
      Walk.drop, Walk.finish_take_succ_of_getElem? ht]
    exact hg.ancestry_output_consistent _ (List.mem_of_getElem? ht)

/-- Both actual LCA cycles are closed incidence trails, including the final pair of
fresh LCA child ports in the copied-constraint branch. -/
theorem Trace.blossom_cycle_isWalk (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) {b : BlossomData F} (hb : m.blossomData = some b) :
    b.cycle.IsWalk := by
  rcases (m.blossomData_eq_some_iff b).mp hb with ⟨_, ha, rfl⟩ | ⟨_, _, _, ha, hs, ht, rfl⟩
  · apply h.drop_join_isWalk hF hf
    have hh := m.ancestor_variable_length ha
    omega
  · exact h.constraint_cycle_isWalk hF hf ha hs ht

/-- Every returned preparatory walk is an actual prefix of the left root ancestry. -/
theorem blossom_prepare_prefix {b : BlossomData F} (hb : m.blossomData = some b) :
    ∃ n, b.prepare = m.left.walk.take n := by
  rcases (m.blossomData_eq_some_iff b).mp hb with ⟨_, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ <;>
    exact ⟨_, rfl⟩

/-- The preparatory root path ends at the base of the actual returned cycle. -/
theorem blossom_prepare_finish {b : BlossomData F} (hb : m.blossomData = some b) :
    b.prepare.finish = b.cycle.start := by
  rcases (m.blossomData_eq_some_iff b).mp hb with ⟨_, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ <;> rfl

/-- Timestamp and pivot metadata from either extractor branch have exactly the lengths
needed for its two-arm cycle, and the terminal meeting step is present. -/
theorem blossom_metadata {b : BlossomData F} (hb : m.blossomData = some b) :
    b.times.length = b.cycle.steps.length ∧ 0 < b.pivot ∧ b.pivot ≤ b.cycle.steps.length := by
  have hl : m.left.times.length = m.left.walk.steps.length :=
    m.older.ancestry_length m.current.input.var
  have hr : m.right.times.length = m.right.walk.steps.length :=
    m.older.ancestry_length m.output.var
  rcases (m.blossomData_eq_some_iff b).mp hb with ⟨_, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ <;>
    simp only [Walk.append, Walk.snoc, Walk.reverse, Walk.drop, List.length_append,
      List.length_map, List.length_reverse, List.length_singleton, List.length_drop] <;>
    omega

private theorem Trace.join_times_nodup (h : Trace sem f m) (k : ℕ)
    (hk : m.commonNodes.length < 2 * k + 2) :
    (m.left.times.drop k ++ [m.older.length] ++ (m.right.times.drop k).reverse).Nodup := by
  have hleft : (m.left.times.drop k).Nodup :=
    ((m.older.ancestry_times_pairwise m.current.input.var).imp ne_of_lt).sublist
      (List.drop_sublist _ _)
  have hright : (m.right.times.drop k).Nodup :=
    ((m.older.ancestry_times_pairwise m.output.var).imp ne_of_lt).sublist
      (List.drop_sublist _ _)
  have hfreshL : ∀ t ∈ m.left.times.drop k, t < m.older.length :=
    fun t ht => m.older.ancestry_time_lt _ (List.mem_of_mem_drop ht)
  have hfreshR : ∀ t ∈ m.right.times.drop k, t < m.older.length :=
    fun t ht => m.older.ancestry_time_lt _ (List.mem_of_mem_drop ht)
  have hcross : ∀ t ∈ m.left.times.drop k, ∀ u ∈ m.right.times.drop k, t ≠ u := by
    intro t ht u hu he
    dsimp only [Meeting.left, Meeting.right] at ht hu
    rw [h.ancestry_times_drop] at ht hu
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hu
    have hzfull := List.mem_of_mem_drop hz
    have hc := congrArg Arc.copy (Log.incoming_time_unique
      (h.expansion.grown.ancestry_arcs _ (List.mem_of_mem_drop hs)).1
      (h.expansion.grown.ancestry_arcs _ hzfull).1 rfl rfl he)
    have hw := (h.expansion.grown.ancestry_directed h.expansion.visited).drop
      (m.older.toDAG_supported m.roots) k
    exact Finset.disjoint_left.mp (h.left_drop_disjoint_right k hk)
      (hw.mem_copies.mpr ⟨s, hs, rfl⟩)
      (h.right_directed.mem_copies.mpr ⟨z, hzfull, hc.symm⟩)
  rw [List.nodup_append, List.nodup_append]
  refine ⟨⟨hleft, by simp, ?_⟩, List.nodup_reverse.mpr hright, ?_⟩
  · exact fun t ht u hu he => Nat.ne_of_lt (hfreshL t ht) (he.trans (List.mem_singleton.mp hu))
  · intro t ht u hu he
    have hum := List.mem_reverse.mp hu
    rcases List.mem_append.mp ht with ht | ht
    · exact hcross t ht u hum he
    · exact Nat.ne_of_lt (hfreshR u hum) (he.symm.trans (List.mem_singleton.mp ht))

/-- Actual extractor timestamps distinguish every copied cycle step in both LCA branches.
The cross-arm distinction follows from the ancestry common-prefix theorem. Original
constraints may still occur repeatedly, at different timestamps. -/
theorem Trace.blossom_times_nodup (h : Trace sem f m) {b : BlossomData F}
    (hb : m.blossomData = some b) : b.times.Nodup := by
  rcases (m.blossomData_eq_some_iff b).mp hb with ⟨_, ha, rfl⟩ | ⟨c, s, t, ha, hs, ht, rfl⟩
  · apply h.join_times_nodup
    have hl := m.ancestor_variable_length ha
    omega
  · let k := (m.commonNodes.length - 1) / 2
    have hcs := h.constraint_first_copies ha hs ht
    have hst : m.older.stamp s.1 = c.2 := congrArg Prod.snd hcs.1
    have hlast : c.2 < m.older.length :=
      hst ▸ (m.older.mem_arcs (h.expansion.grown.ancestry_arcs _ (List.mem_of_getElem? hs)).1).2
    have hbound : m.commonNodes.length < 2 * (k + 1) + 2 :=
      (m.ancestor_constraint_length ha : m.commonNodes.length = 2 * k + 2).trans_lt (by omega)
    have hlateSide : ∀ {v : V} {x : Occurrence F × Occurrence F},
        (m.older.ancestry v).walk.steps[k]? = some x → (inArc m.older.stamp x).copy = c →
        ∀ t' ∈ (m.older.ancestry v).times.drop (k + 1), c.2 < t' := by
      intro v x hx hxc t' ht'
      rw [h.ancestry_times_drop] at ht'
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht'
      exact (congrArg Prod.snd hxc) ▸ h.stamp_gt_of_drop_succ hx hw
    apply List.nodup_append.mpr
    refine ⟨h.join_times_nodup (k + 1) hbound, by simp, fun t' ht' u hu => ?_⟩
    simp only [List.mem_append, List.mem_singleton, List.mem_reverse] at ht' hu
    subst hu
    rcases ht' with (ht' | rfl) | ht'
    · exact (hlateSide hs hcs.1 _ ht').ne'
    · exact hlast.ne'
    · exact (hlateSide ht hcs.2 _ ht').ne'

/-- The returned preparatory path is a trail from an originally inconsistent root. -/
theorem Trace.blossom_prepare_isWalk (h : Trace sem f m) {b : BlossomData F}
    (hb : m.blossomData = some b) : b.prepare.IsWalk ∧ Inconsistent f b.prepare.start := by
  obtain ⟨n, hp⟩ := blossom_prepare_prefix hb
  rw [hp]
  exact ⟨h.left_directed.walk.take n,
    (mem_roots f _).mp (h.roots_eq ▸ h.expansion.grown.ancestry_start_root h.expansion.visited)⟩

/-- A variable LCA of an actual terminal event is a root. Its returned preparatory
path is therefore empty, as specified in source Section 5.3. -/
theorem Trace.variable_prepare_empty (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) {v : V} (ha : m.ancestor? = some (.inl v)) :
    (m.left.walk.take ((m.commonNodes.length - 1) / 2)).steps = [] := by
  let k := (m.commonNodes.length - 1) / 2
  let w := m.left.walk.drop k
  let z := m.right.walk.drop k
  have hT := h.pruned_isFDAG hF hf
  have hw := h.left_directed.drop hT.supported k
  have hz := h.right_directed.drop hT.supported k
  have hbase := m.ancestor_variable_prefix ha
  have hbound : m.commonNodes.length < 2 * k + 2 :=
    (m.ancestor_variable_length ha : m.commonNodes.length = 2 * k + 1).trans_lt (by omega)
  have hd := (h.left_drop_disjoint_right k hbound).mono_right
    (h.right_directed.drop_copies_subset hT.supported k)
  have hab := (mem_partners sem f _ _).mp h.partner
  let a : Arc F := ⟨m.current.input, m.older.length, true⟩
  let b : Arc F := ⟨m.output, m.older.length, true⟩
  have hac : a.copy = m.copy := rfl
  have hbc : b.copy = m.copy := Prod.ext hab.1.symm rfl
  have ham : a ∈ m.prunedDAG.arcs := by rw [h.pruned_arcs]; simp [a]
  have hbm : b ∈ m.prunedDAG.arcs := by rw [h.pruned_arcs]; simp [b]
  have hfirst (q : Walk F) (hq : DirectedPath m.prunedDAG q m.older.stamp) (d : Arc F)
      (hdm : d ∈ m.prunedDAG.arcs) (hdi : d.incoming = true) (hdv : d.occurrence.var = q.finish) :
      ∃ e ∈ m.prunedDAG.arcs, e.incoming = true ∧ e.occurrence.var = q.start ∧
        ((e.copy ∈ (pathDAG q m.older.stamp).copies) ∨ e = d) := by
    cases he : q.steps with
    | nil =>
      refine ⟨d, hdm, hdi, ?_, Or.inr rfl⟩
      simpa only [Walk.finish, he, Walk.finishFrom] using hdv
    | cons s ss =>
      have hsm : s ∈ q.steps := by rw [he]; exact List.mem_cons_self
      have hlink := hq.walk.1
      rw [he] at hlink
      exact ⟨inArc m.older.stamp s, hq.incoming s hsm, rfl, hlink.1,
        Or.inl (hq.mem_copies.mpr ⟨s, hsm, rfl⟩)⟩
  obtain ⟨x, hxm, hxi, hxv, hxc⟩ := hfirst w hw a ham rfl
    (by change m.current.input.var = (m.left.walk.drop k).finish
        simp only [Walk.finish_drop, Meeting.left, Log.ancestry_finish])
  obtain ⟨y, hym, hyi, hyv, hyc⟩ := hfirst z hz b hbm rfl
    (by change m.output.var = (m.right.walk.drop k).finish
        simp only [Walk.finish_drop, Meeting.right, Log.ancestry_finish])
  have hxbase : x.occurrence.var = v := hxv.trans hbase.1
  have hybase : y.occurrence.var = v := hyv.trans hbase.2
  have hxy : x ≠ y := by
    intro he
    rcases hxc with hxc | rfl <;> rcases hyc with hyc | rfl
    · exact Finset.disjoint_left.mp hd hxc (he.symm ▸ hyc)
    · exact h.copy_fresh h.expansion.visited (((congrArg Arc.copy he).trans hbc) ▸
        h.left_directed.drop_copies_subset hT.supported k hxc)
    · exact h.copy_fresh h.old_visited (((congrArg Arc.copy he).symm.trans hac) ▸
        h.right_directed.drop_copies_subset hT.supported k hyc)
    · exact hab.2.1 (congrArg (fun e : Arc F => e.occurrence.var) he)
  by_contra hn
  obtain ⟨s, hs, hsf⟩ := Walk.finish_step (m.left.walk.take k) hn
  have hsm : s ∈ m.left.walk.steps := List.mem_of_mem_take hs
  have hparent := h.left_directed.outgoing s hsm
  have hpv : (outArc m.older.stamp s).occurrence.var = v := hsf.trans hbase.1
  exact hxy (hT.incoming_eq_of_parent hF hparent hxm hym rfl hxi hyi
    (hxbase.trans hpv.symm) (hybase.trans hpv.symm))

/-- A nonempty preparatory path ends at an originally consistent discovered variable. -/
theorem Trace.blossom_prepare_finish_consistent (h : Trace sem f m) {b : BlossomData F}
    (hb : m.blossomData = some b) (hn : b.prepare.steps ≠ []) :
    ¬ Inconsistent f b.prepare.finish := by
  obtain ⟨s, hs, he⟩ := Walk.finish_step b.prepare hn
  obtain ⟨n, hp⟩ := blossom_prepare_prefix hb
  rw [hp] at hs
  have hg : Grown sem f (Forest.roots f) m.older := h.roots_eq ▸ h.expansion.grown
  rw [← he]
  exact hg.ancestry_output_consistent _ (List.mem_of_mem_take hs)

open scoped symmDiff in
/-- Preparation moves the original root defect to the actual cycle base. -/
theorem Trace.blossom_base_inconsistent (h : Trace sem f m) (hF : EdgeInstance F)
    {b : BlossomData F} (hb : m.blossomData = some b) :
    Inconsistent (b.prepare.flip f) b.cycle.start := by
  obtain ⟨hw, hr⟩ := h.blossom_prepare_isWalk hb
  rw [← blossom_prepare_finish hb, ← mem_defects, hw.defects_flip hF]
  by_cases hn : b.prepare.steps = []
  · simp [Walk.finish, hn, Walk.finishFrom, mem_defects, hr]
  · have hc := h.blossom_prepare_finish_consistent hb hn
    have he : b.prepare.finish ≠ b.prepare.start := fun he => hc (he.symm ▸ hr)
    simp [Finset.mem_symmDiff, mem_defects, hc, he]

open scoped symmDiff in
/-- Preparatory root-path flipping preserves the number of defects. This is the
counting interface needed before contracting the returned blossom. -/
theorem Trace.blossom_prepare_card_defects (h : Trace sem f m) (hF : EdgeInstance F)
    {b : BlossomData F} (hb : m.blossomData = some b) :
    (defects (b.prepare.flip f)).card = (defects f).card := by
  obtain ⟨hw, hr⟩ := h.blossom_prepare_isWalk hb
  rw [hw.defects_flip hF]
  by_cases hn : b.prepare.steps = []
  · simp [Walk.finish, hn, Walk.finishFrom]
  · have hrm := mem_defects.mpr hr
    have he : b.prepare.finish ∉ (defects f).erase b.prepare.start := fun hm =>
      h.blossom_prepare_finish_consistent hb hn (mem_defects.mp (Finset.mem_of_mem_erase hm))
    rw [Finset.symmDiff_singleton_eq (defects f) b.prepare.start, ite_eq_left hrm,
      Finset.symmDiff_singleton_eq, ite_eq_right he, Finset.card_insert_of_notMem he]
    exact Finset.card_erase_add_one hrm

/-- Source Lemma 41, arXiv:1602.03124v6, printed pp. 19–20: the actual returned cycle
is a Definition 39 blossom after the actual preparatory path is flipped. The alternative
proof transfers the later fork through chronological prefix flips, then uses Lemma 37
rerooting at a constraint LCA. No correctness premise is added to the raw extractor. -/
theorem Trace.blossom_correct (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F)
    {b : BlossomData F} (hb : m.blossomData = some b) :
    b.cycle.IsBlossom sem (b.prepare.flip f) := by
  have hw := h.blossom_cycle_isWalk hF hf hb
  have hm := blossom_metadata hb
  have hp := h.blossom_prepare_isWalk hb
  exact ⟨hw, h.blossom_cycle_closed hb, List.ne_nil_of_length_pos (hm.2.1.trans_le hm.2.2),
    h.blossom_base_inconsistent hF hb, hw.internallyConsistent_flip hF hp.1 f
      (blossom_prepare_finish hb) hp.2 (h.blossom_original_consistent hb),
    b.times, b.pivot, b.cycle.distinctCopies_of_nodup_times hm.1 (h.blossom_times_nodup hb),
    hm.2.1, hm.2.2, Subsingleton.elim (inferInstance : DecidableEq V) (Classical.decEq V) ▸
      h.blossom_isFDAG hF hf hM hb⟩

end Cslib.Logic.PL.CSP.Forest.Meeting

namespace Cslib.Logic.PL.CSP.Forest

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]

/-- Fresh-run blossom correctness, including source-strength cycle validity, validity of
the preparatory labeling, and preservation of its defect count. The only search premise
is the actual result equation; all forest and event invariants are derived from the run. -/
theorem search_blossom_correct (sem : Rel → List Bool → Bool)
    (f : OccurrenceLabeling F Bool) (hF : EdgeInstance F) (hf : ValidLabeling sem f)
    (hM : EdgeInstance.EvenConstraints sem F) {m : Meeting F}
    (hr : search sem f = .blossom m) :
    ∃ b, m.blossomData = some b ∧ b.cycle.IsBlossom sem (b.prepare.flip f) ∧
      ValidLabeling sem (b.prepare.flip f) ∧
      (defects (b.prepare.flip f)).card = (defects f).card := by
  have ht := search_trace sem f hF
  have he : (search sem f).Classified :=
    run_event_roots sem f (Forest.roots f) [] (incidenceList F)
  rw [hr] at ht he
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (m.blossomData_isSome he)
  exact ⟨b, hb, ht.blossom_correct hF hf hM hb, ht.blossom_prepare_valid hF hf hM hb,
    ht.blossom_prepare_card_defects hF hb⟩

end Cslib.Logic.PL.CSP.Forest
