/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Growth

/-!
# Invariants of completed chronological forest expansions

Derivations from actual local growth certificates of Algorithm 1,
[KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed pp. 10 and 16.
Saturation is essential: pairwise feasible graph adjacency alone is insufficient for the
prefix-dependent walk semantics. Original-constraint revisits are retained throughout.

## Main results

* `search_completed_isFDAG`: all six DAG invariants for completed expansions of a fresh run.
-/

public section

namespace Cslib.Logic.PL.CSP.Forest

open DAG

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]

namespace Log

omit [DecidableEq V] in
/-- Recording arcs and then forgetting orientations and timestamps recovers all used ports,
including the input port of an expansion with no children. -/
theorem map_arcs_occurrence (es : Log F) : es.arcs.map Arc.occurrence = es.used := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [arcs, used, List.map_map, Function.comp_def, ih]

omit [DecidableEq V] in
/-- Outgoing arcs are exactly the recorded discovery ports, preserving multiplicity. -/
theorem map_outgoing_arcs (es : Log F) :
    ((es.arcs.filter fun a => !a.incoming).map fun a => a.occurrence.var) = es.children := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp [arcs, children, List.filter_append, List.filter_map, Function.comp_def, ih]

omit [DecidableEq V] in
/-- Every output port has its actual outgoing stamped arc in the recorded graph. -/
theorem outgoing_arc {es : Log F} {b : Occurrence F} (hb : b ∈ es.outgoing) :
    ∃ c ∈ es.arcs, c.occurrence = b ∧ c.incoming = false := by
  induction es with
  | nil => simp [outgoing] at hb
  | cons d ds ih =>
    rcases List.mem_append.mp hb with hb | hb
    · exact ⟨⟨b, ds.length, false⟩, List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_map.mpr ⟨b, hb, rfl⟩)), rfl, rfl⟩
    · obtain ⟨c, hc, he, hi⟩ := ih hb
      exact ⟨c, List.mem_cons_of_mem _ (List.mem_append_right _ hc), he, hi⟩

end Log

namespace Log

/-- Rank of a variable: roots have rank zero; a newly discovered child at time `t` has rank
`2*t+2`. This finite chronological numbering never compares variable names. -/
@[expose] def birth : Log F → V → ℕ
  | [], _ => 0
  | e :: es, v => if v ∈ e.outputs.map Occurrence.var then 2 * es.length + 2 else birth es v

/-- Every variable rank is at most twice the number of completed expansions. -/
theorem birth_le (es : Log F) (v : V) : es.birth v ≤ 2 * es.length := by
  induction es with
  | nil => exact Nat.le_refl _
  | cons e es ih => by_cases h : v ∈ e.outputs.map Occurrence.var <;> simp [birth, h] <;> omega

end Log

namespace Grown

variable {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool}
  {rs : List V} {es : Log F}

/-- No positional incidence is ever reused by a completed chronological forest. -/
theorem used_nodup (hg : Grown sem f rs es) : es.used.Nodup := by
  induction hg with
  | nil => simp [Log.used]
  | @cons es e hp hv hu hf hn _ _ ih =>
    rw [Log.used, List.nodup_cons, List.nodup_append]
    refine ⟨fun h => ?_, hn.of_map Occurrence.var, ih, fun a ha b hb he =>
      hf a ha (he.symm ▸ Log.Grown.used_visited hp hb)⟩
    exact (List.mem_append.mp h).elim (fun ho => hf e.input ho hv) hu

/-- A variable is discovered at most once, even across different copies of a constraint. -/
theorem children_nodup (hg : Grown sem f rs es) : es.children.Nodup := by
  induction hg with
  | nil => simp [Log.children]
  | @cons es e hp hv hu hf hn _ _ ih =>
    rw [Log.children, List.nodup_append]
    refine ⟨hn, ih, fun v hv _ hw he => ?_⟩
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hv
    exact hf o ho (Or.inr (he.symm ▸ hw))

/-- Incidence uniqueness, including orientation and timestamp, follows from the executable
port-accounting invariant rather than an assumed graph property. -/
theorem unique (hg : Grown sem f rs es) {a b : Arc F}
    (ha : a ∈ es.arcs) (hb : b ∈ es.arcs) (he : a.occurrence = b.occurrence) : a = b :=
  List.inj_on_of_nodup_map (Log.map_arcs_occurrence es ▸ hg.used_nodup) ha hb he

/-- Every variable has at most one incoming incidence arc (copy-to-variable orientation). -/
theorem indegree (hg : Grown sem f rs es) {a b : Arc F}
    (ha : a ∈ es.arcs) (hb : b ∈ es.arcs)
    (hai : a.incoming = false) (hbi : b.incoming = false)
    (he : a.occurrence.var = b.occurrence.var) : a = b :=
  List.inj_on_of_nodup_map (Log.map_outgoing_arcs es ▸ hg.children_nodup)
    (List.mem_filter.mpr ⟨ha, by simp [hai]⟩)
    (List.mem_filter.mpr ⟨hb, by simp [hbi]⟩) he

/-- A complete scan supplies an outgoing witness for each feasible partner of an incoming
arc. Its timestamp is no later than that incoming arc's timestamp. -/
theorem saturated (hg : Grown sem f rs es) {a : Arc F}
    (ha : a ∈ es.arcs) (hai : a.incoming = true) {b : Occurrence F}
    (hpartner : b ∈ partners sem f a.occurrence) :
    ∃ c ∈ es.arcs, c.occurrence = b ∧ c.incoming = false ∧ c.time ≤ a.time := by
  induction hg with
  | nil => simp [Log.arcs] at ha
  | @cons es e hp hv hu hf hn hfe hs ih =>
    simp only [Log.arcs, List.mem_cons, List.mem_append, List.mem_map] at ha
    rcases ha with rfl | ⟨o, ho, rfl⟩ | ha
    · rcases List.mem_append.mp (hs b hpartner) with hb | hb
      · refine ⟨⟨b, es.length, false⟩, ?_, rfl, rfl, Nat.le_refl _⟩
        exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨b, hb, rfl⟩))
      · obtain ⟨c, hc, he, hi⟩ := Log.outgoing_arc hb
        exact ⟨c, List.mem_cons_of_mem _ (List.mem_append_right _ hc), he, hi,
          Nat.le_of_lt (es.mem_arcs hc).2⟩
    · cases hai
    · obtain ⟨c, hc, he, hi, ht⟩ := ih ha
      exact ⟨c, List.mem_cons_of_mem _ (List.mem_append_right _ hc), he, hi, ht⟩

/-- Completed scans rule out every shortcut from an old incoming port to a later used port,
including later incoming ports. This is condition 6 of Definition 32. -/
theorem noShortcut (hg : Grown sem f rs es) (hF : EdgeInstance F)
    {a b : Arc F} (ha : a ∈ es.arcs) (hb : b ∈ es.arcs) (hai : a.incoming = true)
    (hc : a.occurrence.1 = b.occurrence.1) (ht : a.time < b.time) :
    ¬ ValidLabeling sem (pairFlip f a.occurrence b.occurrence) := fun hvalid => by
  by_cases hv : a.occurrence.var = b.occurrence.var
  · exact ht.ne (congrArg Arc.time (hg.unique ha hb (hF.eq_of_constraint_eq hv hc)))
  · obtain ⟨c, hcm, hco, -, hct⟩ :=
      hg.saturated ha hai ((mem_partners sem f a.occurrence b.occurrence).mpr ⟨hc, hv, hvalid⟩)
    exact (ht.trans_le (congrArg Arc.time (hg.unique hcm hb hco) ▸ hct)).false

private theorem birth_old {e : Expansion F}
    (hf : ∀ o ∈ e.outputs, ¬ es.Visited rs o.var) {v : V}
    (hv : es.Visited rs v) : Log.birth (e :: es) v = es.birth v :=
  ite_eq_right fun hm => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hm
    exact hf o ho hv

/-- Every recorded directed arc increases its chronological node rank. -/
theorem rank_arc (hg : Grown sem f rs es) {a : Arc F} (ha : a ∈ es.arcs) :
    if a.incoming then es.birth a.occurrence.var < 2 * a.time + 1
    else 2 * a.time + 1 < es.birth a.occurrence.var := by
  induction hg with
  | nil => simp [Log.arcs] at ha
  | @cons es e hp hv hu hf _ _ _ ih =>
    simp only [Log.arcs, List.mem_cons, List.mem_append, List.mem_map] at ha
    rcases ha with rfl | ⟨o, ho, rfl⟩ | ha
    · have := es.birth_le e.input.var
      simp only [↓reduceIte, birth_old hf hv]; omega
    · simp only [Bool.false_eq_true, ↓reduceIte, Log.birth, List.mem_map.mpr ⟨o, ho, rfl⟩]; omega
    · exact birth_old hf (Log.Grown.used_visited hp (es.mem_arcs ha).1) ▸ ih ha

/-- Different original constraint positions cannot share a timestamp. -/
theorem copy_unique (hg : Grown sem f rs es) {a b : Arc F}
    (ha : a ∈ es.arcs) (hb : b ∈ es.arcs) (ht : a.time = b.time) : a.copy = b.copy := by
  induction hg with
  | nil => simp [Log.arcs] at ha
  | @cons es e hp hv hu hf hn hfe hs ih =>
    have hcase : ∀ c ∈ Log.arcs (e :: es),
        c ∈ es.arcs ∨ (c.time = es.length ∧ c.copy = (e.input.1, es.length)) := by
      intro c hc
      simp only [Log.arcs, List.mem_cons, List.mem_append, List.mem_map] at hc
      rcases hc with rfl | ⟨o, ho, rfl⟩ | hc
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, Prod.ext ((mem_partners sem f _ _).mp (hfe o ho)).1.symm rfl⟩
      · exact Or.inl hc
    rcases hcase a ha with ha | ⟨hat, hac⟩ <;>
      rcases hcase b hb with hb | ⟨hbt, hbc⟩
    · exact ih ha hb
    · exact absurd (es.mem_arcs ha).2 (by omega)
    · exact absurd (es.mem_arcs hb).2 (by omega)
    · exact hac.trans hbc.symm

/-- The source's timestamp-compatible topological order, witnessed by an explicit finite
rank. Equal ranks of unrelated roots are harmless and can be broken by the existing DAG API. -/
theorem ordered (hg : Grown sem f rs es) : (es.toDAG rs).Ordered := by
  refine ⟨?_, ⟨Sum.elim es.birth (fun c => 2 * c.2 + 1), ?_⟩⟩
  · intro c hc d hd ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
    exact hg.copy_unique ha hb ht
  · intro x y hxy
    rcases hxy with ⟨a, ha, rfl, rfl⟩ | ⟨c, hc, d, hd, ht, rfl, rfl⟩
    · have hr := hg.rank_arc (List.mem_toFinset.mp ha)
      cases hi : a.incoming <;> simpa [Arc.source, Arc.target, hi, Arc.copy] using hr
    · simp only [Sum.elim]; omega

/-- Feasibility at every copied constraint, with cancellation of equal input ports. -/
theorem feasible (hg : Grown sem f rs es) (hf : ValidLabeling sem f)
    {a b : Arc F} (ha : a ∈ es.arcs) (hb : b ∈ es.arcs)
    (hai : a.incoming = true) (hc : a.copy = b.copy) :
    ValidLabeling sem (pairFlip f a.occurrence b.occurrence) := by
  induction hg with
  | nil => simp [Log.arcs] at ha
  | @cons es e _ _ _ _ _ hfe _ ih =>
    have ht : a.time = b.time := congrArg Prod.snd hc
    simp only [Log.arcs, List.mem_cons, List.mem_append, List.mem_map] at ha hb
    rcases ha with rfl | ⟨o, ho, rfl⟩ | ha
    · rcases hb with rfl | ⟨o, ho, rfl⟩ | hb
      · simpa only [pairFlip_self] using hf
      · exact ((mem_partners sem f _ _).mp (hfe o ho)).2.2
      · exact absurd ht.symm (es.mem_arcs hb).2.ne
    · cases hai
    · rcases hb with rfl | ⟨_, _, rfl⟩ | hb
      · exact absurd ht (es.mem_arcs ha).2.ne
      · exact absurd ht (es.mem_arcs ha).2.ne
      · exact ih ha hb

/-- Lemma 34 for completed expansions, derived from chronological growth, including full
same-original-constraint no-shortcut and an explicit ordered-forest rank. -/
theorem isFDAG (hg : Grown sem f rs es) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) : (es.toDAG rs).IsFDAG sem f where
  valid := hf
  supported := es.toDAG_supported rs
  unique _a ha _b hb := hg.unique (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb)
  indegree _a ha _b hb := hg.indegree (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb)
  ordered := hg.ordered
  feasible _a ha _b hb := hg.feasible hf (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb)
  noShortcut _a ha _b hb := hg.noShortcut hF (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb)

end Grown

/-- Every completed forest appearing as a search result is an f-DAG, with no supplied
forest-correctness premise. The partially scanned terminal copy is treated separately. -/
theorem search_completed_isFDAG (sem : Rel → List Bool → Bool)
    (f : OccurrenceLabeling F Bool) (hF : EdgeInstance F) (hf : ValidLabeling sem f) :
    (search sem f).Logs (fun es => (es.toDAG (roots f)).IsFDAG sem f) := by
  have hg := search_grown sem f hF
  cases hr : search sem f <;> exact Grown.isFDAG (by rwa [hr] at hg) hF hf

end Cslib.Logic.PL.CSP.Forest
