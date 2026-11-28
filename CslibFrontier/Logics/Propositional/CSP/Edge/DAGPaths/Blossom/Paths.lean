/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Edge.DAGPaths.Blossom
public import CslibFrontier.Logics.Propositional.CSP.Edge.Walk.Subpath
import Mathlib.Data.Bool.Basic

/-!
# Actual ports and timestamps of blossom arms

The displayed arms of Definition 39 of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6,
printed p. 19, retain their actual original incidences and copied-step timestamps. The finite
clock lookup below reads the supplied arc list; no graph or labeling oracle is introduced.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel V : Type*} {F : CSP Rel V}

namespace Walk

/-- A source-strength blossom has an actual nonempty cycle. -/
theorem IsBlossom.steps_ne_nil {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {w : Walk F} (h : w.IsBlossom sem f) : w.steps ≠ [] :=
  h.2.2.1

/-- A nonempty linked trail uses an actual occurrence of its starting variable. -/
theorem IsWalk.start_mem_vars {w : Walk F} (hw : w.IsWalk) (hn : w.steps ≠ []) :
    w.start ∈ w.edges.map Occurrence.var := by
  cases he : w.steps with
  | nil => exact (hn he).elim
  | cons s ss =>
    exact List.mem_map.mpr ⟨s.1, by simp [edges, he, edgesOf], (he ▸ hw.1).1⟩

end Walk

namespace DAG

/-- Forgetting orientations and timestamps gives exactly the original incidence list. -/
theorem blossomArcs_map_occurrence (ss : List (Occurrence F × Occurrence F))
    (ts : List ℕ) (pivot : ℕ) (hl : ts.length = ss.length) :
    (blossomArcs ss ts pivot).map Arc.occurrence = Walk.edgesOf ss := by
  fun_induction blossomArcs ss ts pivot with
  | case1 => simp [Walk.edgesOf] -- no steps
  -- steps but no timestamps
  | case2 ss _ hss => exact absurd (List.eq_nil_of_length_eq_zero (by simpa using hl.symm)) hss
  | case3 input output ss t ts pivot ih => -- (input, output) :: ss, t :: ts
    simp only [List.map_cons, Walk.edgesOf_cons]
    rw [ih (by simpa using hl)]

/-- Both actual ports of a cycle step appear at its supplied timestamp and orientation. -/
theorem blossomArcs_get_mem {ss : List (Occurrence F × Occurrence F)} {ts : List ℕ}
    (hl : ts.length = ss.length) (pivot j : ℕ) (hj : j < ss.length) :
    let (input, output) := ss[j]
    let stamp := ts[j]'(by omega)
    (⟨input, stamp, decide (j < pivot)⟩ : Arc F) ∈ blossomArcs ss ts pivot ∧
      (⟨output, stamp, decide (pivot ≤ j + 1)⟩ : Arc F) ∈ blossomArcs ss ts pivot := by
  fun_induction blossomArcs ss ts pivot generalizing j with
  | case1 => simp at hj -- no steps
  -- steps but no timestamps
  | case2 ss _ hss => exact absurd (List.eq_nil_of_length_eq_zero (by simpa using hl.symm)) hss
  | case3 input output ss t ts pivot ih => -- (input, output) :: ss, t :: ts
    cases j with
    | zero => simp
    | succ j =>
      simpa only [List.get_eq_getElem, List.getElem_cons_succ, Nat.succ_eq_add_one,
        Nat.lt_sub_iff_add_lt, Nat.sub_le_iff_le_add] using
        (ih (by simpa using hl) j (by simpa using hj)).imp
          (fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
          (fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))

/-- Every actual blossom arc is one of the two supplied ports of a particular cycle step. -/
theorem blossomArcs_mem {ss : List (Occurrence F × Occurrence F)} {ts : List ℕ}
    (hl : ts.length = ss.length) {pivot : ℕ} {a : Arc F} (ha : a ∈ blossomArcs ss ts pivot) :
    ∃ j, ∃ hj : j < ss.length,
      let (input, output) := ss[j]
      let stamp := ts[j]'(by omega)
      a = ⟨input, stamp, decide (j < pivot)⟩ ∨
        a = ⟨output, stamp, decide (pivot ≤ j + 1)⟩ := by
  fun_induction blossomArcs ss ts pivot with
  | case3 input output ss t ts pivot ih => -- (input, output) :: ss, t :: ts
    simp only [List.mem_cons] at ha
    rcases ha with rfl | rfl | ha
    · exact ⟨0, by simp, Or.inl rfl⟩
    · exact ⟨0, by simp, Or.inr rfl⟩
    · obtain ⟨j, hj, he⟩ := ih (by simpa using hl) ha
      exact ⟨j + 1, by simpa using Nat.succ_lt_succ hj, by simpa only [List.getElem_cons_succ,
        Nat.succ_eq_add_one, Nat.lt_sub_iff_add_lt, Nat.sub_le_iff_le_add] using he⟩
  | _ => simp at ha -- no steps or no timestamps

/-- A finite lookup of the timestamp at an actual blossom incidence. -/
@[expose] def blossomTime (w : Walk F) (times : List ℕ) (pivot : ℕ)
    (o : Occurrence F) : ℕ :=
  (((blossomArcs w.steps times pivot).find? fun a => a.occurrence == o).map Arc.time).getD 0

/-- Incidence uniqueness makes the finite lookup agree with every actual certified arc. -/
theorem blossomTime_eq [DecidableEq V] {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {w : Walk F} {times : List ℕ} {pivot : ℕ}
    (h : (blossomDAG w times pivot).IsFDAG sem f) {a : Arc F}
    (ha : a ∈ blossomArcs w.steps times pivot) :
    blossomTime w times pivot a.occurrence = a.time := by
  cases he : (blossomArcs w.steps times pivot).find? (fun b => b.occurrence == a.occurrence) with
  | none =>
    exact (List.find?_eq_none.mp he a ha (by simp)).elim
  | some b =>
    obtain rfl := h.unique b (List.mem_toFinset.mpr (List.mem_of_find?_eq_some he)) a
      (List.mem_toFinset.mpr ha) (by simpa using List.find?_some he)
    simp [blossomTime, he]

end DAG

namespace Walk

/-- The copied-step list retains the exact original constraint and supplied timestamp. -/
theorem getElem_copies (w : Walk F) {ts : List ℕ} (hl : ts.length = w.steps.length)
    (j : ℕ) (hj : j < w.steps.length) :
    let (input, _) := w.steps[j]
    (w.copies ts)[j]'(by simp [copies, hl, hj]) =
      (input.1, ts[j]'(by omega)) := by
  simp [copies, List.getElem_zip]

/-- Equal copied nodes identify the actual cycle step, including repeated original constraints. -/
theorem DistinctCopies.index_eq {w : Walk F} {ts : List ℕ} (h : w.DistinctCopies ts)
    {i j : ℕ} (hi : i < w.steps.length) (hj : j < w.steps.length)
    (he : let (firstInput, _) := w.steps[i]
      let (secondInput, _) := w.steps[j]
      (firstInput.1, ts[i]'(by have := h.1; omega)) =
        (secondInput.1, ts[j]'(by have := h.1; omega))) : i = j := by
  apply (h.2.getElem_inj_iff (hi := by simp [copies, h.1, hi])
    (hj := by simp [copies, h.1, hj])).mp
  simpa only [getElem_copies w h.1 i hi, getElem_copies w h.1 j hj] using he

end Walk

namespace DAG

open Finset

/-- At a specified copied cycle step there are exactly its two original incidences. -/
theorem blossomArcs_copy {w : Walk F} {ts : List ℕ} {pivot : ℕ}
    (hw : w.IsWalk) (hd : w.DistinctCopies ts) {j : ℕ} (hj : j < w.steps.length)
    {e : Arc F} (he : e ∈ blossomArcs w.steps ts pivot)
    (hc : let (input, _) := w.steps[j]
      e.copy = (input.1, ts[j]'(by have := hd.1; omega))) :
    e = ⟨w.steps[j].1, ts[j]'(by have := hd.1; omega), decide (j < pivot)⟩ ∨
      e = ⟨w.steps[j].2, ts[j]'(by have := hd.1; omega), decide (pivot ≤ j + 1)⟩ := by
  obtain ⟨k, hk, he⟩ := blossomArcs_mem hd.1 he
  have hl : w.steps[k].1.1 = w.steps[k].2.1 := linked_constraint hw.1 (List.getElem_mem hk)
  obtain rfl : k = j := hd.index_eq hk hj (by
    rcases he with rfl | rfl
    · exact hc
    · simpa only [Arc.copy, List.get_eq_getElem, ← hl] using hc)
  exact he

/-- Distinct copied steps give the two-arc hypothesis needed by Corollary 36 and Lemma 40.
The terminal meeting contributes two incoming arcs at its own single copy. -/
theorem blossomDAG_pairedCopies [DecidableEq V] {w : Walk F} {ts : List ℕ} {pivot : ℕ}
    (hw : w.IsWalk) (hd : w.DistinctCopies ts) :
    (blossomDAG w ts pivot).PairedCopies := by
  intro c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
  obtain ⟨j, hj, heq⟩ := blossomArcs_mem hd.1 he
  let a : Arc F := ⟨w.steps[j].1, ts[j]'(by have := hd.1; omega), decide (j < pivot)⟩
  let b : Arc F := ⟨w.steps[j].2, ts[j]'(by have := hd.1; omega), decide (pivot ≤ j + 1)⟩
  have hm := blossomArcs_get_mem hd.1 pivot j hj
  have ha : a ∈ (blossomDAG w ts pivot).arcs := List.mem_toFinset.mpr hm.1
  have hb : b ∈ (blossomDAG w ts pivot).arcs := List.mem_toFinset.mpr hm.2
  have habc : a.copy = b.copy := Prod.ext (linked_constraint hw.1 (List.getElem_mem hj)) rfl
  have hec : e.copy = a.copy := heq.elim (fun h => h ▸ rfl) fun h => h ▸ habc.symm
  have hab : a ≠ b := fun hh =>
    (List.nodup_cons.mp (hw.2.sublist ((List.singleton_sublist.mpr (List.getElem_mem hj)).flatMap
      (fun s : Occurrence F × Occurrence F => [s.1, s.2])))).1
      (List.mem_singleton.mpr (congrArg Arc.occurrence hh))
  have hp (d : Arc F) (hd0 : d ∈ (blossomDAG w ts pivot).arcs) (hdc : d.copy = e.copy) :
      d = a ∨ d = b :=
    blossomArcs_copy hw hd hj (List.mem_toFinset.mp hd0) (hdc.trans hec)
  by_cases hjp : j < pivot
  · exact ⟨a, ha, b, hb, by simp [a, hjp], hec.symm, habc.symm.trans hec.symm, hab, hp⟩
  · exact ⟨b, hb, a, ha, by simp [b]; omega, habc.symm.trans hec.symm, hec.symm, hab.symm,
      fun d hd0 hdc => (hp d hd0 hdc).symm⟩

end DAG

namespace Walk

/-- Taking whole steps takes exactly the corresponding prefix of copied nodes. -/
theorem copies_take (w : Walk F) (ts : List ℕ) (n : ℕ) :
    (w.take n).copies (ts.take n) = (w.copies ts).take n := by
  simp only [copies, take, List.map_zip_eq_zipWith, List.take_zipWith]

/-- Suffixes retain exactly the supplied suffix of copied nodes. -/
theorem copies_drop (w : Walk F) (ts : List ℕ) (n : ℕ) :
    (w.drop n).copies (ts.drop n) = (w.copies ts).drop n := by
  simp only [copies, drop, List.map_zip_eq_zipWith, List.drop_zipWith]

/-- Copied-node distinctness is inherited by every variable-ended prefix. -/
theorem DistinctCopies.take {w : Walk F} {ts : List ℕ} (h : w.DistinctCopies ts) (n : ℕ) :
    (w.take n).DistinctCopies (ts.take n) :=
  ⟨by simp [Walk.take, h.1], copies_take w ts n ▸ (List.take_sublist n _).nodup h.2⟩

/-- Copied-node distinctness is inherited by every variable-ended suffix. -/
theorem DistinctCopies.drop {w : Walk F} {ts : List ℕ} (h : w.DistinctCopies ts) (n : ℕ) :
    (w.drop n).DistinctCopies (ts.drop n) :=
  ⟨by simp [Walk.drop, h.1], copies_drop w ts n ▸ (List.drop_sublist n _).nodup h.2⟩

end Walk

namespace DAG

/-- Prefixes retain their actual arc orientations, including a terminal two-input meeting. -/
theorem blossomArcs_take_subset (ss : List (Occurrence F × Occurrence F))
    (ts : List ℕ) (pivot n : ℕ) :
    ∀ a ∈ blossomArcs (ss.take n) (ts.take n) pivot, a ∈ blossomArcs ss ts pivot := by
  induction ss generalizing ts pivot n with
  | nil => simp [blossomArcs]
  | cons s ss ih =>
    cases ts with
    | nil => cases n <;> simp [blossomArcs]
    | cons t ts =>
      cases n with
      | zero => simp [blossomArcs]
      | succ n =>
        intro a ha
        simp only [List.take_succ_cons, blossomArcs, List.mem_cons] at ha ⊢
        exact ha.imp id (Or.imp id (ih ts (pivot - 1) n a))

/-- Dropping whole steps retains actual arcs, with the meeting index shifted by their count. -/
theorem blossomArcs_drop_subset (ss : List (Occurrence F × Occurrence F))
    (ts : List ℕ) (pivot n : ℕ) :
    ∀ a ∈ blossomArcs (ss.drop n) (ts.drop n) (pivot - n),
      a ∈ blossomArcs ss ts pivot := by
  induction ss generalizing ts pivot n with
  | nil => simp [blossomArcs]
  | cons s ss ih =>
    cases n with
    | zero => simp
    | succ n =>
      cases ts with
      | nil =>
        cases (s :: ss).drop (n + 1) <;> simp [blossomArcs]
      | cons t ts =>
        intro a ha
        have he : pivot - (n + 1) = pivot - 1 - n := by omega
        simp only [List.drop_succ_cons, he] at ha
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih ts (pivot - 1) n a ha))

/-- A blossom graph's copied nodes are exactly the supplied copied steps. -/
theorem blossomDAG_copies [DecidableEq V] {w : Walk F} {ts : List ℕ} (hw : w.IsWalk)
    (hl : ts.length = w.steps.length) (pivot : ℕ) :
    (blossomDAG w ts pivot).copies = (w.copies ts).toFinset := by
  ext c
  simp only [blossomDAG, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨j, hj, he⟩ := blossomArcs_mem hl ha
    refine List.mem_iff_getElem.mpr ⟨j, by simp [Walk.copies, hl, hj], ?_⟩
    rw [Walk.getElem_copies w hl j hj]
    have hs := linked_constraint hw.1 (List.getElem_mem hj)
    change w.steps[j].1.1 = w.steps[j].2.1 at hs
    rcases he with rfl | rfl
    · rfl
    · exact congrArg (fun i : Fin F.length => (i, ts[j]'(by omega))) hs
  · intro hc
    obtain ⟨j, hjc, he⟩ := List.mem_iff_getElem.mp hc
    have hj : j < w.steps.length := by simpa [Walk.copies, hl] using hjc
    exact ⟨⟨w.steps[j].1, ts[j]'(by omega), decide (j < pivot)⟩,
      (blossomArcs_get_mem hl pivot j hj).1, (Walk.getElem_copies w hl j hj).symm.trans he⟩

/-- The boundary step's copy is absent from every preceding whole step. -/
theorem blossomDAG_copy_not_take [DecidableEq V] {w : Walk F} {ts : List ℕ}
    (hw : w.IsWalk) (hd : w.DistinctCopies ts) (pivot j : ℕ) (hj : j < w.steps.length) :
    let (input, _) := w.steps[j]
    (input.1, ts[j]'(by have := hd.1; omega)) ∉
      (blossomDAG (w.take j) (ts.take j) pivot).copies := by
  dsimp only
  rw [blossomDAG_copies (hw.take j) (hd.take j).1, Walk.copies_take, List.mem_toFinset,
    List.mem_iff_getElem]
  rintro ⟨k, hk, he⟩
  simp only [List.length_take] at hk
  have hjl : j < (w.copies ts).length := by simp [Walk.copies, hd.1, hj]
  have heq : k = j := (hd.2.getElem_inj_iff (hi := by omega) (hj := hjl)).mp
    (by simpa only [List.getElem_take, Walk.getElem_copies w hd.1 j hj] using he)
  omega

/-- The boundary step's copy is absent from every following whole step. -/
theorem blossomDAG_copy_not_drop [DecidableEq V] {w : Walk F} {ts : List ℕ}
    (hw : w.IsWalk) (hd : w.DistinctCopies ts) (pivot j : ℕ) (hj : j < w.steps.length) :
    let (input, _) := w.steps[j]
    (input.1, ts[j]'(by have := hd.1; omega)) ∉
      (blossomDAG (w.drop (j + 1)) (ts.drop (j + 1)) pivot).copies := by
  dsimp only
  rw [blossomDAG_copies (hw.drop (j + 1)) (hd.drop (j + 1)).1, Walk.copies_drop,
    List.mem_toFinset, List.mem_iff_getElem]
  rintro ⟨k, hk, he⟩
  simp only [List.length_drop] at hk
  have hjl : j < (w.copies ts).length := by simp [Walk.copies, hd.1, hj]
  have heq : j + 1 + k = j := (hd.2.getElem_inj_iff (hi := by omega) (hj := hjl)).mp
    (by simpa only [List.getElem_drop, Walk.getElem_copies w hd.1 j hj] using he)
  omega

/-- The support of the displayed blossom is exactly its base and actual used variables. -/
theorem blossomDAG_vars [DecidableEq V] (w : Walk F) (ts : List ℕ) (pivot : ℕ)
    (hl : ts.length = w.steps.length) :
    (blossomDAG w ts pivot).vars = insert w.start (w.edges.map Occurrence.var).toFinset := by
  dsimp only [blossomDAG, Walk.edges]
  rw [← blossomArcs_map_occurrence w.steps ts pivot hl, List.map_map]
  rfl

/-- Each variable-ended prefix is a supported subgraph with its actual copied steps. -/
theorem blossomDAG_take_subgraph [DecidableEq V] {w : Walk F} {ts : List ℕ} {pivot : ℕ}
    (hs : (blossomDAG w ts pivot).Supported) (n : ℕ) :
    (blossomDAG (w.take n) (ts.take n) pivot).Subgraph (blossomDAG w ts pivot) :=
  blossomDAG_subgraph_of_arcs _ _ _ (by simp [blossomDAG, Walk.take]) hs fun a ha =>
    List.mem_toFinset.mpr (blossomArcs_take_subset w.steps ts pivot n a ha)

/-- Each variable-ended suffix is a supported subgraph, with its meeting index shifted. -/
theorem blossomDAG_drop_subgraph [DecidableEq V] {w : Walk F} {ts : List ℕ} {pivot : ℕ}
    (hl : ts.length = w.steps.length) (hs : (blossomDAG w ts pivot).Supported) (n : ℕ) :
    (blossomDAG (w.drop n) (ts.drop n) (pivot - n)).Subgraph (blossomDAG w ts pivot) := by
  have hstart : (w.drop n).start ∈ (blossomDAG w ts pivot).vars := by
    rw [blossomDAG_vars w ts pivot hl]
    change (w.take n).finish ∈ _
    by_cases he : w.steps.take n = []
    · simp only [Walk.take, Walk.finish, Walk.finishFrom, he, Finset.mem_insert, true_or]
    · obtain ⟨s, hsm, heq⟩ := Walk.finish_step (w.take n) he
      exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map.mpr
        ⟨s.2, List.mem_flatMap.mpr ⟨s, List.mem_of_mem_take hsm, by simp⟩, heq⟩))
  exact blossomDAG_subgraph_of_arcs _ _ _ hstart hs (fun a ha =>
    List.mem_toFinset.mpr (blossomArcs_drop_subset w.steps ts pivot n a ha))

/-- Forgetting timestamps in a blossom graph gives exactly the original used incidences. -/
theorem blossomDAG_occurrences [DecidableEq V] (w : Walk F) (ts : List ℕ) (pivot : ℕ)
    (hl : ts.length = w.steps.length) :
    (blossomDAG w ts pivot).arcs.image Arc.occurrence = w.edges.toFinset := by
  ext o
  simp [blossomDAG, Walk.edges, ← blossomArcs_map_occurrence w.steps ts pivot hl]

/-- Forgetting timestamps in a blossom graph gives the actual incidence flip. -/
theorem blossomDAG_flip [DecidableEq V] (w : Walk F) (ts : List ℕ) (pivot : ℕ)
    (hl : ts.length = w.steps.length) (f : OccurrenceLabeling F Bool) :
    (blossomDAG w ts pivot).flip f = w.flip f :=
  congrArg (fun es => BitString.flipOn es f) (blossomDAG_occurrences w ts pivot hl)

/-- Lemma 40 for all variable-ended prefixes, derived from the full six-invariant DAG and
distinct actual copied steps. Repeated original constraints and odd local parity are allowed. -/
theorem blossomDAG_valid_take [DecidableEq V] {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {w : Walk F} {ts : List ℕ} {pivot : ℕ}
    (h : (blossomDAG w ts pivot).IsFDAG sem f) (hw : w.IsWalk)
    (hd : w.DistinctCopies ts) (hM : EdgeInstance.EvenConstraints sem F) (n : ℕ) :
    ValidLabeling sem ((w.take n).flip f) := by
  have hh := h.subgraph (blossomDAG_take_subgraph h.supported n) (blossomDAG_supported _ _ _)
  rw [← blossomDAG_flip _ _ pivot (hd.take n).1 f]
  exact hh.valid_flip_of_pairedCopies hM (blossomDAG_pairedCopies (hw.take n) (hd.take n))

end DAG

end Cslib.Logic.PL.CSP
