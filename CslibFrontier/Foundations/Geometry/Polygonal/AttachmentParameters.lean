/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Join
public import CslibFrontier.Foundations.Geometry.Polygonal.Segment
import Mathlib.Tactic.Ring

/-!
# Parameters of routes with attached end segments

Every actual segment parameter is either an unchanged old parameter or a parameter of
an attached end segment. The global position is recorded exactly, so contact proofs can
recover the original route ends after one or both attachments. Finite append words retain
every old segment and specify every added segment by its exact list position.

## Main results

* `Cslib.Polygonal.Route.segments_foldl_append`: the exact number of segments after a word.
* `Cslib.Polygonal.Route.foldl_append_eval_cases`: all-real evaluation and chain-position
  classification of every actual segment after a finite append word.
* `Cslib.Polygonal.Route.eval_foldl_append_line`: actual adjacent-node evaluation after a line.
-/

public section

namespace Cslib.Polygonal.Route

/-- Every parameter of a prepended route is an old parameter shifted by one, or a
parameter of the new initial segment. The statement holds for every real parameter. -/
theorem prepend_eval_cases (a : ℂ) (p : Route) (i : Fin (Route.prepend a p).segments) (t : ℝ) :
    (∃ j : Fin p.segments, (Route.prepend a p).eval i t = p.eval j t ∧
      (Route.prepend a p).position i t = 1 + p.position j t) ∨
    ((Route.prepend a p).eval i t = AffineMap.lineMap a p.start t ∧
      (Route.prepend a p).position i t = t) := by
  induction i using Fin.cases with
  | zero => exact Or.inr ⟨eval_prepend_zero a p t, by simp [position]⟩
  | succ j =>
    change Fin p.segments at j
    exact Or.inl ⟨j, eval_prepend_succ a p j t, position_prepend_succ a p j t⟩

/-- Every parameter of an appended route is an unchanged old parameter or a parameter
of its new final segment, with its exact global position. -/
theorem append_eval_cases (p : Route) (b : ℂ) (i : Fin (p.append b).segments) (t : ℝ) :
    (∃ j : Fin p.segments, (p.append b).eval i t = p.eval j t ∧
      (p.append b).position i t = p.position j t) ∨
    ((p.append b).eval i t = AffineMap.lineMap p.finish b t ∧
      (p.append b).position i t = (p.segments : ℝ) + t) := by
  induction i using Fin.lastCases with
  | last => exact Or.inr ⟨eval_append_last p b t, rfl⟩
  | cast j =>
    change Fin p.segments at j
    exact Or.inl ⟨j, eval_append_castSucc p b j t, position_append_castSucc p b j t⟩

/-- Attaching both ends retains every old parameter and distinguishes both new
segments, even when the new route is closed. -/
theorem attach_eval_cases (a : ℂ) (p : Route) (b : ℂ)
    (i : Fin ((Route.prepend a p).append b).segments) (t : ℝ) :
    (∃ j : Fin p.segments, ((Route.prepend a p).append b).eval i t = p.eval j t ∧
      ((Route.prepend a p).append b).position i t = 1 + p.position j t) ∨
    (((Route.prepend a p).append b).eval i t = AffineMap.lineMap a p.start t ∧
      ((Route.prepend a p).append b).position i t = t) ∨
    (((Route.prepend a p).append b).eval i t = AffineMap.lineMap p.finish b t ∧
      ((Route.prepend a p).append b).position i t = (p.segments : ℝ) + 1 + t) := by
  rcases append_eval_cases (Route.prepend a p) b i t with ⟨j, heval, hpos⟩ | ⟨heval, hpos⟩
  · rcases prepend_eval_cases a p j t with ⟨k, heval', hpos'⟩ | ⟨heval', hpos'⟩
    · exact Or.inl ⟨k, heval.trans heval', hpos.trans hpos'⟩
    · exact Or.inr (Or.inl ⟨heval.trans heval', hpos.trans hpos'⟩)
  · right
    right
    have hfinish : (Route.prepend a p).finish = p.finish := endpoint_prepend a p true
    refine ⟨heval.trans (congrArg (fun x => AffineMap.lineMap x b t) hfinish), ?_⟩
    simpa only [segments_prepend, Nat.cast_add, Nat.cast_one] using hpos

/-- Each appended node contributes exactly one actual segment. -/
theorem segments_foldl_append (p : Route) (nodes : List ℂ) :
    (nodes.foldl Route.append p).segments = p.segments + nodes.length := by
  induction nodes generalizing p with
  | nil => simp
  | cons a nodes ih =>
    simp only [List.foldl_cons, ih, segments_append, List.length_cons]
    omega

private theorem index_of_position (p : Route) (i : Fin p.segments) (t : ℝ) (n : ℕ)
    (h : p.position i t = (n : ℝ) + t) : i.val = n := by
  change (i.val : ℝ) + t = (n : ℝ) + t at h
  exact_mod_cast add_right_cancel h

/-- Every final segment is either an unchanged old segment or the specified consecutive
node pair of the append word. Indices, evaluations and positions are exact for ALL real times. -/
theorem foldl_append_eval_cases (p : Route) (nodes : List ℂ)
    (i : Fin (nodes.foldl Route.append p).segments) (t : ℝ) :
    (∃ j : Fin p.segments, i.val = j.val ∧
      (nodes.foldl Route.append p).eval i t = p.eval j t ∧
      (nodes.foldl Route.append p).position i t = p.position j t) ∨
    (∃ q : Fin nodes.length, i.val = p.segments + q.val ∧
      (nodes.foldl Route.append p).eval i t =
        AffineMap.lineMap ((p.finish :: nodes)[q.castSucc]) (nodes[q]) t ∧
      (nodes.foldl Route.append p).position i t = (p.segments : ℝ) + q.val + t) := by
  induction nodes generalizing p with
  | nil => exact Or.inl ⟨i, rfl, rfl, rfl⟩
  | cons a nodes ih =>
    rcases ih (p.append a) i with ⟨j, _, heval, hpos⟩ | ⟨q, _, heval, hpos⟩
    · rcases append_eval_cases p a j t with ⟨k, hkval, hkpos⟩ | ⟨hkval, hkpos⟩
      · have hpos' := hpos.trans hkpos
        exact Or.inl ⟨k, index_of_position _ i t k.val hpos', heval.trans hkval, hpos'⟩
      · have hpos' : ((a :: nodes).foldl Route.append p).position i t =
            (p.segments : ℝ) + t := hpos.trans hkpos
        refine Or.inr ⟨0, ?_, ?_, ?_⟩
        · simpa only [Fin.val_zero, Nat.add_zero] using index_of_position _ i t p.segments hpos'
        · simpa only [List.foldl_cons, List.getElem_cons_zero, Fin.getElem_fin, Fin.val_zero,
            Fin.val_castSucc] using heval.trans hkval
        · simpa using hpos'
    · have hpos' : ((a :: nodes).foldl Route.append p).position i t =
          (p.segments : ℝ) + (q.val + 1 : ℕ) + t := by
        calc
          _ = ((p.append a).segments : ℝ) + q.val + t := hpos
          _ = _ := by simp only [segments_append, Nat.cast_add, Nat.cast_one]; ring
      refine Or.inr ⟨q.succ, ?_, ?_, ?_⟩
      · have hindex := index_of_position _ i t (p.segments + (q.val + 1)) (by
          simpa only [Nat.cast_add] using hpos')
        simpa only [Fin.val_succ] using hindex
      · have hfinish : (p.append a).finish = a := endpoint_append p a true
        simpa only [List.foldl_cons, hfinish, Fin.getElem_fin, Fin.val_castSucc, Fin.val_succ,
          List.getElem_cons_succ] using heval
      · simpa only [Fin.val_succ] using hpos'

/-- All-real evaluation of a line followed by an append word at its actual adjacent nodes. -/
theorem eval_foldl_append_line (a b : ℂ) (nodes : List ℂ)
    (i : Fin (nodes.foldl Route.append (Route.line a b)).segments) (t : ℝ) :
    (nodes.foldl Route.append (Route.line a b)).eval i t =
      AffineMap.lineMap ((a :: b :: nodes)[i.val]'(by
        have hi := i.isLt
        simp only [Route.segments_foldl_append] at hi
        change i.val < 1 + nodes.length at hi
        simp only [List.length_cons]
        omega))
        ((a :: b :: nodes)[i.val + 1]'(by
          have hi := i.isLt
          simp only [Route.segments_foldl_append] at hi
          change i.val < 1 + nodes.length at hi
          simp only [List.length_cons]
          omega)) t := by
  rcases Route.foldl_append_eval_cases (Route.line a b) nodes i t with
    ⟨j, hij, heval, _⟩ | ⟨q, hiq, heval, _⟩
  · have hj : j = 0 := by
        apply Fin.ext
        change j.val = 0
        have h := j.isLt
        change j.val < 1 at h
        omega
    subst j
    simpa only [hij, Fin.val_zero, Nat.zero_add, List.getElem_cons_zero,
      List.getElem_cons_succ, Route.eval_line] using heval
  · change i.val = 1 + q.val at hiq
    simpa only [hiq, Nat.add_comm 1 q.val, Nat.add_assoc,
      Fin.getElem_fin, Fin.val_castSucc, List.getElem_cons_succ,
      Route.finish_line] using heval

end Cslib.Polygonal.Route
