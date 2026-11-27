/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Completeness
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.OutputLatch

/-!
# Closed QBF circuits and their fixed target configurations

Close the two outer controls of the QBF body with an output latch and a free try source.
The initial and target configurations have the same inactive body and differ in the output
latch's canonical memory. Execute the body, record its success, and undo the body execution to
reach that target [HearnDemaine2005, Theorem 5 and Corollary 6].

## Main definitions

* `Cslib.Complexity.NCL.QBF.Circuit.diagram`: the closed circuit.
* `Cslib.Complexity.NCL.QBF.Circuit.initial`, `Cslib.Complexity.NCL.QBF.Circuit.target`:
  explicit legal initial and target configurations, independent of formula truth.
* `Cslib.Complexity.NCL.QBF.Circuit.output`: the output latch's memory edge.

## Main results

* `Cslib.Complexity.NCL.QBF.Circuit.reachable_target_iff_truth`: the fixed target is reachable
  exactly when the quantified matrix is true.
* `Cslib.Complexity.NCL.QBF.Circuit.canReverse_initial_iff_truth`: configuration-to-edge
  correctness from the canonical initial configuration.
* `Cslib.Complexity.NCL.QBF.Circuit.exists_reachable_sat_iff_truth`: edge-to-edge correctness,
  from trying inactive to a satisfied body.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Circuit

open Diagram Gate

local notation "B" => Color.blue

/-- The quantifier chain and CNF terminal, closed by an output latch and a free try source. -/
@[expose] def diagram (qs : List Quantifier) (ms : List (List Bool)) : Diagram Gate [] [] :=
  OutputLatch.diagram.comp (Matrix.body qs ms)

/-- The inactive body with the given output record. Both record settings are legal for every
matrix; sat points down and try is inactive. -/
@[expose] def configuration (recorded : Bool) (qs : List Quantifier) (ms : List (List Bool)) :
    Realization Gate.interp (diagram qs ms) [] [] :=
  (OutputLatch.canonical recorded true false).comp (Initial.body qs ms)

/-- The explicit initial configuration, with a clear output record. -/
@[expose] def initial (qs : List Quantifier) (ms : List (List Bool)) :
    Realization Gate.interp (diagram qs ms) [] [] := configuration false qs ms

/-- The fixed target configuration: the inactive initial body with the output record set. -/
@[expose] def target (qs : List Quantifier) (ms : List (List Bool)) :
    Realization Gate.interp (diagram qs ms) [] [] := configuration true qs ms

/-- The QBF body as an occurrence in the closed circuit. -/
@[expose] def bodyOcc (qs : List Quantifier) (ms : List (List Bool)) :
    Occurrence (Matrix.body qs ms) (diagram qs ms) := .compRight _ .refl

/-- The output latch as an occurrence in the closed circuit. -/
@[expose] def latchOcc (qs : List Quantifier) (ms : List (List Bool)) :
    Occurrence latch (diagram qs ms) := .compLeft _ OutputLatch.latchOcc

/-- The memory edge of the output latch. -/
@[expose] def output (qs : List Quantifier) (ms : List (List Bool)) : (diagram qs ms).Edge :=
  (latchOcc qs ms).emb Latch.mem

/-- The body's outer try input. -/
@[expose] def tryIn (qs : List Quantifier) (ms : List (List Bool)) : (diagram qs ms).Edge :=
  (bodyOcc qs ms).emb (.inl 1)

/-- The satisfied output of the body, active when it points into the output latch. -/
@[expose] def satOut (qs : List Quantifier) (ms : List (List Bool)) : (diagram qs ms).Edge :=
  (bodyOcc qs ms).emb (.inl 0)

@[simp] theorem configuration_output (recorded : Bool) (qs : List Quantifier)
    (ms : List (List Bool)) : (configuration recorded qs ms).orient (output qs ms) = recorded := by
  exact (congrFun (Realization.comp_orient_compLeft (OutputLatch.canonical recorded true false)
    (Initial.body qs ms)) OutputLatch.mem).trans (OutputLatch.canonical_mem recorded true false)

@[simp] theorem configuration_tryIn (recorded : Bool) (qs : List Quantifier)
    (ms : List (List Bool)) : (configuration recorded qs ms).orient (tryIn qs ms) = false := by
  exact (congrFun (Realization.comp_orient_compRight (OutputLatch.canonical recorded true false)
    (Initial.body qs ms)) (.inl 1)).trans (by rw [Realization.orient_top]; rfl)

private theorem lock_body (qs : List Quantifier) (ms : List (List Bool)) :
    (latchOcc qs ms).emb Latch.lock = (bodyOcc qs ms).emb (.inl 0) := by
  change compLeft OutputLatch.diagram (Matrix.body qs ms) (OutputLatch.latchOcc.emb Latch.lock) = _
  rw [OutputLatch.latch_lock]
  rfl

private def extend (D : Diagram Gate [B, B] []) (recorded : Bool) (u : D.Edge → Bool) :
    (OutputLatch.diagram.comp D).Edge → Bool :=
  glueComp OutputLatch.diagram D (OutputLatch.canonical recorded (u (.inl 0)) (u (.inl 1))).orient u

private theorem control_agrees (D : Diagram Gate [B, B] []) (recorded : Bool)
    (u : D.Edge → Bool) (j : Fin 2) : u (.inl j) =
      (OutputLatch.canonical recorded (u (.inl 0)) (u (.inl 1))).orient
        (OutputLatch.diagram.bottom j) := by
  have htop : D.topList u = [u (.inl 0), u (.inl 1)] := by simp [topList, List.ofFn_succ]
  exact congrFun (List.ofFn_inj.1 (htop.trans
    (OutputLatch.canonical recorded (u (.inl 0)) (u (.inl 1))).bot_eq.symm)) j

private theorem legal_extend (D : Diagram Gate [B, B] []) (recorded : Bool)
    {u : D.Edge → Bool} (hu : (D.graph Gate.interp).Legal u) :
    ((OutputLatch.diagram.comp D).graph Gate.interp).Legal (extend D recorded u) :=
  legal_glueComp (OutputLatch.canonical recorded (u (.inl 0)) (u (.inl 1))).legal hu
    (control_agrees D recorded u)

private theorem extend_compRight (D : Diagram Gate [B, B] []) (recorded : Bool)
    (u : D.Edge → Bool) : extend D recorded u ∘ compRight OutputLatch.diagram D = u :=
  funext fun e => glueComp_compRight OutputLatch.diagram D _ u (control_agrees D recorded u) e

private theorem extend_reverse (D : Diagram Gate [B, B] []) (recorded : Bool)
    (u : D.Edge → Bool) (e : D.Edge) :
    extend D recorded (reverse u e) =
      reverse (extend D recorded u) (compRight OutputLatch.diagram D e) := by
  rcases e with i | e
  · fin_cases i
    · change extend D recorded (reverse u (.inl 0)) =
        reverse (extend D recorded u) (compRight OutputLatch.diagram D (.inl 0))
      unfold extend
      rw [reverse_self, reverse_of_ne u (show (.inl 1 : D.Edge) ≠ .inl 0 by simp)]
      rw [OutputLatch.canonical_flip_sat]
      exact (glueComp_congr_right OutputLatch.diagram D _
        (fun e => reverse_of_ne u (by simp))).trans (glueComp_reverse_left _ _ _ _ _)
    · change extend D recorded (reverse u (.inl 1)) =
        reverse (extend D recorded u) (compRight OutputLatch.diagram D (.inl 1))
      unfold extend
      rw [reverse_self, reverse_of_ne u (show (.inl 0 : D.Edge) ≠ .inl 1 by simp)]
      rw [OutputLatch.canonical_flip_try]
      exact (glueComp_congr_right OutputLatch.diagram D _
        (fun e => reverse_of_ne u (by simp))).trans (glueComp_reverse_left _ _ _ _ _)
  · unfold extend
    rw [reverse_of_ne u (show (.inl 0 : D.Edge) ≠ .inr e by simp),
      reverse_of_ne u (show (.inl 1 : D.Edge) ≠ .inr e by simp)]
    exact glueComp_reverse_right _ _ _ _ _

private theorem extend_reachable (D : Diagram Gate [B, B] []) (recorded : Bool)
    {s t : D.Edge → Bool} (h : (D.graph Gate.interp).Reachable s t) :
    ((OutputLatch.diagram.comp D).graph Gate.interp).Reachable
      (extend D recorded s) (extend D recorded t) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨hu, hv, e, rfl⟩ := hs
    exact ih.tail ⟨legal_extend D recorded hu, legal_extend D recorded hv,
      compRight OutputLatch.diagram D e, extend_reverse D recorded _ e⟩

private theorem extend_initial (recorded : Bool) (qs : List Quantifier) (ms : List (List Bool)) :
    extend (Matrix.body qs ms) recorded (Initial.body qs ms).orient =
      (configuration recorded qs ms).orient := by
  unfold extend
  rw [Realization.orient_top, Realization.orient_top]
  rfl

private theorem record_extend (D : Diagram Gate [B, B] []) {u : D.Edge → Bool}
    (hu : (D.graph Gate.interp).Legal u) (hsat : u (.inl 0) = false) :
    ((OutputLatch.diagram.comp D).graph Gate.interp).Reachable
      (extend D false u) (extend D true u) := by
  have hag := control_agrees D false u
  rw [hsat] at hag
  unfold extend
  rw [hsat]
  exact (innerReach_glueComp_left (OutputLatch.record (u (.inl 1))) hu hag).reachable

/-- **A true quantified matrix reaches the fixed target.** Execute the body, set the output
record with three internal moves, and undo the body while retaining that record. -/
theorem reachable_target_of_truth (qs : List Quantifier) (ms : List (List Bool))
    (h : Chain.Truth (Matrix.Satisfies ms) qs []) :
    ((diagram qs ms).graph Gate.interp).Reachable (initial qs ms).orient (target qs ms).orient := by
  obtain ⟨t, ht, he⟩ := Matrix.canReverse_of_truth qs ms h
  have hsat : t (.inl 0) = false := Bool.eq_false_of_not_eq_true
    (by rwa [Realization.orient_top] at he)
  have hp := (extend_reachable (Matrix.body qs ms) false ht).trans
    ((record_extend (Matrix.body qs ms) (ht.legal (Initial.body qs ms).legal) hsat).trans
      (extend_reachable (Matrix.body qs ms) true ht.symm))
  rwa [extend_initial, extend_initial] at hp

private theorem unlocked_of_step (qs : List Quantifier) (ms : List (List Bool))
    {s t : (diagram qs ms).Edge → Bool} (h : ((diagram qs ms).graph Gate.interp).Step s t)
    (hchange : t (output qs ms) ≠ s (output qs ms)) :
    s ((bodyOcc qs ms).emb (.inl 0)) = false := by
  obtain ⟨hs, ht, e, rfl⟩ := h
  obtain rfl : e = output qs ms := by
    by_contra hne
    exact hchange (reverse_of_ne s (Ne.symm hne))
  exact lock_body qs ms ▸
    (Latch.not_step_mem ((latchOcc qs ms).legal hs) ((latchOcc qs ms).legal_reverse ht) :
      s ((latchOcc qs ms).emb Latch.lock) = false)

/-- **Closed-circuit soundness from any inactive legal start.** Changing the output memory
requires a successful body at some step of the path. The initial output record may have either
value; only the outer try input must be inactive. -/
theorem truth_of_output_changed (qs : List Quantifier) (ms : List (List Bool))
    {s t : (diagram qs ms).Edge → Bool} (hs : ((diagram qs ms).graph Gate.interp).Legal s)
    (hstart : s (tryIn qs ms) = false) (h : ((diagram qs ms).graph Gate.interp).Reachable s t)
    (hchange : t (output qs ms) ≠ s (output qs ms)) :
    Chain.Truth (Matrix.Satisfies ms) qs [] := by
  revert hchange
  induction h with
  | refl => exact fun hn => (hn rfl).elim
  | @tail u v hr hstep ih =>
    intro hchange
    by_cases he : u (output qs ms) = s (output qs ms)
    · exact Matrix.truth_of_reachable qs ms (bodyOcc qs ms) hs hstart hr
        (unlocked_of_step qs ms hstep fun hh => hchange (hh.trans he))
    · exact ih he

/-- **Configuration-to-configuration correctness of the closed circuit.** Its explicit target
is reachable exactly when the quantified matrix is true. -/
theorem reachable_target_iff_truth (qs : List Quantifier) (ms : List (List Bool)) :
    ((diagram qs ms).graph Gate.interp).Reachable (initial qs ms).orient (target qs ms).orient ↔
      Chain.Truth (Matrix.Satisfies ms) qs [] := by
  refine ⟨fun h => truth_of_output_changed qs ms (initial qs ms).legal (by simp [initial]) h
    (by simp [initial, target]), reachable_target_of_truth qs ms⟩

/-- **Configuration-to-edge correctness of the closed circuit.** Its output memory can be
reversed from the explicit initial configuration exactly when the quantified matrix is true. -/
theorem canReverse_initial_iff_truth (qs : List Quantifier) (ms : List (List Bool)) :
    ((diagram qs ms).graph Gate.interp).CanReverse (initial qs ms).orient (output qs ms) ↔
      Chain.Truth (Matrix.Satisfies ms) qs [] := by
  refine ⟨fun ⟨_, ht, he⟩ => truth_of_output_changed qs ms (initial qs ms).legal
    (by simp [initial]) ht he, fun h =>
      ⟨(target qs ms).orient, reachable_target_of_truth qs ms h, by simp [initial, target]⟩⟩

/-- **Edge-to-edge correctness of the closed circuit.** A legal configuration with trying
inactive can reach a satisfied body exactly when the quantified matrix is true. -/
theorem exists_reachable_sat_iff_truth (qs : List Quantifier) (ms : List (List Bool)) :
    (∃ s t, ((diagram qs ms).graph Gate.interp).Legal s ∧ s (tryIn qs ms) = false ∧
      t (satOut qs ms) = false ∧ ((diagram qs ms).graph Gate.interp).Reachable s t) ↔
      Chain.Truth (Matrix.Satisfies ms) qs [] := by
  refine ⟨fun ⟨s, t, hs, htry, hsat, ht⟩ =>
    Matrix.truth_of_reachable qs ms (bodyOcc qs ms) hs htry ht hsat, fun h => ?_⟩
  obtain ⟨t, ht, he⟩ := Matrix.canReverse_of_truth qs ms h
  have hsat : t (.inl 0) = false := Bool.eq_false_of_not_eq_true
    (by rwa [Realization.orient_top] at he)
  exact ⟨(initial qs ms).orient, extend (Matrix.body qs ms) false t,
    (initial qs ms).legal, by simp [initial],
    (congrFun (extend_compRight (Matrix.body qs ms) false t) (.inl 0)).trans hsat,
    extend_initial false qs ms ▸ extend_reachable (Matrix.body qs ms) false ht⟩

end Cslib.Complexity.NCL.QBF.Circuit
