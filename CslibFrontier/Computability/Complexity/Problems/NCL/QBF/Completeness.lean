/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Execution
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Matrix.Evaluation
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Execution

/-!
# Completeness of the quantifier circuit

Execute a true quantified matrix by induction on its prefix. An existential chooses a witness.
A universal calls its suffix with false, records success, undoes that call, switches to true,
and calls the suffix again. All calls fix trying and the incoming literal bundle.

The recursion regroups the existing chain and terminal with `Diagram.compAssoc`; it uses the
same graph and the explicit initial configurations of `NCL.QBF.Initial`.

## Main definitions

The proof uses inactive suffix configurations with prescribed incoming literal directions.

## Main results

* `Cslib.Complexity.NCL.QBF.Matrix.canReverse_iff_truth`: from the canonical initial
  configuration, the body's sat wire is reversible exactly when the quantified matrix is true.
* `Cslib.Complexity.NCL.QBF.Source.canReverse_iff_eval`: the same equivalence for the closed
  upstream source QBF, including repeated binders.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF

open Diagram Gate Network

local notation "B" => Color.blue

namespace Completeness

private abbrev colors (p : ℕ) : List Color := bundle (2 * p) ++ []

private abbrev circuit (p : ℕ) (qs : List Quantifier) (ms : List (List Bool)) :=
  (Chain.diagram (colors p) qs).comp (Matrix.terminal p qs ms)

private def initial (p : ℕ) (qs : List Quantifier) (ms : List (List Bool)) :
    Realization Gate.interp (circuit p qs ms) (Initial.controls (colors p)) [] :=
  (Initial.chain (colors p) qs).comp (Initial.terminal p qs ms)

private theorem controls_le (p : ℕ) (ls : List Bool) (hl : ls.length = 2 * p) (attempt : Bool) :
    List.Forall₂ (· ≤ ·) (Initial.controls (colors p)) ([true, attempt] ++ ls) := by
  have htail (xs : List Bool) : List.Forall₂ (· ≤ ·) (List.replicate xs.length false) xs := by
    induction xs with
    | nil => exact .nil
    | cons x _ ih => exact .cons (Bool.false_le x) ih
  simpa [Initial.controls, colors, bundle, ← hl] using
    List.Forall₂.cons (le_rfl : true ≤ true) (.cons (Bool.false_le attempt) (htail ls))

private def config (p : ℕ) (qs : List Quantifier) (ms : List (List Bool))
    (attempt : Bool) (ls : List Bool) (hl : ls.length = 2 * p) :
    Realization Gate.interp (circuit p qs ms) ([true, attempt] ++ ls) [] :=
  (initial p qs ms).withTop Gate.interp_forward ([true, attempt] ++ ls)
    (by simp [colors, bundle, hl]) (controls_le p ls hl attempt)

private def localIdle : (q : Quantifier) → (attempt : Bool) →
    Realization Gate.interp q.gadget [true, attempt] [true, false, false, false]
  | .ex, false => Initial.existsInitial
  | .ex, true => ExistsGadget.Execution.idle
  | .all, false => Initial.forallInitial
  | .all, true => ForallGadget.Execution.idle

private theorem localIdle_inner (q : Quantifier) (attempt : Bool) : ∀ e : q.gadget.Inner,
    (localIdle q attempt).orient (.inr e) = (Initial.quantifier q).orient (.inr e) := by
  cases q <;> cases attempt <;> decide +kernel

private def wires (p : ℕ) (ls : List Bool) (hl : ls.length = 2 * p) :
    Realization Gate.interp (Diagram.id (colors p)) ls ls :=
  .id _ _ (by simp [colors, bundle, hl])

private theorem config_cons (p : ℕ) (q : Quantifier) (qs : List Quantifier)
    (ms : List (List Bool)) (attempt : Bool) (ls : List Bool) (hl : ls.length = 2 * p) :
    (config p (q :: qs) ms attempt ls hl).orient =
      glueComp (q.gadget.tensor (.id (colors p))) (circuit (p + 1) qs ms)
        ((localIdle q attempt).tensor (wires p ls hl)).orient
        (config (p + 1) qs ms false ([false, false] ++ ls) (by simp [hl]; omega)).orient ∘
          compAssoc (q.gadget.tensor (.id (colors p)))
            (Chain.diagram (colors (p + 1)) qs) (Matrix.terminal (p + 1) qs ms) := by
  funext e
  rcases e with i | ((e | e) | e) | e
  · change (config p (q :: qs) ms attempt ls hl).orient (.inl i) =
      ((localIdle q attempt).tensor (wires p ls hl)).orient (.inl i)
    rw [Realization.orient_top, Realization.orient_top]
  · exact (localIdle_inner q attempt e).symm
  · exact e.elim
  · rfl
  · rfl

private theorem legal_dormant (p : ℕ) (qs : List Quantifier) (ms : List (List Bool))
    (u : (circuit p qs ms).Edge → Bool)
    (hinner : ∀ e, u (.inr e) = (initial p qs ms).orient (.inr e))
    (hsat : u (.inl ⟨0, by simp⟩) = true) : ((circuit p qs ms).graph Gate.interp).Legal u := by
  refine legal_top_mono Gate.interp_forward _ (initial p qs ms).legal ?_ (fun e => (hinner e).symm)
  intro i
  rw [Realization.orient_top]
  cases hi : i.val with
  | zero =>
    have he : i = ⟨0, by simp⟩ := Fin.ext hi
    rw [he, hsat]
    simp [Initial.controls]
  | succ n =>
    simp only [Initial.controls, List.getElem!_eq_getElem?_getD, List.getElem?_cons_succ,
      ← List.replicate_succ, List.getElem?_replicate]
    split <;> simp

private abbrev head (p : ℕ) (q : Quantifier) := q.gadget.tensor (.id (colors p))

private def attach (p : ℕ) (q : Quantifier) (qs : List Quantifier) (ms : List (List Bool))
    (ls : List Bool) (hl : ls.length = 2 * p) (u : q.gadget.Edge → Bool)
    (v : (circuit (p + 1) qs ms).Edge → Bool) :
    ((head p q).comp (circuit (p + 1) qs ms)).Edge → Bool :=
  glueComp (head p q) (circuit (p + 1) qs ms)
    (glueTensor q.gadget (.id (colors p)) u (wires p ls hl).orient) v

private theorem attach_config (p : ℕ) (q : Quantifier) (qs : List Quantifier)
    (ms : List (List Bool)) (ls : List Bool) (hl : ls.length = 2 * p)
    (u : q.gadget.Edge → Bool) (attempt : Bool) (vs : List Bool) (hv : vs.length = 2 * (p + 1)) :
    attach p q qs ms ls hl u (config (p + 1) qs ms attempt vs hv).orient =
      attach p q qs ms ls hl u (initial (p + 1) qs ms).orient :=
  glueComp_congr_right _ _ _ (fun _ => rfl)

private theorem config_cons_attach (p : ℕ) (q : Quantifier) (qs : List Quantifier)
    (ms : List (List Bool)) (attempt : Bool) (ls : List Bool) (hl : ls.length = 2 * p) :
    (config p (q :: qs) ms attempt ls hl).orient =
      attach p q qs ms ls hl (localIdle q attempt).orient (initial (p + 1) qs ms).orient ∘
        compAssoc (head p q) (Chain.diagram (colors (p + 1)) qs)
          (Matrix.terminal (p + 1) qs ms) := by
  rw [config_cons]
  exact congrArg (· ∘ compAssoc (head p q) (Chain.diagram (colors (p + 1)) qs)
    (Matrix.terminal (p + 1) qs ms)) (attach_config p q qs ms ls hl _ _ _ _)

private theorem config_nil (p : ℕ) (ms : List (List Bool)) (ls : List Bool)
    (hl : ls.length = 2 * p) :
    (config p [] ms true ls hl).orient =
      Matrix.Evaluation.idle p ls hl ms ∘ idComp (Matrix.terminalBase p ms) := by
  funext e
  rcases e with i | (e | e)
  · change (config p [] ms true ls hl).orient (.inl i) =
      (Matrix.Evaluation.evalTerminalBase p ls hl ms true (by simp)).orient (.inl i)
    rw [Realization.orient_top, Realization.orient_top]
  · exact e.elim
  · exact (congrFun (Initial.terminalBase_off p ms) (.inr e)).symm

private theorem regroup_path (p : ℕ) (q : Quantifier) (qs : List Quantifier)
    (ms : List (List Bool)) (ls : List Bool) (hl : ls.length = 2 * p)
    {t : ((head p q).comp (circuit (p + 1) qs ms)).Edge → Bool}
    (h : (((head p q).comp (circuit (p + 1) qs ms)).graph Gate.interp).ReachableOn
      (AllowsTop 0)
      (attach p q qs ms ls hl (localIdle q true).orient (initial (p + 1) qs ms).orient) t) :
    ((circuit p (q :: qs) ms).graph Gate.interp).ReachableOn
      (AllowsTop 0) (config p (q :: qs) ms true ls hl).orient
      (t ∘ compAssoc (head p q) (Chain.diagram (colors (p + 1)) qs)
        (Matrix.terminal (p + 1) qs ms)) := by
  rw [config_cons_attach]
  apply reachableOn_compAssoc_allowsTop _ _ _ 0 h
  apply (legal_compAssoc _ _ _ _).1
  rw [← config_cons_attach]
  exact (config p (q :: qs) ms true ls hl).legal

private theorem attach_legal (p : ℕ) (q : Quantifier) (qs : List Quantifier)
    (ms : List (List Bool)) (ls : List Bool) (hl : ls.length = 2 * p)
    {x y : List Bool} (u : Realization Gate.interp q.gadget x y)
    {v : (circuit (p + 1) qs ms).Edge → Bool}
    (hv : ((circuit (p + 1) qs ms).graph Gate.interp).Legal v)
    (hb : (circuit (p + 1) qs ms).topList v = y ++ ls) :
    (((head p q).comp (circuit (p + 1) qs ms)).graph Gate.interp).Legal
      (attach p q qs ms ls hl u.orient v) :=
  legal_glueComp (u.tensor (wires p ls hl)).legal hv
    (fun i => congrFun (List.ofFn_inj.1 (hb.trans (u.tensor (wires p ls hl)).bot_eq.symm)) i)

private theorem head_bottom_zero (p : ℕ) (q : Quantifier) :
    (head p q).bottom ⟨0, by simp⟩ = tensorLeft q.gadget (.id (colors p)) (q.gadget.bottom 0) :=
  bottom_tensor_left q.gadget (.id (colors p)) (0 : Fin 4)

private theorem attach_dormant_legal (p : ℕ) (q : Quantifier) (qs : List Quantifier)
    (ms : List (List Bool)) (ls : List Bool) (hl : ls.length = 2 * p)
    {u : q.gadget.Edge → Bool} (hu : (q.gadget.graph Gate.interp).Legal u)
    (hsat : u (q.gadget.bottom 0) = true) :
    (((head p q).comp (circuit (p + 1) qs ms)).graph Gate.interp).Legal
      (attach p q qs ms ls hl u (initial (p + 1) qs ms).orient) := by
  refine (legal_comp_iff _ _ _).2 ⟨?_, ?_⟩
  · rw [show attach p q qs ms ls hl u (initial (p + 1) qs ms).orient ∘
        compLeft (head p q) (circuit (p + 1) qs ms) =
        glueTensor q.gadget (.id (colors p)) u (wires p ls hl).orient from
      funext (glueComp_compLeft _ _ _ _)]
    exact legal_glueTensor hu (wires p ls hl).legal
  · apply legal_dormant (p + 1) qs ms
      (attach p q qs ms ls hl u (initial (p + 1) qs ms).orient ∘
        compRight (head p q) (circuit (p + 1) qs ms)) (fun _ => rfl)
    dsimp only [Function.comp_apply, attach, compRight]
    rwa [glueComp_compLeft, head_bottom_zero, glueTensor_tensorLeft]

private theorem attach_allowed (p : ℕ) (q : Quantifier) (qs : List Quantifier)
    (ms : List (List Bool)) {e : q.gadget.Edge} (he : e ≠ .inl 1) :
    AllowsTop 0 (compLeft (head p q) (circuit (p + 1) qs ms)
      (tensorLeft q.gadget (.id (colors p)) e)) := by
  rcases e with j | e
  · fin_cases j
    · exact (allowsTop_inl _ _).2 rfl
    · exact (he rfl).elim
  · exact allowsTop_inr 0 _

private theorem attach_path (p : ℕ) (q : Quantifier) (qs : List Quantifier)
    (ms : List (List Bool)) (ls : List Bool) (hl : ls.length = 2 * p)
    {allowed : q.gadget.Edge → Prop} {s t : q.gadget.Edge → Bool}
    (h : (q.gadget.graph Gate.interp).ReachableOn allowed s t)
    (v : (circuit (p + 1) qs ms).Edge → Bool)
    (hlegal : ∀ u, (q.gadget.graph Gate.interp).ReachableOn allowed s u →
      (((head p q).comp (circuit (p + 1) qs ms)).graph Gate.interp).Legal
        (attach p q qs ms ls hl u v))
    (he : ∀ e, allowed e → e ≠ .inl 1) :
    (((head p q).comp (circuit (p + 1) qs ms)).graph Gate.interp).ReachableOn
      (AllowsTop 0)
      (attach p q qs ms ls hl s v) (attach p q qs ms ls hl t v) :=
  h.map (attach p q qs ms ls hl · v)
    (compLeft (head p q) (circuit (p + 1) qs ms) ∘ tensorLeft q.gadget (.id (colors p))) hlegal
    (fun u e _ => (congrArg (glueComp (head p q) (circuit (p + 1) qs ms) · v)
      (glueTensor_reverse_left q.gadget (.id (colors p)) u (wires p ls hl).orient e)).trans
        (glueComp_reverse_left _ _ _ _ _))
    (fun e hallowed => attach_allowed p q qs ms (he e hallowed))

private theorem prepare_path (p : ℕ) (q : Quantifier) (qs : List Quantifier)
    (ms : List (List Bool)) (ls : List Bool) (hl : ls.length = 2 * p)
    {allowed : q.gadget.Edge → Prop} {s t : q.gadget.Edge → Bool}
    (h : (q.gadget.graph Gate.interp).ReachableOn allowed s t)
    (hs : (q.gadget.graph Gate.interp).Legal s) (hsat : s (q.gadget.bottom 0) = true)
    (hfixed : ¬allowed (q.gadget.bottom 0)) (he : ∀ e, allowed e → e ≠ .inl 1) :
    (((head p q).comp (circuit (p + 1) qs ms)).graph Gate.interp).ReachableOn
      (AllowsTop 0)
      (attach p q qs ms ls hl s (initial (p + 1) qs ms).orient)
      (attach p q qs ms ls hl t (initial (p + 1) qs ms).orient) :=
  attach_path p q qs ms ls hl h _
    (fun _ hu => attach_dormant_legal p q qs ms ls hl (hu.reachable.legal hs)
      ((hu.apply_eq hfixed).symm.trans hsat)) he

private theorem fixed_path (p : ℕ) (q : Quantifier) (qs : List Quantifier)
    (ms : List (List Bool)) (ls : List Bool) (hl : ls.length = 2 * p)
    {allowed : q.gadget.Edge → Prop} {s t : q.gadget.Edge → Bool}
    (h : (q.gadget.graph Gate.interp).ReachableOn allowed s t)
    (hs : (q.gadget.graph Gate.interp).Legal s)
    (hfixed : ∀ j, ¬allowed (q.gadget.bottom j)) (he : ∀ e, allowed e → e ≠ .inl 1)
    {v : (circuit (p + 1) qs ms).Edge → Bool}
    (hv : ((circuit (p + 1) qs ms).graph Gate.interp).Legal v)
    (hb : (circuit (p + 1) qs ms).topList v = q.gadget.botList s ++ ls) :
    (((head p q).comp (circuit (p + 1) qs ms)).graph Gate.interp).ReachableOn
      (AllowsTop 0)
      (attach p q qs ms ls hl s v) (attach p q qs ms ls hl t v) := by
  refine attach_path p q qs ms ls hl h v (fun u hu => ?_) he
  let ur : Realization Gate.interp q.gadget (q.gadget.topList u) (q.gadget.botList u) :=
    ⟨u, hu.reachable.legal hs, rfl, rfl⟩
  have hbot : q.gadget.botList u = q.gadget.botList s :=
    List.ofFn_inj.2 (funext fun j => (hu.apply_eq (hfixed j)).symm)
  exact attach_legal p q qs ms ls hl ur hv (hb.trans (congrArg (· ++ ls) hbot.symm))

private theorem padded_response (p : ℕ) (q : Quantifier) (ls : List Bool)
    (hl : ls.length = 2 * p) (f : Bool → q.gadget.Edge → Bool)
    (hf : f false = reverse (f true) (q.gadget.bottom 0)) :
    glueTensor q.gadget (.id (colors p)) (f false) (wires p ls hl).orient =
      reverse (glueTensor q.gadget (.id (colors p)) (f true) (wires p ls hl).orient)
        ((head p q).bottom ⟨0, by simp⟩) := by
  rw [head_bottom_zero, hf]
  exact glueTensor_reverse_left _ _ _ _ _

private theorem call_allowed (p : ℕ) (q : Quantifier) (qs : List Quantifier)
    (ms : List (List Bool)) (e : (circuit (p + 1) qs ms).Edge)
    (he : AllowsTop 0 e) :
    AllowsTop 0 (compRight (head p q) (circuit (p + 1) qs ms) e) := by
  rcases e with i | e
  · obtain rfl : i = ⟨0, by simp⟩ := Fin.ext ((allowsTop_inl _ _).1 he)
    change AllowsTop 0
      (compLeft (head p q) (circuit (p + 1) qs ms) ((head p q).bottom ⟨0, by simp⟩))
    rw [head_bottom_zero]
    exact attach_allowed p q qs ms (by cases q <;> decide +kernel)
  · exact allowsTop_inr 0 _

private theorem call_path (p : ℕ) (q : Quantifier) (qs : List Quantifier)
    (ms : List (List Bool)) (ls : List Bool) (hl : ls.length = 2 * p) (value : Bool)
    {x : Bool → List Bool}
    (f : (bit : Bool) → Realization Gate.interp q.gadget (x bit) [bit, true, value, !value])
    (hf : (f false).orient = reverse (f true).orient (q.gadget.bottom 0))
    {t : (circuit (p + 1) qs ms).Edge → Bool}
    (h : ((circuit (p + 1) qs ms).graph Gate.interp).ReachableOn
      (AllowsTop 0)
      (config (p + 1) qs ms true ([value, !value] ++ ls) (by simp [hl]; omega)).orient t)
    (hsat : t (.inl ⟨0, by simp⟩) = false) :
    (((head p q).comp (circuit (p + 1) qs ms)).graph Gate.interp).ReachableOn
      (AllowsTop 0)
      (attach p q qs ms ls hl (f true).orient
        (config (p + 1) qs ms true ([value, !value] ++ ls) (by simp [hl]; omega)).orient)
      (attach p q qs ms ls hl (f false).orient t) := by
  let j : Fin ([B, B] ++ colors (p + 1)).length := ⟨0, by simp⟩
  let fp (bit : Bool) := ((f bit).tensor (wires p ls hl)).orient
  have hfp := padded_response p q ls hl (fun bit => (f bit).orient) hf
  have hp := reachableOn_glueResponse_allowsTop j fp hfp h (allowed := AllowsTop 0)
    (fun u hu => ?_) (call_allowed p q qs ms)
  · have hs : (config (p + 1) qs ms true ([value, !value] ++ ls)
        (by simp [hl]; omega)).orient (.inl j) = true := by
      rw [Realization.orient_top]
      rfl
    simp only [glueResponse, hs, show t (.inl j) = false from hsat] at hp
    exact hp
  · apply attach_legal p q qs ms ls hl (f (u (.inl j)))
      (hu.reachable.legal (config (p + 1) qs ms true ([value, !value] ++ ls)
        (by simp [hl]; omega)).legal)
    exact topList_of_reachableOn hu
      (config (p + 1) qs ms true ([value, !value] ++ ls) (by simp [hl]; omega)).top_eq

private def Succeeds (p : ℕ) (qs : List Quantifier) (ms : List (List Bool))
    (ls : List Bool) (hl : ls.length = 2 * p) : Prop :=
  ∃ t, ((circuit p qs ms).graph Gate.interp).ReachableOn
    (AllowsTop 0) (config p qs ms true ls hl).orient t ∧
    t (.inl ⟨0, by simp⟩) = false

private theorem regroup_success (p : ℕ) (q : Quantifier) (qs : List Quantifier)
    (ms : List (List Bool)) (ls : List Bool) (hl : ls.length = 2 * p)
    {t : ((head p q).comp (circuit (p + 1) qs ms)).Edge → Bool}
    (h : (((head p q).comp (circuit (p + 1) qs ms)).graph Gate.interp).ReachableOn
      (AllowsTop 0)
      (attach p q qs ms ls hl (localIdle q true).orient (initial (p + 1) qs ms).orient) t)
    (ht : t (.inl ⟨0, by simp⟩) = false) : Succeeds p (q :: qs) ms ls hl :=
  ⟨_, regroup_path p q qs ms ls hl h, ht⟩

private theorem succeeds_nil (p : ℕ) (ms : List (List Bool)) (ls : List Bool)
    (hl : ls.length = 2 * p) (h : ms.all (hits · ls) = true) : Succeeds p [] ms ls hl := by
  have hp := reachableOn_idComp_allowsTop (Matrix.terminalBase p ms) 0
    (Matrix.Evaluation.reachable_sat p ls hl ms h) (Matrix.Evaluation.legal_idle p ls hl ms)
  refine ⟨(Matrix.Evaluation.evalTerminalBase p ls hl ms false (fun _ => h)).orient ∘
    idComp (Matrix.terminalBase p ms), ?_, ?_⟩
  · rw [config_nil]
    exact hp
  · change (Matrix.Evaluation.evalTerminalBase p ls hl ms false (fun _ => h)).orient
      (.inl ⟨0, by simp⟩) = false
    rw [Realization.orient_top]
    rfl

private theorem succeeds_ex (p : ℕ) (qs : List Quantifier) (ms : List (List Bool))
    (ls : List Bool) (hl : ls.length = 2 * p) (value : Bool)
    (h : Succeeds (p + 1) qs ms ([value, !value] ++ ls) (by simp [hl]; omega)) :
    Succeeds p (.ex :: qs) ms ls hl := by
  obtain ⟨t, ht, hsat⟩ := h
  have hp := prepare_path p .ex qs ms ls hl (ExistsGadget.Execution.prepare value)
    ExistsGadget.Execution.idle.legal (by decide +kernel) (fun he => he.1 rfl)
    (fun _ he => he.2)
  have hc := call_path p .ex qs ms ls hl value (ExistsGadget.Execution.ready value)
    (ExistsGadget.Execution.ready_sat value) ht hsat
  simp only [attach_config] at hc
  apply regroup_success p .ex qs ms ls hl (hp.trans hc)
  change (ExistsGadget.Execution.ready value false).orient (.inl 0) = false
  rw [Realization.orient_top]
  rfl

private theorem called_top (p : ℕ) (qs : List Quantifier) (ms : List (List Bool))
    (ls : List Bool) (hl : ls.length = 2 * p) (value : Bool)
    {t : (circuit (p + 1) qs ms).Edge → Bool}
    (h : ((circuit (p + 1) qs ms).graph Gate.interp).ReachableOn
      (AllowsTop 0)
      (config (p + 1) qs ms true ([value, !value] ++ ls) (by simp [hl]; omega)).orient t)
    (hsat : t (.inl ⟨0, by simp⟩) = false) :
    (circuit (p + 1) qs ms).topList t = [false, true, value, !value] ++ ls := by
  have hh := topList_of_reachableOn h
    (config (p + 1) qs ms true ([value, !value] ++ ls) (by simp [hl]; omega)).top_eq
  rw [hsat] at hh
  exact hh

private theorem false_phase (p : ℕ) (qs : List Quantifier) (ms : List (List Bool))
    (ls : List Bool) (hl : ls.length = 2 * p)
    (h : Succeeds (p + 1) qs ms ([false, true] ++ ls) (by simp [hl]; omega)) :
    (((head p .all).comp (circuit (p + 1) qs ms)).graph Gate.interp).ReachableOn
      (AllowsTop 0)
      (attach p .all qs ms ls hl ForallGadget.Execution.idle.orient (initial (p + 1) qs ms).orient)
      (attach p .all qs ms ls hl (ForallGadget.Execution.ready false true true).orient
        (initial (p + 1) qs ms).orient) := by
  obtain ⟨t, ht, hsat⟩ := h
  have hp := prepare_path p .all qs ms ls hl (ForallGadget.Execution.prepare false)
    ForallGadget.Execution.idle.legal (by decide +kernel) (fun he => he.2.2.1 rfl)
    (fun _ he => he.2.1)
  have hc := call_path p .all qs ms ls hl false (ForallGadget.Execution.ready false false)
    (ForallGadget.Execution.ready_sat false false) ht hsat
  have hb : (circuit (p + 1) qs ms).topList t =
      forallGadget.botList (ForallGadget.Execution.ready false false false).orient ++ ls := by
    rw [(ForallGadget.Execution.ready false false false).bot_eq]
    exact called_top p qs ms ls hl false ht hsat
  have hr := fixed_path p .all qs ms ls hl ForallGadget.Execution.record_false
    (ForallGadget.Execution.ready false false false).legal
    (fun j hn => hn (Or.inr ⟨j, rfl⟩)) (fun _ hn he => hn (Or.inl ⟨1, he⟩))
    (ht.reachable.legal (config (p + 1) qs ms true ([false, true] ++ ls)
      (by simp [hl]; omega)).legal) hb
  have hback := call_path p .all qs ms ls hl false (ForallGadget.Execution.ready false true)
    (ForallGadget.Execution.ready_sat false true) ht hsat
  simp only [attach_config] at hc hback
  exact hp.trans (hc.trans (hr.trans hback.symm))

private theorem true_phase (p : ℕ) (qs : List Quantifier) (ms : List (List Bool))
    (ls : List Bool) (hl : ls.length = 2 * p)
    (h : Succeeds (p + 1) qs ms ([true, false] ++ ls) (by simp [hl]; omega)) :
    ∃ t, (((head p .all).comp (circuit (p + 1) qs ms)).graph Gate.interp).ReachableOn
      (AllowsTop 0)
      (attach p .all qs ms ls hl (ForallGadget.Execution.ready false true true).orient
        (initial (p + 1) qs ms).orient) t ∧ t (.inl ⟨0, by simp⟩) = false := by
  obtain ⟨t, ht, hsat⟩ := h
  have hp := prepare_path p .all qs ms ls hl ForallGadget.Execution.switch_true
    (ForallGadget.Execution.ready false true true).legal (by decide +kernel)
    (fun he => he.2.2.1 rfl) (fun _ he => he.2.1)
  have hc := call_path p .all qs ms ls hl true (ForallGadget.Execution.ready true true)
    (ForallGadget.Execution.ready_sat true true) ht hsat
  have hb : (circuit (p + 1) qs ms).topList t =
      forallGadget.botList (ForallGadget.Execution.ready true true false).orient ++ ls := by
    rw [(ForallGadget.Execution.ready true true false).bot_eq]
    exact called_top p qs ms ls hl true ht hsat
  have hf := fixed_path p .all qs ms ls hl ForallGadget.Execution.finish
    (ForallGadget.Execution.ready true true false).legal
    (fun j hn => hn.2 j rfl) (fun _ hn => hn.1)
    (ht.reachable.legal (config (p + 1) qs ms true ([true, false] ++ ls)
      (by simp [hl]; omega)).legal) hb
  simp only [attach_config] at hc
  refine ⟨attach p .all qs ms ls hl ForallGadget.Execution.success.orient t,
    hp.trans (hc.trans hf), ?_⟩
  change ForallGadget.Execution.success.orient (.inl 0) = false
  rw [Realization.orient_top]
  rfl

private theorem succeeds_all (p : ℕ) (qs : List Quantifier) (ms : List (List Bool))
    (ls : List Bool) (hl : ls.length = 2 * p)
    (h : ∀ value, Succeeds (p + 1) qs ms ([value, !value] ++ ls) (by simp [hl]; omega)) :
    Succeeds p (.all :: qs) ms ls hl := by
  have hf := false_phase p qs ms ls hl (h false)
  obtain ⟨t, ht, hsat⟩ := true_phase p qs ms ls hl (h true)
  exact regroup_success p .all qs ms ls hl (hf.trans ht) hsat

private theorem literalValues_snoc (values : List Bool) (value : Bool) :
    Chain.literalValues (values ++ [value]) = [value, !value] ++ Chain.literalValues values := by
  simp [Chain.literalValues]

private theorem length_literalValues (values : List Bool) :
    (Chain.literalValues values).length = 2 * values.length := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    have hc : Chain.literalValues (value :: values) =
        Chain.literalValues values ++ [value, !value] := by simp [Chain.literalValues]
    rw [hc]
    simp only [List.length_append, List.length_cons, List.length_nil, ih]
    omega

private theorem execute : ∀ (qs : List Quantifier) (values : List Bool)
    (ms : List (List Bool)), Chain.Truth (Matrix.Satisfies ms) qs values →
      Succeeds values.length qs ms (Chain.literalValues values) (length_literalValues values)
  | [], values, ms, h => succeeds_nil _ _ _ _ h
  | .ex :: qs, values, ms, h => by
    obtain ⟨value, hv⟩ := h
    apply succeeds_ex values.length qs ms _ _ value
    have ih := execute qs (values ++ [value]) ms hv
    simpa only [List.length_append, List.length_singleton, literalValues_snoc] using ih
  | .all :: qs, values, ms, h => by
    apply succeeds_all values.length qs ms _ _
    intro value
    have ih := execute qs (values ++ [value]) ms (h value)
    simpa only [List.length_append, List.length_singleton, literalValues_snoc] using ih

private theorem activate_body (qs : List Quantifier) (ms : List (List Bool)) :
    ((Matrix.body qs ms).graph Gate.interp).Step (Initial.body qs ms).orient
      (config 0 qs ms true [] rfl).orient := by
  let active : Realization Gate.interp (Matrix.body qs ms) [true, true] [] :=
    config 0 qs ms true [] rfl
  change ((Matrix.body qs ms).graph Gate.interp).Step (Initial.body qs ms).orient active.orient
  refine ⟨(Initial.body qs ms).legal, active.legal, .inl 1, ?_⟩
  funext e
  rcases e with i | e
  · fin_cases i
    · change active.orient (.inl 0) = reverse (Initial.body qs ms).orient (.inl 1) (.inl 0)
      rw [reverse_of_ne _ (by simp), Realization.orient_top, Realization.orient_top]
      rfl
    · change active.orient (.inl 1) = reverse (Initial.body qs ms).orient (.inl 1) (.inl 1)
      rw [reverse_self, Realization.orient_top, Realization.orient_top]
      rfl
  · rw [reverse_of_ne _ (by simp)]
    rfl

end Completeness

namespace Matrix

/-- **Completeness of the actual QBF body.** A true quantified matrix can reverse the outer
satisfied wire from the explicit inactive initial configuration. -/
theorem canReverse_of_truth (qs : List Quantifier) (ms : List (List Bool))
    (h : Chain.Truth (Satisfies ms) qs []) :
    ((body qs ms).graph Gate.interp).CanReverse (Initial.body qs ms).orient (.inl 0) := by
  obtain ⟨t, ht, hsat⟩ := Completeness.execute qs [] ms h
  let t' : (body qs ms).Edge → Bool := t
  refine ⟨t',
    (Relation.ReflTransGen.single (Completeness.activate_body qs ms)).trans ht.reachable, ?_⟩
  rw [show t' (.inl 0) = false from hsat, Realization.orient_top]
  decide +kernel

/-- Reversing the actual body's sat wire from its canonical initial configuration is
equivalent to the quantified matrix, for every prefix and CNF. -/
theorem canReverse_iff_truth (qs : List Quantifier) (ms : List (List Bool)) :
    ((body qs ms).graph Gate.interp).CanReverse (Initial.body qs ms).orient (.inl 0) ↔
      Chain.Truth (Satisfies ms) qs [] :=
  ⟨fun ⟨t, ht, he⟩ => truth_of_reachable qs ms .refl (Initial.body qs ms).legal
    (by rw [Realization.orient_top]; rfl : (Initial.body qs ms).orient (.inl 1) = false) ht
    (Bool.eq_false_of_not_eq_true (by rwa [Realization.orient_top] at he)),
   canReverse_of_truth qs ms⟩

end Matrix

namespace Source

open Cslib.Logic.PL Cslib.Logic.PL.QBF

/-- The canonical NCL body's output is reversible exactly when the closed upstream source QBF
is true. The source may have repeated names, unused binders, or an empty matrix. -/
theorem canReverse_iff_eval {V : Type*} [DecidableEq V] (ps : List (V × V)) (φ : CNF V)
    (hclosed : (rounds ps (ofCNF φ)).Closed) (σ : V → Bool) :
    ((Matrix.body (quantifiers ps) (masks ps φ)).graph Gate.interp).CanReverse
      (Initial.body (quantifiers ps) (masks ps φ)).orient (.inl 0) ↔
      (rounds ps (ofCNF φ)).eval σ = true :=
  (Matrix.canReverse_iff_truth _ _).trans (truth_iff_eval ps φ hclosed σ)

end Source

end Cslib.Complexity.NCL.QBF
