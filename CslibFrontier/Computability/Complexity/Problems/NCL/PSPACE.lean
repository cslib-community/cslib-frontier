/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Reachability
public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.Reachability
public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.StepPolyTime
public import CslibFrontier.Computability.Complexity.Classes.Space.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# AND/OR NCL configuration reachability is in PSPACE

Check the structural and endpoint conditions, then run Savitch's procedure on configuration
bit strings. Its width and depth are the supplied initial list's length. The target is fitted
to that length so the space certificate applies to every input.

For an AND/OR multigraph with `m` edges, each legal orientation is an `m`-bit state, with
one bit for each loop as well. The algorithm checks graph validity, both configuration widths
and legality of the start, including for a path of length zero. This proves the AND/OR case of
the configuration-to-configuration upper bound in [HearnDemaine2005, Corollary 6] for the explicit
graph and bit-list encoding `encAndOrNCL`.

## Main results

* `Cslib.Complexity.NCL.AndOrNCL_mem_PSPACE`: configuration-to-configuration NCL is in PSPACE.

## References

* [Hearn and Demaine][HearnDemaine2005, Corollary 6]
* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.5][Sipser2013]
-/

public section

namespace Cslib.Complexity.NCL

open _root_.Turing.MultiTapeTM

private abbrev Input := AndOrNCL.Instance

private def fit (n : ℕ) (t : List Bool) : List Bool :=
  t.take n ++ List.replicate (n - t.length) false

private theorem length_fit (n : ℕ) (t : List Bool) : (fit n t).length = n := by
  simp only [fit, List.length_append, List.length_take, List.length_replicate]
  omega

private theorem fit_eq (n : ℕ) (t : List Bool) (ht : t.length = n) : fit n t = t := by
  simp [fit, ← ht]

private def search (x : Input) : Bool :=
  Cslib.Reachability.reach x.graph.checkStep x.initial.length x.initial.length x.initial
    (fit x.initial.length x.target)

private def guard (x : Input) : Bool :=
  x.graph.checkValid &&
    ((decide (x.initial.length = x.graph.edgeCount) &&
      decide (x.target.length = x.graph.edgeCount)) &&
      x.graph.checkLegal x.initial)

private def decideConfig (x : Input) : Bool := guard x && search x

private theorem computableInPolyTime_inputGraph :
    ComputableInPolyTime (fun x : Input => x.graph) encAndOrNCL encAndOrGraph := by
  fun_prop

private theorem computableInPolyTime_inputStart :
    ComputableInPolyTime (fun x : Input => x.initial) encAndOrNCL encBits := by
  have h : ComputableInPolyTime (fun x : Input => x.initial) encAndOrNCL (encList encBool) := by
    fun_prop
  exact (bits_encList_polyTime encBool).2.comp h

private theorem computableInPolyTime_inputTarget :
    ComputableInPolyTime (fun x : Input => x.target) encAndOrNCL encBits := by
  have h : ComputableInPolyTime (fun x : Input => x.target) encAndOrNCL (encList encBool) := by
    fun_prop
  exact (bits_encList_polyTime encBool).2.comp h

private theorem computableInPolySpace_search :
    ComputableInPolySpace search encAndOrNCL encBool := by
  have hg := computableInPolyTime_inputGraph
  have hs := computableInPolyTime_inputStart
  have ht := computableInPolyTime_inputTarget
  have hn : ComputableInPolyTime (fun x : Input => x.initial.length) encAndOrNCL encUnary := by
    fun_prop
  have hpad : ComputableInPolyTime
      (fun x : Input => List.replicate (x.initial.length - x.target.length) false)
      encAndOrNCL encBits := by fun_prop
  have hd : ComputableInPolyTime (fun x : Input => fit x.initial.length x.target)
      encAndOrNCL encBits := by
    unfold fit
    fun_prop
  have hedge : ComputableInPolyTime
      (fun q : (List Bool × List Bool) × Input => q.2.graph.checkStep q.1.1 q.1.2)
      (encPair (encPair encBits encBits) encAndOrNCL) encBool := by
    have := hg.comp (ComputableInPolyTime.snd (encPair encBits encBits) encAndOrNCL)
    fun_prop
  exact ComputableInPolySpace.reach (edge := fun x => x.graph.checkStep) (.of_polyTime hn)
    (.of_polyTime hn) (.of_polyTime hs) (.of_polyTime hd) (.of_polyTime hedge)
    fun x => ⟨rfl, length_fit x.initial.length x.target⟩

private theorem computableInPolyTime_guard : ComputableInPolyTime guard encAndOrNCL encBool := by
  have hg := computableInPolyTime_inputGraph
  have hs := computableInPolyTime_inputStart
  have ht := computableInPolyTime_inputTarget
  have hw : ComputableInPolyTime (fun x : Input => x.graph.edgeCount) encAndOrNCL encNat := by
    fun_prop
  have hns : ComputableInPolyTime (fun x : Input => x.initial.length) encAndOrNCL encUnary := by
    fun_prop
  have hnt : ComputableInPolyTime (fun x : Input => x.target.length) encAndOrNCL encUnary := by
    fun_prop
  have hbs := ComputableInPolyTime.unary_to_binary.comp hns
  have hbt := ComputableInPolyTime.unary_to_binary.comp hnt
  have hsizeS := hbs.decide_eq' hw
  have hsizeT := hbt.decide_eq' hw
  have hv := AndOrGraph.computableInPolyTime_checkValid.comp hg
  have hl := AndOrGraph.computableInPolyTime_checkLegal hg hs
  exact ComputableInPolyTime.bool_and' hv
    (ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hsizeS hsizeT) hl)

private theorem decideConfig_eq_true_iff (x : Input) : decideConfig x = true ↔ x ∈ AndOrNCL := by
  simp only [decideConfig, guard, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hv, ⟨hs, ht⟩, hl⟩, hr⟩
    have hv := (AndOrGraph.checkValid_eq_true_iff x.graph).1 hv
    refine ⟨hv, hs, ht, (AndOrGraph.checkLegal_eq_true_iff _ hv.1 _).1 hl, ?_⟩
    unfold search at hr
    rw [fit_eq _ _ (ht.trans hs.symm), hs] at hr
    exact (AndOrGraph.reach_eq_true_iff _ hv.1 _ _ hs ht).1 hr
  · rintro ⟨hv, hs, ht, hl, hr⟩
    refine ⟨⟨(AndOrGraph.checkValid_eq_true_iff _).2 hv, ⟨hs, ht⟩,
      (AndOrGraph.checkLegal_eq_true_iff _ hv.1 _).2 hl⟩, ?_⟩
    unfold search
    rw [fit_eq _ _ (ht.trans hs.symm), hs]
    exact (AndOrGraph.reach_eq_true_iff _ hv.1 _ _ hs ht).2 hr

/-- Configuration-to-configuration reachability on AND/OR multigraphs is in PSPACE,
including graphs with loops. -/
theorem AndOrNCL_mem_PSPACE : AndOrNCL ∈ PSPACE encAndOrNCL := by
  have hand : ComputableInPolyTime (fun p : Bool × Bool => p.1 && p.2)
      (encPair encBool encBool) encBool := by fun_prop
  have hf : ComputableInPolySpace decideConfig encAndOrNCL encBool :=
    (ComputableInPolySpace.of_polyTime hand).comp
      ((ComputableInPolySpace.of_polyTime computableInPolyTime_guard).prod
        computableInPolySpace_search)
  exact ⟨decideConfig, hf, fun x => (decideConfig_eq_true_iff x).symm⟩

end Cslib.Complexity.NCL
