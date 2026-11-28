/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Strict oracle PPT list traversal

Running an oracle PPT program on each element of an efficiently computed list is strict oracle
PPT when every encoded result has an efficiently computed length bound from the original input.
The traversal maintains the remaining items and the results in order. Its state grows by at most
one framed result per step, including under arbitrary oracle replies. Sending a list of queries
and keeping a prefix of each reply is a specialization.

## Main results

* `Cslib.Probability.IsOraclePPTOn.mapM_with_of_bounded_output`: certify a traversal whose
  per-item program can read the original input.
* `Cslib.Probability.IsOraclePPTOn.mapM_query_take`: the traversal `List.mapM` of truncated
  external queries is strict oracle PPT.
-/

public section

namespace Cslib.Probability

open Turing.MultiTapeTM

variable {Operation α Item Result : Type} [DecidableEq Operation] {input : α ↪ List Bool}

private def mapMStep (fallback : Item) (program : Item → WordOracleComp Operation Result)
    (state : List Item × List Result) : WordOracleComp Operation (List Item × List Result) :=
  (fun result => (state.1.tail, state.2 ++ [result])) <$> program (state.1.headD fallback)

omit [DecidableEq Operation] in
private theorem iterate_mapMStep (fallback : Item)
    (program : Item → WordOracleComp Operation Result) (xs : List Item) (acc : List Result) :
    Prod.snd <$> OracleComp.iterate xs.length (mapMStep fallback program) (xs, acc) =
      (acc ++ ·) <$> xs.mapM program := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, OracleComp.iterate_succ_bind, mapMStep, List.headD_cons,
      List.tail_cons, List.mapM_cons, map_bind, bind_map_left, ih, List.append_assoc,
      List.singleton_append]
    simp only [map_pure, bind_pure_comp]

/-- Traverse an efficiently computed list with a strict oracle PPT program that can read the
original input. An efficiently computed bound covers every supported encoded result, including
under arbitrary oracle replies. The fallback only totalizes the loop body. -/
theorem IsOraclePPTOn.mapM_with_of_bounded_output {item : Item ↪ List Bool}
    {output : Result ↪ List Bool} (fallback : Item) {list : α → List Item}
    {program : α → Item → WordOracleComp Operation Result} {bound : α → ℕ}
    (hlist : ComputableInPolyTime list input (encList item))
    (hprogram : IsOraclePPTOn (encPair input item) output (Function.uncurry program))
    (hbound : ComputableInPolyTime bound input encUnary)
    (houtput : ∀ a x r, r ∈ OracleComp.support (program a x) → (output r).length ≤ bound a) :
    IsOraclePPTOn input (encList output) (fun a => (list a).mapM (program a)) := by
  let stateEncoding := encPair (encList item) (encList output)
  have hstep : IsOraclePPTOn (encPair input stateEncoding) stateEncoding
      (fun p : α × List Item × List Result => mapMStep fallback (program p.1) p.2) :=
    (hprogram.preprocess <| (ComputableInPolyTime.fst _ _).prod <|
      (ComputableInPolyTime.headD fallback).comp <|
        (ComputableInPolyTime.fst (encList item) (encList output)).comp
          (ComputableInPolyTime.snd input stateEncoding)).map_with
      (f := fun (p : α × List Item × List Result) result => (p.2.1.tail, p.2.2 ++ [result]))
      (by fun_prop)
  have hpoly : PolyBounded (fun a => (input a).length) (fun a => 2 * bound a + 2) := by
    have h1 : ComputableInPolyTime (fun a => 2 * bound a + 2) input encUnary := by fun_prop
    simpa only [encUnary_apply, List.length_replicate] using h1.polyBounded_length
  have hloop : IsOraclePPTOn input stateEncoding
      (fun a => OracleComp.iterate (list a).length (mapMStep fallback (program a))
        (list a, [])) := by
    refine IsOraclePPTOn.iterateWith_of_bounded_growth
      ((ComputableInPolyTime.length_list item).comp hlist) (hlist.prod (.const []))
      hstep hpoly fun a state next hnext => ?_
    obtain ⟨result, hresult, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    have htailLen : (encList item state.1.tail).length ≤ (encList item state.1).length :=
      ((List.tail_sublist state.1).flatMap (frame ∘ item)).length_le
    have hlen := houtput a (state.1.headD fallback) result hresult
    simp only [stateEncoding, length_encPair, encList_append, encList_cons, encList_nil,
      List.append_nil, List.length_append, length_frame]
    omega
  simpa only [iterate_mapMStep, List.nil_append, id_map'] using
    hloop.map (.snd (encList item) (encList output))

/-- Querying channel `op` on each word of an efficiently computed list, in order, and keeping the
first `limit a` bits of each reply is strict oracle PPT. -/
theorem IsOraclePPTOn.mapM_query_take [Finite Operation] (op : Operation)
    {list : α → List (List Bool)} {limit : α → ℕ}
    (hlist : ComputableInPolyTime list input (encList encBits))
    (hlimit : ComputableInPolyTime limit input encUnary) :
    IsOraclePPTOn input (encList encBits) (fun a =>
      (list a).mapM fun x => List.take (limit a) <$>
        ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool) (op, x)) := by
  refine IsOraclePPTOn.mapM_with_of_bounded_output [] hlist
    (IsOraclePPTOn.query_take op (.snd input encBits) (hlimit.comp (.fst input encBits))) hlimit
    fun _ _ _ hresult => ?_
  obtain ⟨_, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
  exact List.length_take_le _ _

end Cslib.Probability
