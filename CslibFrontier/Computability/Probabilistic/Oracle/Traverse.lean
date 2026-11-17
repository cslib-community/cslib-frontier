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
# Strict oracle PPT traversal of external queries

Sending each word of an efficiently computed list to the external oracle, and keeping an
efficiently computed prefix of each reply, is strict oracle PPT. This is the oracle counterpart of
`Cslib.Probability.IsPPTOn.mapM`, where each element runs a closed PPT program: here each element
makes one charged external call (`Cslib.Probability.IsOraclePPTOn.query_take'`). The traversal is
realized as a bounded loop over the remaining requests whose state grows by at most one framed
reply prefix per step.

## Main results

* `Cslib.Probability.IsOraclePPTOn.mapM_query_take`: the traversal `List.mapM` of truncated
  external queries is strict oracle PPT.
-/

public section

namespace Cslib.Probability

open Turing.MultiTapeTM

variable {Operation α : Type} [DecidableEq Operation] [Finite Operation] {input : α ↪ List Bool}

/-- One step of the query traversal: send the next request on channel `op` and append the
`limit`-bit prefix of its reply. -/
private def mapQueryTakeStep (op : Operation) (limit : ℕ)
    (state : List (List Bool) × List (List Bool)) :
    WordOracleComp Operation (List (List Bool) × List (List Bool)) :=
  (fun reply => (state.1.tail, state.2 ++ [reply])) <$>
    (List.take limit <$>
      ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool)
        (op, state.1.headD []))

omit [DecidableEq Operation] [Finite Operation] in
private theorem iterate_mapQueryTakeStep (op : Operation) (limit : ℕ)
    (xs acc : List (List Bool)) :
    Prod.snd <$> OracleComp.iterate xs.length (mapQueryTakeStep op limit) (xs, acc) =
      (acc ++ ·) <$> xs.mapM (fun x => List.take limit <$>
        ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool) (op, x)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, OracleComp.iterate_succ_bind, mapQueryTakeStep,
      List.headD_cons, List.tail_cons, List.mapM_cons, map_bind, bind_map_left, ih,
      List.append_assoc, List.singleton_append]
    simp only [map_pure, bind_pure_comp]

/-- Querying channel `op` on each word of an efficiently computed list, in order, and keeping the
first `limit a` bits of each reply is strict oracle PPT. -/
theorem IsOraclePPTOn.mapM_query_take (op : Operation) {list : α → List (List Bool)}
    {limit : α → ℕ} (hlist : ComputableInPolyTime list input (encList encBits))
    (hlimit : ComputableInPolyTime limit input encUnary) :
    IsOraclePPTOn input (encList encBits) (fun a =>
      (list a).mapM fun x => List.take (limit a) <$>
        ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool) (op, x)) := by
  let stateEncoding : List (List Bool) × List (List Bool) ↪ List Bool :=
    encPair (encList encBits) (encList encBits)
  have hcount : ComputableInPolyTime (fun a => (list a).length) input encUnary :=
    (ComputableInPolyTime.length_list encBits).comp hlist
  have hinitial : ComputableInPolyTime (fun a => (list a, ([] : List (List Bool))))
      input stateEncoding :=
    hlist.prod (ComputableInPolyTime.const [])
  have hstep : IsOraclePPTOn (encPair input stateEncoding) stateEncoding
      (fun p : α × List (List Bool) × List (List Bool) =>
        mapQueryTakeStep op (limit p.1) p.2) := by
    unfold mapQueryTakeStep
    exact (IsOraclePPTOn.query_take' op (by fun_prop) (by fun_prop)).map_with'
      (f := fun (p : α × List (List Bool) × List (List Bool)) reply =>
        (p.2.1.tail, p.2.2 ++ [reply]))
      (by fun_prop)
  have hpoly : PolyBounded (fun a => (input a).length) (fun a => 2 * limit a + 2) := by
    have h1 : ComputableInPolyTime (fun a => 2 * limit a + 2) input encUnary := by fun_prop
    simpa only [encUnary_apply, List.length_replicate] using h1.polyBounded_length
  have hloop : IsOraclePPTOn input stateEncoding
      (fun a => OracleComp.iterate (list a).length (mapQueryTakeStep op (limit a))
        (list a, [])) := by
    refine IsOraclePPTOn.iterateWith_of_bounded_growth' hcount hinitial hstep hpoly ?_
    intro a state next hnext
    unfold mapQueryTakeStep at hnext
    obtain ⟨reply, hreply, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
    have htailLen : (encList encBits state.1.tail).length ≤ (encList encBits state.1).length :=
      ((List.tail_sublist state.1).flatMap (frame ∘ encBits)).length_le
    have htake : (raw.take (limit a)).length ≤ limit a := List.length_take_le _ _
    simp only [stateEncoding, length_encPair, encList_append, encList_cons, encList_nil,
      List.append_nil, List.length_append, length_frame, encBits_apply]
    omega
  simpa only [iterate_mapQueryTakeStep, List.nil_append, id_map'] using
    hloop.map' (ComputableInPolyTime.snd (encList encBits) (encList encBits))

end Cslib.Probability
