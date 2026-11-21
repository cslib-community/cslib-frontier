/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.OffsetReader

/-! # Ordinary-import clients of the runtime-offset ID callee -/

set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingOffsetReader
open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace Turing.DoubleCounting
open OffsetReader

-- Offset registers use binary encNat; the canonical ID word remains external and unchanged.
example (r : Request) : encRequest r =
    frame (encNat r.offset) ++ VertexParameters.encParameters r.parameters := rfl
example (s : Context) : encContext s =
    frame (encNat s.offset) ++ VertexReader.encState s.inner := rfl

-- Runtime preparation validates width and does not copy the supplied word.
example : load ⟨3, ⟨3, 2⟩⟩ = some ⟨3, ⟨3, 2, 0, 0, false⟩⟩ := rfl
example : load ⟨3, ⟨4, 2⟩⟩ = none := rfl
example : load ⟨100, ⟨0, 0⟩⟩ = some ⟨100, ⟨0, 0, 0, 0, false⟩⟩ := rfl

private def initial : Context := ⟨3, ⟨3, 2, 0, 0, false⟩⟩

-- Actual original-word queries are 3 and 4; bits before/after that ID do not affect its value.
example : callee.query (callee.runFrom [true, true, true, true, false, true] initial 0) = 3 := rfl
example : callee.query (callee.runFrom [true, true, true, true, false, true] initial 1) = 4 := rfl
example : VertexReader.result
    (callee.runFrom [true, true, true, true, false, true] initial 2).inner = some 2 := by
  decide +kernel
example : VertexReader.result
    (callee.runFrom [true, true, true, false, false, true] initial 2).inner = some 0 := by
  decide +kernel
example : VertexReader.result
    (callee.runFrom [false, false, false, true, true] initial 2).inner = none := by decide +kernel
example : VertexReader.result
    (callee.runFrom [true, true, true, false] initial 2).inner = none := by decide +kernel
example : VertexReader.result (callee.runFrom [] initial 2).inner = none := by decide +kernel
example : VertexReader.result
    (callee.runFrom [false] ⟨100, ⟨3, 2, 0, 0, false⟩⟩ 2).inner = none := by decide +kernel
example : VertexReader.result
    (callee.runFrom [] ⟨0, ⟨0, 0, 0, 0, false⟩⟩ 0).inner = none := by decide +kernel
example : VertexReader.result
    (callee.runFrom [true, false] ⟨1, ⟨1, 1, 0, 0, false⟩⟩ 1).inner = some 0 := by decide +kernel
example : VertexReader.result
    (callee.runFrom [true, false, true, true] ⟨1, ⟨4, 3, 0, 0, false⟩⟩ 3).inner = some 3 := by
  decide +kernel

-- Arbitrary runtime context and suffix: clients consume the canonical codec bridge directly.
example (r : Request) (s : Context) (h : load r = some s) (w : List Bool) :
    (VertexReader.result (callee.runFrom w s r.parameters.dimension.size).inner).map
      (fun n => (n, w.drop (r.offset + r.parameters.dimension.size))) =
    (Cslib.DoubleCounting.Scan.Binary.readVertex (N := r.parameters.dimension)
      (w.drop r.offset)).map (fun p => (p.1.val, p.2)) := suffix_loaded r s h w

-- The bridge rejects missing bits and out-of-range values for arbitrary runtime inputs.
example (r : Request) (s : Context) (h : load r = some s) (w : List Bool)
    (hshort : (w.drop r.offset).length < r.parameters.dimension.size) :
    VertexReader.result (callee.runFrom w s r.parameters.dimension.size).inner = none := by
  rw [result_loaded r s h]
  have hlen : ((w.drop r.offset).take r.parameters.dimension.size).length ≠
      r.parameters.dimension.size := by
    rw [List.length_take]
    omega
  simp only [Cslib.DoubleCounting.Scan.Binary.decodeVertex, hlen, ite_false, Option.map_none]

example (r : Request) (s : Context) (h : load r = some s) (w : List Bool)
    (hrange : r.parameters.dimension ≤ Cslib.BitString.binaryValue
      ((w.drop r.offset).take r.parameters.dimension.size)) :
    VertexReader.result (callee.runFrom w s r.parameters.dimension.size).inner = none := by
  rw [result_loaded r s h,
    Cslib.DoubleCounting.Scan.Binary.decodeVertex_out_of_range _ hrange]
  rfl

-- Canonical ID plus an arbitrary suffix is recovered without re-proving the codec.
example (r : Request) (s : Context) (h : load r = some s) (w rest : List Bool)
    (v : Fin r.parameters.dimension)
    (hw : w.drop r.offset = Cslib.DoubleCounting.Scan.Binary.vertex v ++ rest) :
    (VertexReader.result (callee.runFrom w s r.parameters.dimension.size).inner).map
      (fun n => (n, w.drop (r.offset + r.parameters.dimension.size))) = some (v.val, rest) := by
  rw [suffix_loaded r s h,
    (Cslib.DoubleCounting.Scan.Binary.readVertex_eq_some_iff _ rest v).mpr hw]
  rfl

private def caller : QueryMachine Bool where
  init := false
  query _ := 0
  next p := p.1
  emit _ := []
  halted b := b
  finish _ := []

private def ask (_ : Bool) : Option Context := some initial
private def resume (_ : Bool) (_ : Context) : Bool := true

-- A real same-input call returns after entry + two reads + return, for any supplied word.
example (w : List Bool) :
    (caller.withCalls callee ask resume).runFrom w (.inl false) 4 = .inl true := by
  have hclock : (3 : ℕ).size + 2 = 4 := by decide +kernel
  simpa only [resume, hclock] using
    call_loaded caller ask resume ⟨3, ⟨3, 2⟩⟩ initial rfl false w rfl rfl

-- Existing native call composition consumes the actual offset-callee certificates.
example : ComputableInSpace (caller.withCalls callee ask resume).query
    (QueryMachine.encWithCalls encBool encContext) encNat
    (fun s => (QueryMachine.encWithCalls encBool encContext s).length) := by
  exact QueryMachine.withCalls_query_inSpace caller callee ask resume encBool encContext
    (budget_const 0 (.refl _))
    (QueryMachine.withOffset_query_inSpace (VertexReader.machine 0) VertexReader.encState
      (VertexReader.query_inSpace 0)) (budget_const (some initial) (.refl _))

example : ComputableInSpace (caller.withCalls callee ask resume).next
    (QueryMachine.encStateRead (QueryMachine.encWithCalls encBool encContext))
    (QueryMachine.encWithCalls encBool encContext)
    (fun s =>
      (QueryMachine.encStateRead (QueryMachine.encWithCalls encBool encContext) s).length) := by
  exact QueryMachine.withCalls_next_inSpace caller callee ask resume encBool encContext
    (fst encBool (encOption encBool))
    (QueryMachine.withOffset_next_inSpace (VertexReader.machine 0) VertexReader.encState
      (VertexReader.next_inSpace 0))
    (QueryMachine.withOffset_halted_inSpace (VertexReader.machine 0) VertexReader.encState
      (VertexReader.halted_inSpace 0))
    (budget_const (some initial) (.refl _)) (budget_const true (.refl _))

-- Query-machine call steps retain the suspended caller as well as the binary offset/ID state.
example (w : List Bool) (t : ℕ) (ht : t ≤ (3 : ℕ).size + 2) :
    (QueryMachine.encWithCalls encBool encContext
      ((caller.withCalls callee ask resume).runFrom w (.inl false) t)).length ≤
      2 * 1 + (2 * (Nat.log2 3 + 1) + 8 * (Nat.log2 3 + 1) + 10) + 2 := by
  exact call_length_le caller ask resume ⟨3, ⟨3, 2⟩⟩ initial rfl false w encBool 1
    rfl rfl (by decide +kernel) (by change 1 ≤ 1; omega) t ht

-- Actual native runtime preparation uses the supplied request encoding.
example : ComputableInSpace load encRequest (encOption encContext)
    (fun r => (encRequest r).length) := load_inSpace

-- Generated record projection certificates expose the binary offset by name.
example : ComputableInSpace (QueryMachine.Located.offset (σ := VertexReader.State))
    encContext encNat (fun s => (encContext s).length) :=
  QueryMachine.encLocated_offset_budget VertexReader.State VertexReader.encState
    (of_inO (ComputableInO.of_eq fun _ => rfl))

end CslibFrontierTests.DoubleCountingOffsetReader
