/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.Layered
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Tactic.EncLen
import Mathlib.Tactic.Ring

/-!
# Read-only adjacency queries for the layered configuration graph

Labels below the original vertex count encode original configuration IDs; the vertex count
itself encodes the accepting sink. The adjacency callback takes binary dimensions and two
layer/label pairs, together with the single input symbol requested at the original source
configuration. Its native workspace is linear in these short arguments, without a copy of
the original word. This supplies the local query component of the reduction in #6747.
-/

public section

namespace Cslib.Complexity.STCON

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace
  _root_.Turing.MultiTapeNTM.ConfigurationGraph

/-- Short binary parameters of one layered adjacency query. The source input word is absent. -/
structure LayeredQuery where
  /-- Configuration-register radix. -/
  radix : ℕ
  /-- Length of the read-only source input. -/
  inputLength : ℕ
  /-- Source layer. -/
  fromLayer : ℕ
  /-- Original source ID, or the original vertex count for the accepting sink. -/
  fromLabel : ℕ
  /-- Target layer. -/
  toLayer : ℕ
  /-- Original target ID, or the original vertex count for the accepting sink. -/
  toLabel : ℕ
  /-- The externally read source-input symbol. -/
  symbol : Option Bool

/-- Six binary naturals followed by the optional bit, in field order. Every natural is framed;
the last field uses the option tag and, when present, its Boolean payload. -/
enc_structure encLayeredQuery : LayeredQuery where
  radix : encNat, inputLength : encNat, fromLayer : encNat, fromLabel : encNat,
  toLayer : encNat, toLabel : encNat, symbol : (encOption encBool)

variable {k : ℕ} {State : Type} [Fintype State]

/-- The local adjacency algorithm. An original transition or a waiting step advances one
layer; a marked original configuration can instead enter the accepting sink. -/
@[expose] noncomputable def layeredEdgeQuery (ntm : MultiTapeNTM k Bool State)
    (q : LayeredQuery) : Bool :=
  let N := vertexBound (k := k) q.radix
  decide (q.toLayer = q.fromLayer + 1) && decide (q.fromLayer < N) &&
    decide (q.fromLabel ≤ N) && decide (q.toLabel ≤ N) &&
    (decide (q.fromLabel = q.toLabel) ||
      if q.fromLabel = N then false
      else if q.toLabel = N then bad (k := k) (State := State) q.radix q.inputLength q.fromLabel
      else edgeWithSymbol ntm q.radix q.inputLength q.fromLabel q.toLabel q.symbol)

/-- The one input query needed by the callback. Sink vertices query the absent bit just past
the word; their adjacency test does not use the returned symbol. -/
@[expose] noncomputable def layeredQueryIndex (q : LayeredQuery) : ℕ :=
  if q.fromLabel < vertexBound (k := k) q.radix then queryIndex (k := k) q.radix q.fromLabel
  else q.inputLength

/-- Construct a pending query from binary dimensions and vertex coordinates, without
reading the original word. The symbol slot is a placeholder filled by the one-read callee. -/
@[expose] noncomputable def layeredQueryRequest {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool)
    (a b : LayeredGraphVertex (configurationInstance ntm c w)) : LayeredQuery :=
  ⟨radix (radixExponent State c) w.length, w.length,
    a.val.layer, a.val.vertex.val, b.val.layer, b.val.vertex.val, none⟩

/-- Mathematical query parameters with the symbol obtained from the original word. Native
execution of this read is supplied by the uniform callee in `STCON.LayeredCallback`. -/
@[expose] noncomputable def layeredQuery {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool)
    (a b : LayeredGraphVertex (configurationInstance ntm c w)) : LayeredQuery :=
  let q := layeredQueryRequest ntm c w a b
  {q with symbol := w[layeredQueryIndex (k := k) q]?}

/-- The read-only callback agrees with the simple finite layered graph, including sink and
waiting edges. -/
theorem layeredQuery_agrees (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool)
    (a b : LayeredGraphVertex (configurationInstance ntm c w)) :
    layeredEdgeQuery ntm (layeredQuery ntm c w a b) = true ↔
      layeredRelation (configurationInstance ntm c w) a b := by
  let B := radix (radixExponent State c) w.length
  let N := vertexBound (k := k) B
  have hu : a.val.vertex.val ≤ N := Nat.le_of_lt_succ a.val.vertex.isLt
  have hv : b.val.vertex.val ≤ N := Nat.le_of_lt_succ b.val.vertex.isLt
  have hvalid : valid (k := k) (State := State) B w.length N = false := by
    simp [valid, N]
  have he (v : ℕ) (symbol : Option Bool) :
      edgeWithSymbol ntm B w.length N v symbol = false := by
    simp [edgeWithSymbol, hvalid]
  have hb : bad (k := k) (State := State) B w.length N = false := by
    simp [bad, hvalid]
  have hswap (u v : ℕ) : u = v ↔ v = u := eq_comm
  have huLt : a.val.vertex.val < N ↔ a.val.vertex.val ≠ N := by omega
  have hvLt : b.val.vertex.val < N ↔ b.val.vertex.val ≠ N := by omega
  by_cases hu' : a.val.vertex.val = N <;> by_cases hv' : b.val.vertex.val = N <;>
    simp [layeredEdgeQuery, layeredQuery, layeredQueryRequest, layeredQueryIndex, layeredRelation,
      Relation.LayeredVertex.Step, Relation.reflGen_iff, STCONInstance.Adj, configurationInstance,
      sinkAdj, hu, hv, huLt, hvLt, hu', hv', he, hb, B, N, Fin.ext_iff, and_assoc, hswap]


/-- Native evaluation of the adjacency callback uses linear workspace in the short binary
query parameters. The source word is read externally, not stored in this argument. -/
theorem layeredEdgeQuery_inSpace (ntm : MultiTapeNTM k Bool State) :
    ComputableInSpace (layeredEdgeQuery ntm) encLayeredQuery encBool
      (fun q => (encLayeredQuery q).length) := by
  have hi := budget_id (enc := encLayeredQuery) (S := fun q => (encLayeredQuery q).length) (.refl _)
  have hB := encLayeredQuery_radix_budget hi
  have hn := encLayeredQuery_inputLength_budget hi
  have hi₀ := encLayeredQuery_fromLayer_budget hi
  have hu := encLayeredQuery_fromLabel_budget hi
  have hi₁ := encLayeredQuery_toLayer_budget hi
  have hv := encLayeredQuery_toLabel_budget hi
  have hs := encLayeredQuery_symbol_budget hi
  have hN := vertexBound_budget (k := k) hB
  have he := edgeWithSymbol_budget ntm hB hn hu hv hs
  have hb := bad_budget (k := k) (State := State) hB hn hu
  have hlocal := budget_boolOr (budget_natEq hu hv)
    (budget_iteProp (budget_natEq hu hN) (budget_const false)
      (budget_iteProp (budget_natEq hv hN) hb he))
  exact budget_boolAnd (budget_boolAnd (budget_boolAnd (budget_boolAnd
    (budget_natEq hi₁ (budget_natSucc hi₀)) (budget_natLt hi₀ hN))
    (budget_natLe hu hN)) (budget_natLe hv hN)) hlocal

/-- Computing the requested input position has the same short-argument workspace bound. -/
theorem layeredQueryIndex_inSpace :
    ComputableInSpace (layeredQueryIndex (k := k)) encLayeredQuery encNat
      (fun q => (encLayeredQuery q).length) := by
  have hi := budget_id (enc := encLayeredQuery) (S := fun q => (encLayeredQuery q).length) (.refl _)
  have hB := encLayeredQuery_radix_budget hi
  have hu := encLayeredQuery_fromLabel_budget hi
  exact budget_iteProp
    (budget_natLt hu (vertexBound_budget (k := k) hB))
    (queryIndex_budget hB hu) (encLayeredQuery_inputLength_budget hi)

private theorem query_length_le (q : LayeredQuery) (L : ℕ)
    (hB : (encNat q.radix).length ≤ L) (hn : (encNat q.inputLength).length ≤ L)
    (hi : (encNat q.fromLayer).length ≤ L) (hu : (encNat q.fromLabel).length ≤ L)
    (hj : (encNat q.toLayer).length ≤ L) (hv : (encNat q.toLabel).length ≤ L) :
    (encLayeredQuery q).length ≤ 12 * L + 8 := by
  have hs : (encOption encBool q.symbol).length ≤ 2 := by
    cases q.symbol with
    | none => decide
    | some b => cases b <;> decide
  enc_len [encLayeredQuery_apply, encLayeredQueryFields]

/-- Polynomially bounded binary dimensions, layers and labels give a logarithmic-length
callback argument. Together with the native linear-workspace certificates, this bounds each
adjacency query by logarithmic workspace in the original input length. -/
theorem layeredQuery_length_le_log (q : LayeredQuery) (n d : ℕ)
    (hB : q.radix ≤ (n + 2) ^ d) (hn : q.inputLength ≤ (n + 2) ^ d)
    (hi : q.fromLayer ≤ (n + 2) ^ d) (hu : q.fromLabel ≤ (n + 2) ^ d)
    (hj : q.toLayer ≤ (n + 2) ^ d) (hv : q.toLabel ≤ (n + 2) ^ d) :
    (encLayeredQuery q).length ≤ 12 * (d + 1) * (Nat.log2 (n + 1) + 1) + 8 := by
  have hlen (m : ℕ) (hm : m ≤ (n + 2) ^ d) :
      (encNat m).length ≤ (d + 1) * (Nat.log2 (n + 1) + 1) :=
    length_encNat_le_of_le_pow (N := n + 1) hm
  calc
    _ ≤ 12 * ((d + 1) * (Nat.log2 (n + 1) + 1)) + 8 :=
      query_length_le q _ (hlen _ hB) (hlen _ hn) (hlen _ hi) (hlen _ hu)
        (hlen _ hj) (hlen _ hv)
    _ = _ := by ring

/-- Queries to actual graph vertices have logarithmic encoded length, uniformly over all
vertex pairs, including the final layer and accepting sink. -/
theorem length_layeredQuery_le_log (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool)
    (a b : LayeredGraphVertex (configurationInstance ntm c w)) (symbol : Option Bool) :
    (encLayeredQuery {layeredQueryRequest ntm c w a b with symbol := symbol}).length ≤
      12 * (radixExponent State c * Fintype.card (Register k) + 1) *
        (Nat.log2 (w.length + 1) + 1) + 8 := by
  let D := radixExponent State c
  have hD : 1 ≤ D := by dsimp only [D, radixExponent]; omega
  have hcard : 0 < Fintype.card (Register k) := Fintype.card_pos_iff.mpr ⟨.inputPos⟩
  have hB : radix D w.length ≤ vertexBound (k := k) (radix D w.length) :=
    Nat.le_self_pow (Nat.ne_of_gt hcard) _
  have hn : w.length ≤ vertexBound (k := k) (radix D w.length) :=
    ((Nat.le_add_right w.length 2).trans (Nat.le_self_pow (by omega) _)).trans hB
  have hu : a.val.vertex.val ≤ vertexBound (k := k) (radix D w.length) :=
    Nat.le_of_lt_succ a.val.vertex.isLt
  have hv : b.val.vertex.val ≤ vertexBound (k := k) (radix D w.length) :=
    Nat.le_of_lt_succ b.val.vertex.isLt
  apply layeredQuery_length_le_log
  · simpa only [layeredQueryRequest, D, vertexBound_eq_pow] using hB
  · simpa only [layeredQueryRequest, D, vertexBound_eq_pow] using hn
  · simpa only [layeredQueryRequest, D, configurationInstance, Nat.add_sub_cancel,
      vertexBound_eq_pow] using a.property
  · simpa only [layeredQueryRequest, D, vertexBound_eq_pow] using hu
  · simpa only [layeredQueryRequest, D, configurationInstance, Nat.add_sub_cancel,
      vertexBound_eq_pow] using b.property
  · simpa only [layeredQueryRequest, D, vertexBound_eq_pow] using hv


end Cslib.Complexity.STCON
