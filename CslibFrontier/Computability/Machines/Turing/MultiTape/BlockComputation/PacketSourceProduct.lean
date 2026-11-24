/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.PacketTerms
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.BinarySlice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryComparison
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.ShortInput
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD

/-!
# Fixed-size repetition of packet source powers

For a packet with `N` dense modes and creation precision `p`, the source-mode powers become one
product over `N * p` positions. Position `k * p + j` contributes mode `k` exactly when it is a
source mode and `j < β[k]`; otherwise it contributes one. When every exponent is at most `p`,
the product is the value of the actual native `sourceProduct`. The tree size therefore depends
only on short binary metadata, rather than on an exponent loaded from the long word.

The native selection guard uses one binary list lookup and one linear binary comparison. Its
time and space are linear in the exponent encoding and polynomial in the short header and the
binary length of that encoding. Precision zero, missing exponents and out-of-range positions
have total behavior. The guard remains efficient on oversized exponents, although the product
identity requires the stated exponent bound. Evaluating the selected mode value is separate
arithmetic input work tracked in #4741.

This is an original representation and machine-bound argument for the packet compiler.

## Main results

* `Turing.MultiTapeTM.PacketSourceProduct.prod_factor_eq_sourceProduct`: bounded source powers
  equal the fixed-size product.
* `Turing.MultiTapeTM.PacketSourceProduct.exists_selected_inO`: the selection guard has a
  linear long-word charge and polynomial short-data charge.
-/

public section

namespace Turing.MultiTapeTM.PacketSourceProduct

open Cslib Cslib.Circuits.Frontier Cslib.Circuits.Frontier.NativePacket
open Cslib.Circuits.Frontier.TensorNetwork Finset GaloisRingArith ComputableInPolyTime

/-- Binary source-product dimensions and position, with a unary symbol-coordinate index. -/
structure Header where
  /-- Number of dense modes. -/
  modes : ℕ
  /-- Fixed number of repetition positions per mode. -/
  precision : ℕ
  /-- Symbol coordinate determining source membership. -/
  coordinate : ℕ
  /-- Number of exponent modes per tile. -/
  perTile : ℕ
  /-- Whether the first packet symbol is the child group. -/
  first : Bool
  /-- Whether the second packet symbol is the child group. -/
  second : Bool
  /-- Position in the fixed product, in mode-major order. -/
  vertex : ℕ
  deriving DecidableEq

/-- Declaration-order fields, framed except for the last binary position. Only the coordinate
index is unary; mode count, precision, modes per tile and position are binary. -/
enc_structure encHeader : Header where
  modes : encNat, precision : encNat, coordinate : encUnary, perTile : encNat,
  first : encBool, second : encBool, vertex : encNat

/-- Short source-product metadata followed by the dense binary exponent word. -/
structure Input where
  /-- The fixed dimensions and requested repetition position. -/
  header : Header
  /-- Dense exponents; a missing exponent is zero. -/
  exponents : List ℕ
  deriving DecidableEq

/-- Framed short metadata followed by the list of framed binary exponent entries. -/
enc_structure encInput : Input where header : encHeader, exponents : (encList encNat)

/-- The polynomial size parameter includes the exponent encoding only through its binary length. -/
@[expose] def shortSize (a : Input) : ℕ :=
  (encHeader a.header).length + (encList encNat a.exponents).length.size + 1

/-- Decide whether this product position contributes its mode value or the identity. -/
@[expose] def selected (a : Input) : Bool :=
  decide (a.header.vertex < a.header.modes * a.header.precision) &&
    modeSources a.header.coordinate a.header.first a.header.second
      (a.header.vertex / a.header.precision / a.header.perTile) &&
    decide (a.header.vertex % a.header.precision <
      a.exponents.getD (a.header.vertex / a.header.precision) 0)

/-- The short request corresponding to one position of an existing packet's source product. -/
@[expose] def ofPacket (c : PacketCtx) (β : List ℕ) (vertex : ℕ) : Input :=
  ⟨⟨c.tiles * c.nb, c.p, c.i, c.nb, c.e₁, c.e₂, vertex⟩, β⟩

/-- One repeated mode value, or the multiplicative identity at an inactive position. -/
@[expose] noncomputable def factor (c : PacketCtx) (β : List ℕ) (vertex : ℕ) : Ring c.p c.fl :=
  if selected (ofPacket c β vertex) then
    val c.p c.fl (modeValueList c.p c.fl c.i c.differ c.cols
      (vertex / c.p / c.nb) (vertex / c.p % c.nb))
  else 1

/-- A fixed product with `modes * precision` positions equals the actual native source product,
provided every exponent is at most the creation precision. No table of replicated factors is
constructed, and the statement includes empty mode sets and precision zero. -/
theorem prod_factor_eq_sourceProduct (c : PacketCtx) (β : List ℕ)
    (hβ : ∀ b ∈ β, b ≤ c.p) :
    (∏ vertex ∈ range ((c.tiles * c.nb) * c.p), factor c β vertex) =
      val c.p c.fl (sourceProduct c β) := by
  classical
  have hb (k : ℕ) : β.getD k 0 ≤ c.p := by
    by_cases hk : k < β.length
    · rw [List.getD_eq_getElem _ _ hk]
      exact hβ _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Nat.zero_le _
  have hpair (k : Fin (c.tiles * c.nb)) (j : Fin c.p) :
      factor c β (finProdFinEquiv (k, j)).val =
        if modeSources c.i c.e₁ c.e₂ (k.val / c.nb) = true ∧ j.val < β.getD k.val 0 then
          val c.p c.fl (modeValueList c.p c.fl c.i c.differ c.cols
            (k.val / c.nb) (k.val % c.nb)) else 1 := by
    have hp : 0 < c.p := Nat.zero_lt_of_lt j.isLt
    have hd : (finProdFinEquiv (k, j)).val / c.p = k.val := by
      change (j.val + c.p * k.val) / c.p = k.val
      rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
    have hm : (finProdFinEquiv (k, j)).val % c.p = j.val := by
      change (j.val + c.p * k.val) % c.p = j.val
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
    simp only [factor, ofPacket, selected, (finProdFinEquiv (k, j)).isLt, decide_true,
      Bool.true_and, hd, hm, Bool.and_eq_true_iff, decide_eq_true_eq]
  have hpower (k : Fin (c.tiles * c.nb)) :
      (∏ j : Fin c.p, if modeSources c.i c.e₁ c.e₂ (k.val / c.nb) = true ∧
          j.val < β.getD k.val 0 then
            val c.p c.fl (modeValueList c.p c.fl c.i c.differ c.cols
              (k.val / c.nb) (k.val % c.nb)) else 1) =
        if modeSources c.i c.e₁ c.e₂ (k.val / c.nb) then
          val c.p c.fl (modeValueList c.p c.fl c.i c.differ c.cols
            (k.val / c.nb) (k.val % c.nb)) ^ β.getD k.val 0 else 1 := by
    cases modeSources c.i c.e₁ c.e₂ (k.val / c.nb) with
    | false => simp
    | true =>
      simp only [true_and, ↓reduceIte]
      rw [Fin.prod_univ_eq_prod_range (fun j => if j < β.getD k.val 0 then
        val c.p c.fl (modeValueList c.p c.fl c.i c.differ c.cols
          (k.val / c.nb) (k.val % c.nb)) else 1), ← Finset.prod_filter]
      have hr : (range c.p).filter (fun j => j < β.getD k.val 0) = range (β.getD k.val 0) := by
        ext j
        simp only [mem_filter, mem_range]
        have := hb k.val
        omega
      rw [hr]
      simp
  rw [prod_range, ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type]
  simp_rw [hpair, hpower]
  rw [Fin.prod_univ_eq_prod_range (fun k => if modeSources c.i c.e₁ c.e₂ (k / c.nb) then
    val c.p c.fl (modeValueList c.p c.fl c.i c.differ c.cols
      (k / c.nb) (k % c.nb)) ^ β.getD k 0 else 1)]
  simp only [sourceProduct, val_prodList, List.map_map, sourceModes]
  rw [← List.prod_toFinset _ (List.nodup_range.filter _)]
  have hrange : (List.range (c.tiles * c.nb)).toFinset = range (c.tiles * c.nb) := by
    ext k
    simp
  simp only [List.toFinset_filter, hrange, Finset.prod_filter, Function.comp_apply, val_pow]

private structure Summary where
  /-- Product position is in range and its mode is a source. -/
  active : Bool
  /-- Repetition index to compare with the selected exponent. -/
  copy : ℕ

private enc_structure encSummary : Summary where active : encBool, copy : encNat

private def index (h : Header) : ℕ := h.vertex / h.precision

private def summary (h : Header) : Summary :=
  ⟨decide (h.vertex < h.modes * h.precision) &&
    modeSources h.coordinate h.first h.second (index h / h.perTile), h.vertex % h.precision⟩

private theorem index_polyTime : ComputableInPolyTime index encHeader encNat :=
  binary_div' encHeader_vertex_deg.computableInPolyTime encHeader_precision_deg.computableInPolyTime

private theorem summary_polyTime : ComputableInPolyTime summary encHeader encSummary := by
  have hv := encHeader_vertex_deg.computableInPolyTime
  have hp := encHeader_precision_deg.computableInPolyTime
  have ht := binary_div' index_polyTime encHeader_perTile_deg.computableInPolyTime
  have hs := ite (binary_testBit ht encHeader_coordinate_deg.computableInPolyTime)
    encHeader_first_deg.computableInPolyTime encHeader_second_deg.computableInPolyTime
  exact encSummary_mk_polyTime
    (bool_and' (binary_lt' hv (binary_mul' encHeader_modes_deg.computableInPolyTime hp)) hs)
    (binary_mod' hv hp)

private def finish (x : Summary × ℕ) : Bool := x.1.active && decide (x.1.copy < x.2)

private theorem finish_deg :
    ComputableInDegree finish (encPair encSummary encNat) encBool 1 1 := by
  have hs := ComputableInDegree.fst encSummary encNat
  have hc := (encSummary_copy_deg.comp hs).prod (ComputableInDegree.snd encSummary encNat)
  have hlt := ComputableInDegree.natLt.comp hc
  exact ((ComputableInDegree.of_finite (encIn := encPair encBool encBool)
    (encMid := encBool) fun q : Bool × Bool => q.1 && q.2).comp
      ((encSummary_active_deg.comp hs).prod hlt)).mono

/-- One sharp binary exponent lookup followed by a linear comparison implements source-factor
selection. Oversized exponent values stay outside the polynomial resource charge. -/
theorem exists_selected_inO : ∃ d, ComputableInO selected encInput encBool
    (fun a => (encList encNat a.exponents).length + shortSize a ^ d)
    (fun a => (encList encNat a.exponents).length + shortSize a ^ d) := by
  obtain ⟨d, h⟩ := ComputableInO.exists_listGetD_short (short := shortSize) 0
    encInput_header_deg encInput_exponents_deg index_polyTime summary_polyTime finish_deg 2
    (fun a => by simp [shortSize])
    (fun a => by
      simp only [encInput_apply, encInputFields, length_encPair, shortSize]
      omega)
    (fun a => by simp only [shortSize]; omega)
    (fun a => by simp only [shortSize]; omega)
  exact ⟨d, h.of_enc_eq fun a => by simp [finish, summary, index, selected]⟩

end Turing.MultiTapeTM.PacketSourceProduct
