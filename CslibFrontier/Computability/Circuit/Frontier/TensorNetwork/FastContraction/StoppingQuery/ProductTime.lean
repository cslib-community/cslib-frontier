/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.Product
import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.ResidueInverse
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog

/-!
# Native polynomial-time access to stopping-product macros

These certificates implement the concrete short-address router and template selector.
Product and compressor heights are unary; all large offsets and coordinates are binary.
The protected assignment and source word are absent from every encoded argument.
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction.StoppingQuery.Product

open Boolean BitString Turing.MultiTapeTM ComputableInPolyTime

private theorem half_polyTime {α : Type} {enc : α ↪ List Bool} {p : α → Parameters}
    (hp : ComputableInPolyTime p enc encParameters) :
    ComputableInPolyTime (fun x => 3 ^ modulusExp (p x).scale) enc encNat :=
  unary_to_binary.comp (ResidueInverse.half_polyTime.comp (by fun_prop))

private theorem operand_polyTime {α : Type} {enc : α ↪ List Bool}
    {p : α → Parameters} {a : α → NodeData} {r : α → Bool}
    (hp : ComputableInPolyTime p enc encParameters)
    (ha : ComputableInPolyTime a enc encNodeData)
    (hr : ComputableInPolyTime r enc encBool) :
    ComputableInPolyTime (fun x => operand (p x) (a x) (r x)) enc
      ConvolutionOperand.Signed.encQuery := by
  unfold operand
  apply ConvolutionOperand.Signed.encQuery_mk_polyTime (half_polyTime hp) <;> fun_prop

private theorem valueTemplate_polyTime :
    ComputableInPolyTime (fun x : Parameters × NodeData =>
      if x.2.coefficient < 2 * 3 ^ modulusExp x.1.scale ∧ x.2.bit < x.1.precision then
        if x.2.level = 0 ∧ x.1.vertices ≤ x.2.base then
          if x.2.coefficient = 0 ∧ x.2.bit = 0 then (2 : Fin 9) else 1
        else 0
      else 1) encTemplateInput (encFinEnum (Fin 9)) := by
  have hp := fst encParameters encNodeData
  have ha := snd encParameters encNodeData
  have hc := encNodeData_coefficient_polyTime ha
  have hb := encNodeData_bit_polyTime ha
  have hl := encNodeData_level_polyTime ha
  have hv := encParameters_vertices_polyTime hp
  have hbase := encNodeData_base_polyTime ha
  have hprec := encParameters_precision_polyTime hp
  have hhalf := half_polyTime hp
  have hvalid := decide_and (binary_lt' hc (binary_mul' (const 2) hhalf))
    (binary_lt' hb hprec)
  have hpadding := decide_and (decide_eq' hl (const 0)) (binary_le.comp (hv.prod hbase))
  have hunit := decide_and (decide_eq' hc (const 0)) (decide_eq' hb (const 0))
  exact ite_decide hvalid (ite_decide hpadding (ite_decide hunit (const 2) (const 1))
    (const 0)) (const 1)

/-- The finite template is selected by native polynomial work on the stated short encoding. -/
theorem templateIndex_polyTime :
    ComputableInPolyTime (fun x : Parameters × NodeData => templateIndex x.1 x.2)
      encTemplateInput (encFinEnum (Fin 9)) := by
  have hp := fst encParameters encNodeData
  have ha := snd encParameters encNodeData
  have hkind := encNodeData_kind_polyTime ha
  have hb := encNodeData_bit_polyTime ha
  have hpw := encParameters_precision_polyTime hp
  have hr := encNodeData_remaining_polyTime ha
  have hc := encNodeData_carry_polyTime ha
  have hj := encNodeData_port_polyTime ha
  have hd := encNodeData_address_polyTime ha
  have htag := CarryLookahead.Query.encAddressData_tag_polyTime hd
  have hindex := CarryLookahead.Query.encAddressData_index_polyTime hd
  have hcor := ConvolutionOperand.Signed.computableInPolyTime_correction.comp
    (operand_polyTime hp ha (const false))
  have hop := CarryLookahead.Query.opData_polyTime hpw (const []) hd
  have hchoose : ComputableInPolyTime (fun op : Op => match op with
      | .const false => (1 : Fin 9)
      | .const true => 2
      | .not => 3
      | .and => 4
      | .or => 5) encOp (encFinEnum (Fin 9)) := of_finite _
  have hlocal := hchoose.comp hop
  have hinput := bool_not.comp (bool_and.comp
    ((binary_le.comp ((const 1).prod htag)).prod (binary_le.comp (htag.prod (const 11)))))
  have hfinish := ite hinput
    (ite_decide (binary_lt' hindex (binary_add' hpw hpw)) (const (0 : Fin 9)) (const 1)) hlocal
  have htree := ite_decide (encB := encFinEnum (Fin 9)) (binary_lt' hb hpw)
    (ite_decide (decide_eq' hr (const 0)) (const (6 : Fin 9)) (ite hc (const 8) (const 7)))
    (const 1)
  have hport := ite_decide (encB := encFinEnum (Fin 9)) (binary_lt' hb hpw)
    (ite_decide (decide_or (decide_eq' hj (const 0)) (decide_eq' hj (const 1)))
      (const (0 : Fin 9)) (ite hcor (const 2) (const 1))) (const 1)
  exact ite_decide (decide_eq' hkind (const 0)) valueTemplate_polyTime
    (ite_decide (decide_eq' hkind (const 1)) hfinish
      (ite_decide (decide_eq' hkind (const 2)) htree
        (ite_decide (decide_eq' hkind (const 3)) hport (const 1))))

/-- Native selection of the fixed bounded local formula, charged only to short metadata. -/
theorem boundedTemplate_polyTime :
    ComputableInPolyTime (fun x : Parameters × NodeData => boundedTemplate x.1 x.2)
      encTemplateInput (LocalValueGame.FormulaExpansion.encBoundedFormula 7 12) :=
  (of_finite localTemplate).comp templateIndex_polyTime

/-- Construct a canonical product root from binary coordinates and a unary level. -/
theorem valueData_polyTime {α : Type} {enc : α ↪ List Bool}
    {base level coefficient bit : α → ℕ}
    (hb : ComputableInPolyTime base enc encNat) (hl : ComputableInPolyTime level enc encUnary)
    (hc : ComputableInPolyTime coefficient enc encNat) (hi : ComputableInPolyTime bit enc encNat) :
    ComputableInPolyTime (fun a => valueData (base a) (level a) (coefficient a) (bit a))
      enc encNodeData :=
  encNodeData_mk_polyTime (const 0) hb hl hc
    (const (⟨0, 0, 0⟩ : CarryLookahead.Query.AddressData)) (const []) (const 0)
    (const false) hi (const 0)

private theorem finishData_polyTime {α : Type} {enc : α ↪ List Bool}
    {base level coefficient : α → ℕ} {address : α → CarryLookahead.Query.AddressData}
    (hb : ComputableInPolyTime base enc encNat) (hl : ComputableInPolyTime level enc encUnary)
    (hc : ComputableInPolyTime coefficient enc encNat)
    (ha : ComputableInPolyTime address enc CarryLookahead.Query.encAddressData) :
    ComputableInPolyTime (fun a => finishData (base a) (level a) (coefficient a) (address a))
      enc encNodeData :=
  encNodeData_mk_polyTime (const 1) hb hl hc ha (const []) (const 0) (const false)
    (const 0) (const 0)

private theorem treeData_polyTime {α : Type} {enc : α ↪ List Bool}
    {base level coefficient remaining bit : α → ℕ} {path : α → List Bool} {carry : α → Bool}
    (hb : ComputableInPolyTime base enc encNat) (hl : ComputableInPolyTime level enc encUnary)
    (hc : ComputableInPolyTime coefficient enc encNat) (hp : ComputableInPolyTime path enc encBits)
    (hr : ComputableInPolyTime remaining enc encUnary)
    (hcar : ComputableInPolyTime carry enc encBool)
    (hi : ComputableInPolyTime bit enc encNat) :
    ComputableInPolyTime (fun a => treeData (base a) (level a) (coefficient a) (path a)
      (remaining a) (carry a) (bit a)) enc encNodeData :=
  encNodeData_mk_polyTime (const 2) hb hl hc
    (const (⟨0, 0, 0⟩ : CarryLookahead.Query.AddressData)) hp hr hcar hi (const 0)

private theorem portData_polyTime {α : Type} {enc : α ↪ List Bool}
    {base level coefficient bit : α → ℕ} {path : α → List Bool} {carry : α → Bool}
    {port : α → Fin 7} (hb : ComputableInPolyTime base enc encNat)
    (hl : ComputableInPolyTime level enc encUnary)
    (hc : ComputableInPolyTime coefficient enc encNat)
    (hp : ComputableInPolyTime path enc encBits) (hcar : ComputableInPolyTime carry enc encBool)
    (hi : ComputableInPolyTime bit enc encNat)
    (hj : ComputableInPolyTime port enc (encFinEnum (Fin 7))) :
    ComputableInPolyTime (fun a => portData (base a) (level a) (coefficient a) (path a)
      (carry a) (bit a) (port a)) enc encNodeData :=
  encNodeData_mk_polyTime (const 3) hb hl hc
    (const (⟨0, 0, 0⟩ : CarryLookahead.Query.AddressData)) hp (const 0) hcar hi hj

private theorem entryData_polyTime {α : Type} {enc : α ↪ List Bool}
    {vertex coefficient bit : α → ℕ} (hv : ComputableInPolyTime vertex enc encNat)
    (hc : ComputableInPolyTime coefficient enc encNat) (hi : ComputableInPolyTime bit enc encNat) :
    ComputableInPolyTime (fun a => entryData (vertex a) (coefficient a) (bit a)) enc encNodeData :=
  encNodeData_mk_polyTime (const 4) hv (const 0) hc
    (const (⟨0, 0, 0⟩ : CarryLookahead.Query.AddressData)) (const []) (const 0)
    (const false) hi (const 0)

attribute [local fun_prop] valueData_polyTime finishData_polyTime treeData_polyTime
  portData_polyTime entryData_polyTime

private theorem sourceValue_polyTime :
    ComputableInPolyTime (fun x : Parameters × NodeData × Fin 7 =>
      source x.1 { x.2.1 with kind := 0 } x.2.2) encSourceInput (encOption encNodeData) := by
  simp only [source, Fin.isValue, ↓reduceIte]
  have hp := fst encParameters (encPair encNodeData (encFinEnum (Fin 7)))
  have ha := (fst encNodeData (encFinEnum (Fin 7))).comp
    (snd encParameters (encPair encNodeData (encFinEnum (Fin 7))))
  have hj := (snd encNodeData (encFinEnum (Fin 7))).comp
    (snd encParameters (encPair encNodeData (encFinEnum (Fin 7))))
  have hbase := encNodeData_base_polyTime ha
  have hl := encNodeData_level_polyTime ha
  have hc := encNodeData_coefficient_polyTime ha
  have hb := encNodeData_bit_polyTime ha
  have hprec := encParameters_precision_polyTime hp
  have hv := encParameters_vertices_polyTime hp
  have hvalid := decide_and (binary_lt' hc (binary_mul' (const 2) (half_polyTime hp)))
    (decide_and (binary_lt' hb hprec) (decide_eq' hj (const 0)))
  have hentry := (optionSome encNodeData).comp (entryData_polyTime hbase hc hb)
  have hfinish := (optionSome encNodeData).comp (finishData_polyTime hbase
    (unary_sub' hl (const 1)) hc
    (CarryLookahead.Query.encAddressData_mk_polyTime (const 11) (const 0) hb))
  exact ite_decide hvalid (ite_decide (decide_eq' hl (const 0))
    (ite_decide (binary_lt' hbase hv) hentry (const none)) hfinish) (const none)

private theorem sourceFinish_polyTime :
    ComputableInPolyTime (fun x : Parameters × NodeData × Fin 7 =>
      source x.1 { x.2.1 with kind := 1 } x.2.2) encSourceInput (encOption encNodeData) := by
  simp only [source, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  have hp := fst encParameters (encPair encNodeData (encFinEnum (Fin 7)))
  have ha := (fst encNodeData (encFinEnum (Fin 7))).comp
    (snd encParameters (encPair encNodeData (encFinEnum (Fin 7))))
  have hj := (snd encNodeData (encFinEnum (Fin 7))).comp
    (snd encParameters (encPair encNodeData (encFinEnum (Fin 7))))
  have hbase := encNodeData_base_polyTime ha
  have hl := encNodeData_level_polyTime ha
  have hc := encNodeData_coefficient_polyTime ha
  have hpw := encParameters_precision_polyTime hp
  have hd := encNodeData_address_polyTime ha
  have htag := CarryLookahead.Query.encAddressData_tag_polyTime hd
  have hindex := CarryLookahead.Query.encAddressData_index_polyTime hd
  have hinput := bool_not.comp (bool_and.comp
    ((binary_le.comp ((const 1).prod htag)).prod (binary_le.comp (htag.prod (const 11)))))
  have hheight := unary_add' (unary_add'
    (binary_clog_two.comp (binary_mul' (const 2) (half_polyTime hp)))
    (binary_clog_two.comp hpw)) (const 2)
  have hright := binary_le.comp (hpw.prod hindex)
  have hbit := ite_decide hright (binary_sub' hindex hpw) hindex
  have htree := (optionSome encNodeData).comp
    (treeData_polyTime hbase hl hc (const []) hheight hright hbit)
  have hzero := decide_eq' hj (const 0)
  have hone := decide_eq' hj (const 1)
  have hop := CarryLookahead.Query.opData_polyTime hpw (const []) hd
  have hchild := CarryLookahead.Query.childData_polyTime hpw
    (binary_clog_two.comp (binary_add' hpw (const 1))) hd hone
  have hfinish := (optionSome encNodeData).comp (finishData_polyTime hbase hl hc hchild)
  have hlive := decide_or (decide_and (decide_eq' hop (const Op.not)) hzero)
    (decide_and (decide_or (decide_eq' hop (const Op.and)) (decide_eq' hop (const Op.or)))
      (decide_or hzero hone))
  exact ite hinput (ite_decide (decide_and (binary_lt' hindex (binary_add' hpw hpw)) hzero)
    htree (const none)) (ite_decide hlive hfinish (const none))

private theorem sourceTree_polyTime :
    ComputableInPolyTime (fun x : Parameters × NodeData × Fin 7 =>
      source x.1 { x.2.1 with kind := 2 } x.2.2) encSourceInput (encOption encNodeData) := by
  simp only [source, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  have hp := fst encParameters (encPair encNodeData (encFinEnum (Fin 7)))
  have ha := (fst encNodeData (encFinEnum (Fin 7))).comp
    (snd encParameters (encPair encNodeData (encFinEnum (Fin 7))))
  have hj := (snd encNodeData (encFinEnum (Fin 7))).comp
    (snd encParameters (encPair encNodeData (encFinEnum (Fin 7))))
  have hbase := encNodeData_base_polyTime ha
  have hl := encNodeData_level_polyTime ha
  have hc := encNodeData_coefficient_polyTime ha
  have hpath := encNodeData_path_polyTime ha
  have hr := encNodeData_remaining_polyTime ha
  have hcar := encNodeData_carry_polyTime ha
  have hb := encNodeData_bit_polyTime ha
  have hshift : ComputableInPolyTime
      (fun a : Bool × Fin 7 => (CarrySaveLocal.source a.1 a.2).shift.val)
      (encPair encBool (encFinEnum (Fin 7))) encNat := of_finite _
  have hside : ComputableInPolyTime
      (fun a : Bool × Fin 7 => CarrySaveQuery.childSide (CarrySaveLocal.source a.1 a.2).word)
      (encPair encBool (encFinEnum (Fin 7))) encBool := of_finite _
  have hcarry : ComputableInPolyTime
      (fun a : Bool × Fin 7 => CarrySaveQuery.childCarry (CarrySaveLocal.source a.1 a.2).word)
      (encPair encBool (encFinEnum (Fin 7))) encBool := of_finite _
  have hsh := hshift.comp (hcar.prod hj)
  have hsi := hside.comp (hcar.prod hj)
  have hca := hcarry.comp (hcar.prod hj)
  have hport := (optionSome encNodeData).comp (portData_polyTime hbase hl hc hpath hcar hb hj)
  have htree := (optionSome encNodeData).comp (treeData_polyTime hbase hl hc
    (bitsAppend hpath (bitsCons hsi (const []))) (unary_sub' hr (const 1)) hca
    (binary_sub' hb hsh))
  exact ite_decide (binary_lt' hb (encParameters_precision_polyTime hp))
    (ite_decide (decide_eq' hr (const 0)) hport
      (ite_decide (binary_le.comp (hsh.prod hb)) htree (const none))) (const none)

private theorem sourcePort_polyTime :
    ComputableInPolyTime (fun x : Parameters × NodeData × Fin 7 =>
      source x.1 { x.2.1 with kind := 3 } x.2.2) encSourceInput (encOption encNodeData) := by
  simp only [source, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  have hp := fst encParameters (encPair encNodeData (encFinEnum (Fin 7)))
  have ha := (fst encNodeData (encFinEnum (Fin 7))).comp
    (snd encParameters (encPair encNodeData (encFinEnum (Fin 7))))
  have hj := (snd encNodeData (encFinEnum (Fin 7))).comp
    (snd encParameters (encPair encNodeData (encFinEnum (Fin 7))))
  have hlocal := encNodeData_port_polyTime ha
  have hright := decide_eq' hlocal (const 1)
  have hoperand := ConvolutionOperand.Signed.computableInPolyTime_source.comp
    (operand_polyTime hp ha hright)
  have hvalue := optionMapWithInput (encC := encNodeData)
    (f := fun x j => valueData
      (if x.2.1.port = 1 then x.2.1.base + 2 ^ x.2.1.level else x.2.1.base)
      x.2.1.level j.1 j.2) hoperand (by
    have harg := fst encSourceInput (encPair encNat encNat)
    have hnode := ha.comp harg
    have hbase := encNodeData_base_polyTime hnode
    have hlevel := encNodeData_level_polyTime hnode
    have hout := snd encSourceInput (encPair encNat encNat)
    exact valueData_polyTime
      (ite_decide (hright.comp harg) (binary_add' hbase (binary_two_pow.comp hlevel)) hbase)
      hlevel hout.fst' hout.snd')
  exact ite_decide
    (decide_and (binary_lt' (encNodeData_bit_polyTime ha) (encParameters_precision_polyTime hp))
      (decide_eq' hj (const 0)))
    (ite_decide (decide_or (decide_eq' hlocal (const 0)) hright) hvalue (const none))
    (const none)

/-- One native routine computes every product macro source. Unary heights pay for the binary
powers of two it writes; neither an assignment nor a tensor entry appears in its input. -/
theorem source_polyTime :
    ComputableInPolyTime (fun x : Parameters × NodeData × Fin 7 => source x.1 x.2.1 x.2.2)
      encSourceInput (encOption encNodeData) := by
  have ha := (fst encNodeData (encFinEnum (Fin 7))).comp
    (snd encParameters (encPair encNodeData (encFinEnum (Fin 7))))
  have hk := encNodeData_kind_polyTime ha
  exact ite_decide (decide_eq' hk (const 0)) sourceValue_polyTime
    (ite_decide (decide_eq' hk (const 1)) sourceFinish_polyTime
      (ite_decide (decide_eq' hk (const 2)) sourceTree_polyTime
        (ite_decide (decide_eq' hk (const 3)) sourcePort_polyTime (const none))))

end Cslib.Circuits.Frontier.FastContraction.StoppingQuery.Product
