/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery
public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.PolyTime
public import CslibFrontier.Computability.Circuit.Boolean.LocalValueGame.Formula.Bounded
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.ResidueInverse
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog

/-!
# Native macro routing in a stopping product

A product subtree retains its assignment outside the changing address. The raw address contains
only a binary vertex offset, unary product height, binary coefficient-bit coordinates and the
short local arithmetic query. It denotes the existing stopping circuit with assignment zero;
interpreting its entry function at a fixed assignment recovers the desired subtree.

The native macro router computes signed operand references, carry-save predecessors and
carry-lookahead predecessors. Every produced address clears unused fields. The assignment is
absent from the encoding, so its length cannot enter the cost of a local routing computation.
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction.StoppingQuery.Product

open Boolean BitString Turing.MultiTapeTM ComputableInPolyTime

/-- Runtime circuit parameters, all encoded in binary. -/
structure Parameters where
  /-- Scale selecting the extension-ring modulus. -/
  scale : ℕ
  /-- Number of bits in each residue coefficient. -/
  precision : ℕ
  /-- Number of genuine vertices before identity padding. -/
  vertices : ℕ
  deriving DecidableEq

/-- Framed binary scale and precision, followed by the binary vertex count. -/
enc_structure encParameters : Parameters where
  scale : encNat, precision : encNat, vertices : encNat

/-- Raw product address: value, finishing adder, carry-save tree, signed port or entry.
The assignment belongs to protected ambient storage and is deliberately absent. -/
structure NodeData where
  /-- Tags 0–4 select value, finishing adder, carry-save tree, signed port, and entry. -/
  kind : Fin 5
  /-- Left endpoint of the vertex block, or the vertex of an entry query. -/
  base : ℕ
  /-- Block height for a value query; child-block height inside its multiplication. -/
  level : ℕ
  /-- Selected coefficient of the reduced polynomial representative. -/
  coefficient : ℕ
  /-- Gate coordinate in the finishing carry-lookahead adder. -/
  address : CarryLookahead.Query.AddressData
  /-- Local convolution-sum path, distinct from the protected assignment word. -/
  path : List Bool
  /-- Number of carry-save layers below the current arithmetic query. -/
  remaining : ℕ
  /-- Select the second carry-save component when true. -/
  carry : Bool
  /-- Selected precision bit outside a finishing-adder query. -/
  bit : ℕ
  /-- Local input of a signed multiplication leaf, including its correction bits. -/
  port : Fin 7
  deriving DecidableEq

/-- The kind and port have fixed finite encodings. Product and tree heights are unary;
all other numbers are binary. Every field except the final port is framed. -/
enc_structure encNodeData : NodeData where
  kind : (encFinEnum (Fin 5)), base : encNat, level : encUnary, coefficient : encNat,
  address : CarryLookahead.Query.encAddressData, path : encBits, remaining : encUnary,
  carry : encBool, bit : encNat, port : (encFinEnum (Fin 7))

/-- Canonical block-value query, with empty arithmetic scratch fields. -/
@[expose] def valueData (base level coefficient bit : ℕ) : NodeData :=
  ⟨0, base, level, coefficient, ⟨0, 0, 0⟩, [], 0, false, bit, 0⟩

/-- Finishing-adder query in a product, with the other macro fields cleared. -/
@[expose] def finishData (base level coefficient : ℕ)
    (address : CarryLookahead.Query.AddressData) : NodeData :=
  ⟨1, base, level, coefficient, address, [], 0, false, 0, 0⟩

/-- Canonical carry-save query in one product coefficient. -/
@[expose] def treeData (base level coefficient : ℕ) (path : List Bool) (remaining : ℕ)
    (carry : Bool) (bit : ℕ) : NodeData :=
  ⟨2, base, level, coefficient, ⟨0, 0, 0⟩, path, remaining, carry, bit, 0⟩

/-- Canonical operand or correction port, with no remaining carry-save layers. -/
@[expose] def portData (base level coefficient : ℕ) (path : List Bool) (carry : Bool)
    (bit : ℕ) (port : Fin 7) : NodeData :=
  ⟨3, base, level, coefficient, ⟨0, 0, 0⟩, path, 0, carry, bit, port⟩

/-- Canonical terminal entry query; the caller supplies the protected assignment. -/
@[expose] def entryData (vertex coefficient bit : ℕ) : NodeData :=
  ⟨4, vertex, 0, coefficient, ⟨0, 0, 0⟩, [], 0, false, bit, 0⟩

/-- Interpret the raw macro address in the existing stopping circuit. -/
@[expose] def node (a : NodeData) : StoppingQuery.Node :=
  if a.kind = 0 then .value 0 a.base a.level a.coefficient a.bit
  else if a.kind = 1 then .product 0 a.base a.level a.coefficient (.finish a.address.address)
  else if a.kind = 2 then .product 0 a.base a.level a.coefficient
    (.tree ⟨a.path, a.remaining, a.carry, a.bit⟩)
  else if a.kind = 3 then .product 0 a.base a.level a.coefficient
    (.port a.path a.carry a.bit a.port)
  else .entry ⟨0, a.base, a.coefficient, a.bit⟩

/-- Canonicalize a product node. Assignments are supplied externally; sum nodes are outside
this view and map to the zero block query. -/
@[expose] def ofNode : StoppingQuery.Node → NodeData
  | .value _ base level coefficient bit => valueData base level coefficient bit
  | .product _ base level coefficient (.finish a) => finishData base level coefficient a.toData
  | .product _ base level coefficient (.tree a) =>
      treeData base level coefficient a.path a.remaining a.carry a.bit
  | .product _ base level coefficient (.port path carry bit port) =>
      portData base level coefficient path carry bit port
  | .entry e => entryData e.vertex e.coefficient e.bit
  | _ => valueData 0 0 0 0

/-- Only the canonical fields for the chosen macro kind are retained. -/
@[expose] def Canonical (a : NodeData) : Prop := ofNode (node a) = a

/-- A raw carry-lookahead tag denotes an input exactly outside its eleven operation tags. -/
@[expose] def isInput (a : CarryLookahead.Query.AddressData) : Bool :=
  !(decide (1 ≤ a.tag) && decide (a.tag ≤ 11))

/-- The signed arithmetic request at one local operand port. -/
@[expose] def operand (p : Parameters) (a : NodeData) (right : Bool) :
    ConvolutionOperand.Signed.Query :=
  ⟨3 ^ modulusExp p.scale, p.precision, a.coefficient, a.path, a.bit, a.carry, right⟩

/-- Local formula identifier: input, the two constants, not, and, or, signed leaf, and the
two carry-save formulas. The choice depends only on short arithmetic metadata. -/
@[expose] def templateIndex (p : Parameters) (a : NodeData) : Fin 9 :=
  if a.kind = 0 then
    if a.coefficient < 2 * 3 ^ modulusExp p.scale ∧ a.bit < p.precision then
      if a.level = 0 ∧ p.vertices ≤ a.base then
        if a.coefficient = 0 ∧ a.bit = 0 then 2 else 1
      else 0
    else 1
  else if a.kind = 1 then
    if isInput a.address then if a.address.index < p.precision + p.precision then 0 else 1
    else match CarryLookahead.Query.opData p.precision [] a.address with
      | .const false => 1
      | .const true => 2
      | .not => 3
      | .and => 4
      | .or => 5
  else if a.kind = 2 then
    if a.bit < p.precision then
      if a.remaining = 0 then 6 else if a.carry then 8 else 7
    else 1
  else if a.kind = 3 then
    if a.bit < p.precision then
      if a.port = 0 ∨ a.port = 1 then 0
      else if ConvolutionOperand.Signed.correction (operand p a false) then 2 else 1
    else 1
  else 1

/-- Follow one macro source, computing each index and resetting unused address fields. -/
@[expose] def source (p : Parameters) (a : NodeData) (port : Fin 7) : Option NodeData :=
  if a.kind = 0 then
    if a.coefficient < 2 * 3 ^ modulusExp p.scale ∧ a.bit < p.precision ∧ port = 0 then
      if a.level = 0 then
        if a.base < p.vertices then some (entryData a.base a.coefficient a.bit) else none
      else some (finishData a.base (a.level - 1) a.coefficient ⟨11, 0, a.bit⟩)
    else none
  else if a.kind = 1 then
    if isInput a.address then
      if a.address.index < p.precision + p.precision ∧ port = 0 then
        some (treeData a.base a.level a.coefficient []
          (SignedValueGame.height (3 ^ modulusExp p.scale) p.precision)
          (decide (p.precision ≤ a.address.index))
          (if p.precision ≤ a.address.index then a.address.index - p.precision
            else a.address.index))
      else none
    else
      let op : Op := CarryLookahead.Query.opData p.precision [] a.address
      if (op = .not ∧ port = 0) ∨ ((op = .and ∨ op = .or) ∧ (port = 0 ∨ port = 1)) then
        some (finishData a.base a.level a.coefficient
          (CarryLookahead.Query.childData p.precision (SignedValueGame.rounds p.precision)
            a.address (decide (port = 1))))
      else none
  else if a.kind = 2 then
    if a.bit < p.precision then
      if a.remaining = 0 then some (portData a.base a.level a.coefficient a.path a.carry a.bit port)
      else if (CarrySaveLocal.source a.carry port).shift.val ≤ a.bit then
        some (treeData a.base a.level a.coefficient
          (a.path ++ [CarrySaveQuery.childSide (CarrySaveLocal.source a.carry port).word])
          (a.remaining - 1) (CarrySaveQuery.childCarry (CarrySaveLocal.source a.carry port).word)
          (a.bit - (CarrySaveLocal.source a.carry port).shift.val))
      else none
    else none
  else if a.kind = 3 then
    if a.bit < p.precision ∧ port = 0 then
      if a.port = 0 ∨ a.port = 1 then
        (ConvolutionOperand.Signed.source (operand p a (decide (a.port = 1)))).map fun j =>
          valueData (if a.port = 1 then a.base + 2 ^ a.level else a.base) a.level j.1 j.2
      else none
    else none
  else none

private theorem opData_eq (p : ℕ) (d : CarryLookahead.Query.AddressData) :
    CarryLookahead.Query.opData p [] d = (SignedValueGame.finishDecoder p).op d.address := by
  rcases d with ⟨tag, round, index⟩
  by_cases ht : tag < 12
  · interval_cases tag <;>
      simp [CarryLookahead.Query.opData, CarryLookahead.Query.AddressData.address,
        SignedValueGame.finishDecoder, CarryLookahead.Query.decoder,
        CarryLookahead.Query.readInput]
  · have hn (i : ℕ) (hi : i < 12) : tag ≠ i := by omega
    simp [CarryLookahead.Query.opData, CarryLookahead.Query.AddressData.address,
      SignedValueGame.finishDecoder, CarryLookahead.Query.decoder,
      CarryLookahead.Query.readInput, hn 1 (by omega), hn 2 (by omega), hn 3 (by omega),
      hn 4 (by omega), hn 5 (by omega), hn 6 (by omega), hn 7 (by omega), hn 8 (by omega),
      hn 9 (by omega), hn 10 (by omega), hn 11 (by omega)]

private theorem childData_eq (p : ℕ) (d : CarryLookahead.Query.AddressData) (b : Bool) :
    (CarryLookahead.Query.childData p (SignedValueGame.rounds p) d b).address =
      (SignedValueGame.finishDecoder p).child d.address b := by
  rcases d with ⟨tag, round, index⟩
  by_cases ht : tag < 12
  · interval_cases tag <;> cases round <;> cases b <;>
      simp [CarryLookahead.Query.childData, CarryLookahead.Query.AddressData.address,
        SignedValueGame.finishDecoder, CarryLookahead.Query.decoder] <;>
        split_ifs <;> simp_all
  · have hn (i : ℕ) (hi : i < 12) : tag ≠ i := by omega
    simp [CarryLookahead.Query.childData, CarryLookahead.Query.AddressData.address,
      SignedValueGame.finishDecoder, CarryLookahead.Query.decoder,
      hn 1 (by omega), hn 2 (by omega), hn 3 (by omega),
      hn 4 (by omega), hn 5 (by omega), hn 6 (by omega), hn 7 (by omega), hn 8 (by omega),
      hn 9 (by omega), hn 10 (by omega), hn 11 (by omega)]

private theorem address_isInput (d : CarryLookahead.Query.AddressData) :
    if isInput d then d.address = .input d.index else ∀ j, d.address ≠ .input j := by
  rcases d with ⟨tag, round, index⟩
  by_cases ht : tag < 12
  · interval_cases tag <;> simp [isInput, CarryLookahead.Query.AddressData.address]
  · have hn (i : ℕ) (hi : i < 12) : tag ≠ i := by omega
    have hlarge : ¬tag ≤ 11 := by omega
    simp [isInput, hlarge, CarryLookahead.Query.AddressData.address,
      hn 1 (by omega), hn 2 (by omega), hn 3 (by omega), hn 4 (by omega),
      hn 5 (by omega), hn 6 (by omega), hn 7 (by omega), hn 8 (by omega),
      hn 9 (by omega), hn 10 (by omega), hn 11 (by omega)]

/-- Every native macro reference is exactly the reference of the existing stopping circuit. -/
theorem source_node (p : Parameters) (a : NodeData) (port : Fin 7) :
    (source p a port).map node =
      StoppingQuery.source p.scale p.precision 0 p.vertices (node a) port := by
  rcases a with ⟨kind, base, level, coefficient, address, path, remaining, carry, bit, index⟩
  fin_cases kind
  · cases level <;> simp [source, node, StoppingQuery.source, length_modulus,
      finishData, entryData, CarryLookahead.Query.AddressData.address]
    split_ifs <;> simp_all [node]
  · by_cases hi : isInput address = true
    · have haddr := address_isInput address
      simp only [hi, ↓reduceIte] at haddr
      simp [source, node, hi, haddr, StoppingQuery.source, SignedValueGame.source, treeData]
    · have haddr := address_isInput address
      simp only [hi] at haddr
      have hop := opData_eq p.precision address
      have hchild := childData_eq p.precision address
      simp only [source, node, Fin.isValue, ↓reduceIte, hi, Bool.false_eq_true]
      cases ha : address.address <;> try exact (haddr _ ha).elim
      all_goals
        simp only [StoppingQuery.source, SignedValueGame.source]
        simp only [ha] at hop hchild
        simp only [hop, SignedValueGame.finishSource]
        cases hoperation : (SignedValueGame.finishDecoder p.precision).op _ <;>
          by_cases hzero : port = 0 <;> by_cases hone : port = 1 <;>
          simp [hoperation, hzero, hone, finishData, node, hchild]
  · simp [source, node, StoppingQuery.source, SignedValueGame.source,
      CarrySaveQuery.descend, treeData, portData]
    split_ifs <;> simp_all [node]
  · by_cases hzero : index = 0 <;> by_cases hone : index = 1 <;>
      simp [source, node, StoppingQuery.source, hzero, hone, operand, operandQuery,
        valueData] <;>
      split_ifs <;> simp_all [node, Option.map_map, Function.comp_def]
  · simp [source, node, StoppingQuery.source]

/-- The nine fixed local formulas used by the product circuit, with their common depth bound. -/
def localTemplate (i : Fin 9) : LocalValueGame.FormulaExpansion.BoundedFormula 7 12 :=
  ⟨if i = 0 then Formula.input 0
    else if i = 1 then Formula.const false
    else if i = 2 then Formula.const true
    else if i = 3 then (Formula.input 0).not
    else if i = 4 then (Formula.input 0).and (.input 1)
    else if i = 5 then (Formula.input 0).or (.input 1)
    else if i = 6 then ((Formula.input 0).and (.input 1)).xor (.input 2)
    else if i = 7 then CarrySaveLocal.formula false
    else CarrySaveLocal.formula true,
    by fin_cases i <;> decide⟩

/-- Construct the bounded local formula from the native finite selector. -/
@[expose] def boundedTemplate (p : Parameters) (a : NodeData) :
    LocalValueGame.FormulaExpansion.BoundedFormula 7 12 := localTemplate (templateIndex p a)

private theorem template_value (p : Parameters) (a : NodeData) (hk : a.kind = 0) :
    (boundedTemplate p a).val =
      StoppingQuery.template p.scale p.precision 0 p.vertices (node a) := by
  simp only [boundedTemplate, templateIndex, node, hk, ↓reduceIte]
  by_cases hvalid : a.coefficient < 2 * 3 ^ modulusExp p.scale ∧ a.bit < p.precision
  · simp only [hvalid]
    cases a.level with
    | zero =>
      simp only [StoppingQuery.template, length_modulus, hvalid, ↓reduceIte, true_and]
      by_cases hb : a.base < p.vertices
      · simp [Nat.not_le.mpr hb, hb, localTemplate]
      · simp only [Nat.le_of_not_gt hb, hb, ↓reduceIte, InterpolationGrid.factorBit,
          Nat.not_lt_zero, false_and]
        by_cases hc : a.coefficient = 0 <;> by_cases hi : a.bit = 0 <;>
          simp [hc, hi, localTemplate]
    | succ l =>
      simp [StoppingQuery.template, length_modulus, hvalid, localTemplate]
  · cases a.level <;> simp [StoppingQuery.template, length_modulus, hvalid, localTemplate]

private theorem localTemplate_operation (op : Op) :
    (localTemplate (match op with
      | .const false => 1 | .const true => 2 | .not => 3 | .and => 4 | .or => 5)).val =
      SignedValueGame.operationFormula op := by
  cases op <;> try rfl
  case const b => cases b <;> rfl

private theorem template_finish (p : Parameters) (a : NodeData) (hk : a.kind = 1) :
    (boundedTemplate p a).val =
      StoppingQuery.template p.scale p.precision 0 p.vertices (node a) := by
  simp only [boundedTemplate, templateIndex, node, hk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  by_cases hi : isInput a.address = true
  · have haddr := address_isInput a.address
    simp only [hi, ↓reduceIte] at haddr
    simp only [hi, ↓reduceIte, StoppingQuery.template, haddr, SignedValueGame.template]
    split_ifs <;> rfl
  · have haddr := address_isInput a.address
    simp only [hi] at haddr
    simp only [hi, Bool.false_eq_true, ↓reduceIte, opData_eq]
    cases ha : a.address.address <;> try exact (haddr _ ha).elim
    all_goals
      simp only [StoppingQuery.template, SignedValueGame.template]
      simpa only [ha] using
        localTemplate_operation ((SignedValueGame.finishDecoder p.precision).op a.address.address)

private theorem localTemplate_const (b : Bool) :
    (localTemplate (if b then 2 else 1)).val = Formula.const b := by
  cases b <;> rfl

/-- The finite template selector reconstructs the existing stopping circuit's exact formula. -/
theorem boundedTemplate_val (p : Parameters) (a : NodeData) :
    (boundedTemplate p a).val =
      StoppingQuery.template p.scale p.precision 0 p.vertices (node a) := by
  by_cases hzero : a.kind = 0
  · exact template_value p a hzero
  by_cases hone : a.kind = 1
  · exact template_finish p a hone
  by_cases htwo : a.kind = 2
  · by_cases hb : a.bit < p.precision <;> by_cases hr : a.remaining = 0 <;> cases hc : a.carry <;>
      simp [boundedTemplate, templateIndex, localTemplate, node, htwo,
        StoppingQuery.template, SignedValueGame.template, hb, hr, hc]
  by_cases hthree : a.kind = 3
  · by_cases hb : a.bit < p.precision <;> by_cases hi : a.port = 0 ∨ a.port = 1 <;>
      simp only [boundedTemplate, templateIndex, node, hthree, Fin.isValue, Fin.reduceEq,
        ↓reduceIte, StoppingQuery.template, operand, operandQuery, hb, hi]
    all_goals first | rfl | exact localTemplate_const _
  · simp [boundedTemplate, templateIndex, localTemplate, node, hzero, hone, htwo, hthree,
      StoppingQuery.template]

/-- A framed parameter record followed by one raw macro address. -/
abbrev encTemplateInput := encPair encParameters encNodeData

/-- Framed parameters and address, followed by the selected finite source port. -/
abbrev encSourceInput := encPair encParameters (encPair encNodeData (encFinEnum (Fin 7)))

end Cslib.Circuits.Frontier.FastContraction.StoppingQuery.Product
