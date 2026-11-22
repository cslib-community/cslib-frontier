/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.Product
public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.Bounds

/-!
# Encoding bounds for native product addresses

Canonical product metadata has size linear in the binary endpoint and coefficient lengths,
the unary product height, and the logarithmic arithmetic depths. The bound contains neither
the assignment word nor the number of outer-sum leaves.
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction.StoppingQuery.Product

open Boolean Turing.MultiTapeTM

/-- Converting a semantic product address always clears all unused raw fields. -/
theorem canonical_ofNode (a : StoppingQuery.Node) : Canonical (ofNode a) := by
  cases a with
  | product assignment base level coefficient a =>
    cases a <;> simp [Canonical, ofNode, node, finishData, treeData, portData]
  | sum coefficient a | sumTree coefficient a | value assignment base level coefficient bit
    | entry e => simp [Canonical, ofNode, node, valueData, entryData]

private theorem canonical_valueData (base level coefficient bit : ℕ) :
    Canonical (valueData base level coefficient bit) :=
  canonical_ofNode (.value 0 base level coefficient bit)

private theorem canonical_finishData (base level coefficient : ℕ)
    (a : CarryLookahead.Query.Address) :
    Canonical (finishData base level coefficient a.toData) :=
  canonical_ofNode (.product 0 base level coefficient (.finish a))

private theorem canonical_treeData (base level coefficient : ℕ) (path : List Bool)
    (remaining : ℕ) (carry : Bool) (bit : ℕ) :
    Canonical (treeData base level coefficient path remaining carry bit) :=
  canonical_ofNode (.product 0 base level coefficient (.tree ⟨path, remaining, carry, bit⟩))

private theorem canonical_portData (base level coefficient : ℕ) (path : List Bool)
    (carry : Bool) (bit : ℕ) (port : Fin 7) :
    Canonical (portData base level coefficient path carry bit port) :=
  canonical_ofNode (.product 0 base level coefficient (.port path carry bit port))

private theorem canonical_entryData (vertex coefficient bit : ℕ) :
    Canonical (entryData vertex coefficient bit) :=
  canonical_ofNode (.entry ⟨0, vertex, coefficient, bit⟩)

/-- Native source routing retains canonical metadata, including the finishing adder's
otherwise unused round fields. -/
theorem Canonical.source {p : Parameters} {a b : NodeData} (ha : Canonical a)
    (port : Fin 7) (h : Product.source p a port = some b) : Canonical b := by
  have hfinish (hk : a.kind = 1) (move : Bool) :
      Canonical (finishData a.base a.level a.coefficient
        (CarryLookahead.Query.childData p.precision (SignedValueGame.rounds p.precision)
          a.address move)) := by
    have haddr : a.address.address.toData = a.address := by
      simpa [Canonical, node, ofNode, finishData, hk] using congrArg NodeData.address ha
    rw [← haddr, CarryLookahead.Query.childData_toData p.precision
      (SignedValueGame.rounds p.precision) (fun _ => false)]
    exact canonical_finishData _ _ _ _
  unfold Product.source at h
  dsimp only at h
  split_ifs at h
  all_goals try cases h
  all_goals first
    | exact canonical_entryData _ _ _
    | exact canonical_finishData _ _ _ (.sum _)
    | exact canonical_treeData _ _ _ _ _ _ _
    | exact canonical_portData _ _ _ _ _ _ _
    | exact hfinish ‹a.kind = 1› _
    | obtain ⟨coordinate, _, rfl⟩ := Option.map_eq_some_iff.mp h
      exact canonical_valueData _ _ _ _

/-- A common metadata bound throughout a product of height at most `levels`, whose vertex
interval ends at `limit`. Precision and coefficient indices contribute binary lengths. -/
@[expose] def metadataBound (p : Parameters) (limit levels : ℕ) : ℕ :=
  2 * limit.size + 2 * levels + 2 * (modulus p.scale).length.size +
    4 * SignedValueGame.rounds p.precision + 2 * p.precision.size +
      2 * SignedValueGame.height (3 ^ modulusExp p.scale) p.precision + 40

private theorem length_encNodeData (a : NodeData) :
    (encNodeData a).length = 2 * (a.kind.val + a.base.size + a.level + a.coefficient.size +
      (CarryLookahead.Query.encAddressData a.address).length + a.path.length + a.remaining +
        a.bit.size) + a.port.val + 11 := by
  simp only [encNodeData_apply, encNodeDataFields, length_encPair, encFinEnum_fin_apply,
    encNat_apply, Nat.size_eq_bits_len, encUnary_apply, encBits_apply, encBool_apply,
    List.length_singleton, List.length_replicate]
  omega

private theorem length_ofNode_le (p : Parameters) (limit levels : ℕ) (a : StoppingQuery.Node)
    (ha : ProductWellFormed p.scale p.precision p.vertices 0 limit levels a) :
    (encNodeData (ofNode a)).length ≤ metadataBound p limit levels := by
  have hzero : (CarryLookahead.Query.encAddressData ⟨0, 0, 0⟩).length = 2 := rfl
  cases a with
  | sum coefficient a | sumTree coefficient a => exact ha.elim
  | product assignment base level coefficient a =>
    obtain ⟨_, hbase, hlevel, hcoefficient, ha⟩ := ha
    have hb := Nat.size_le_size ((Nat.le_add_right base _).trans hbase)
    have hc := Nat.size_le_size hcoefficient.le
    cases a with
    | finish a =>
      have haddr : CarryLookahead.Query.WellFormed p.precision
          (SignedValueGame.rounds p.precision) a := ha
      have had := haddr.length_encAddress
      change (CarryLookahead.Query.encAddressData a.toData).length ≤ _ at had
      simp only [ofNode, length_encNodeData, finishData, List.length_nil, Nat.size_zero]
      unfold metadataBound
      omega
    | tree a =>
      obtain ⟨hpath, hbit⟩ := ha
      have hbit' := Nat.size_le_size hbit.le
      simp only [ofNode, length_encNodeData, treeData, hzero]
      unfold metadataBound
      omega
    | port path carry bit port =>
      obtain ⟨hpath, hbit⟩ := ha
      have hbit' := Nat.size_le_size hbit.le
      have hp := port.isLt
      simp only [ofNode, length_encNodeData, portData, hzero]
      unfold metadataBound
      omega
  | value assignment base level coefficient bit =>
    obtain ⟨_, hbase, hlevel, hcoefficient, hbit⟩ := ha
    have hb := Nat.size_le_size ((Nat.le_add_right base _).trans hbase)
    have hc := Nat.size_le_size hcoefficient.le
    have hi := Nat.size_le_size hbit.le
    simp only [ofNode, length_encNodeData, valueData, hzero, List.length_nil]
    unfold metadataBound
    omega
  | entry e =>
    obtain ⟨_, _, hbase, hcoefficient, hbit⟩ := ha
    have hb := Nat.size_le_size hbase.le
    have hc := Nat.size_le_size hcoefficient.le
    have hi := Nat.size_le_size hbit.le
    simp only [ofNode, length_encNodeData, entryData, hzero, List.length_nil]
    unfold metadataBound
    omega

/-- Every canonical bounded macro query fits the same short encoding budget, regardless of
the protected assignment or the product level currently being visited. -/
theorem length_encNodeData_le (p : Parameters) (limit levels : ℕ) (a : NodeData)
    (hc : Canonical a)
    (ha : ProductWellFormed p.scale p.precision p.vertices 0 limit levels (node a)) :
    (encNodeData a).length ≤ metadataBound p limit levels := by
  rw [← hc]
  exact length_ofNode_le p limit levels (node a) ha

end Cslib.Circuits.Frontier.FastContraction.StoppingQuery.Product
