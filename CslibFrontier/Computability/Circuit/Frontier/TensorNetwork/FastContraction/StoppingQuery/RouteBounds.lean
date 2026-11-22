/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.Routing
public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.RawBounds

/-!
# A uniform storage bound for stopping-product traversal

The native position retains its parameters, canonical product metadata and a bounded local
formula. Its encoding therefore fits one fixed bound at every round of a product traversal.
The bound excludes the separately protected assignment word.
-/

noncomputable section

public section

namespace Cslib.Circuits.Frontier.FastContraction.StoppingQuery.ProductRouting

open Boolean LocalValueGame FormulaExpansion Product Turing.MultiTapeTM

/-- A reachable product position has the fixed parameters and remains within its starting
vertex interval and height. Only canonical raw address fields are retained. -/
structure Valid (params : Parameters) (limit levels : ℕ) (p : Position) : Prop where
  /-- Every routing move retains the original runtime circuit parameters. -/
  parameters : p.parameters = params
  /-- Unused raw address fields carry their canonical empty values. -/
  canonical : Canonical p.data
  /-- The interpreted macro stays within the fixed product interval and arithmetic bounds. -/
  bounded : ProductWellFormed params.scale params.precision params.vertices
    0 limit levels (node p.data)

private theorem canonical_child {p : Position} (hp : Canonical p.data) (b : Bool) :
    Canonical (child p b).data := by
  cases hf : BoundedFormula.operation p.formula with
  | inl port =>
    cases hs : Product.source p.parameters p.data port with
    | none => simpa only [child, hf, hs, Option.elim_none] using hp
    | some a =>
      simpa only [child, hf, hs, Option.elim_some, atNode] using hp.source port hs
  | inr op => simpa only [child, hf] using hp

/-- Every Boolean move preserves the short product storage invariant. -/
theorem Valid.next {parameters : Parameters} {limit levels : ℕ} {p : Position}
    (hp : Valid parameters limit levels p) (b : Bool) :
    Valid parameters limit levels (next p b) := by
  have hchild (move : Bool) :
      ProductWellFormed parameters.scale parameters.precision parameters.vertices
        0 limit levels (node (child p move).data) := by
    change ProductWellFormed parameters.scale parameters.precision parameters.vertices
      0 limit levels (address (child p move)).node
    rw [child_address p (fun _ => false), hp.parameters]
    exact hp.bounded.child (a := address p) (edges := 0) (fun _ => false) move
  constructor
  · exact (next_parameters p b).trans hp.parameters
  · unfold ProductRouting.next
    split <;> exact canonical_child hp.canonical _
  · unfold ProductRouting.next
    split <;> exact hchild _

/-- Root preparation starts a valid balanced product, including identity-padded vertices. -/
theorem valid_root (parameters : Parameters) {coefficient bit : ℕ}
    (hcoefficient : coefficient < (modulus parameters.scale).length)
    (hbit : bit < parameters.precision) (claim : Bool) :
    Valid parameters (2 ^ Nat.clog 2 parameters.vertices) (Nat.clog 2 parameters.vertices)
      (root parameters coefficient bit claim) := by
  constructor
  · rfl
  · exact canonical_ofNode (.value 0 0 (Nat.clog 2 parameters.vertices) coefficient bit)
  · simp [root, atNode, node, valueData, ProductWellFormed, hcoefficient, hbit]

/-- The full short word, including parameters, finite local formula and claim framing. -/
@[expose] def metadataBound (parameters : Parameters) (limit levels : ℕ) : ℕ :=
  2 * (encParameters parameters).length + 2 * Product.metadataBound parameters limit levels +
    2 * Nat.card (BoundedFormula 7 12) + 4

/-- Every position visited in a valid product traversal has the same encoding bound. -/
theorem Valid.length_encPosition_le {parameters : Parameters} {limit levels : ℕ} {p : Position}
    (hp : Valid parameters limit levels p) :
    (encPosition p).length ≤ metadataBound parameters limit levels := by
  have hd := length_encNodeData_le parameters limit levels p.data hp.canonical hp.bounded
  have hf := length_encFinite_lt p.formula
  change (encBoundedFormula 7 12 p.formula).length < _ at hf
  simp only [encPosition_apply, encPositionFields, length_encPair, encBool_apply,
    List.length_singleton, hp.parameters]
  unfold metadataBound
  omega

end Cslib.Circuits.Frontier.FastContraction.StoppingQuery.ProductRouting
