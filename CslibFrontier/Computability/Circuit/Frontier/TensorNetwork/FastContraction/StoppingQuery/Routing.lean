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
public import CslibFrontier.Computability.Circuit.Boolean.LocalValueGame.Formula.Bounded

/-!
# Native Boolean gate routing for stopping products

The encoded position contains only circuit parameters, a product macro address, one bounded
local formula and the claimed bit. The assignment is held outside this word. Native updates
follow the existing stopping circuit through arbitrary runtime product heights, using a single
fixed finite program. Entry terminals are answered separately on the protected assignment.
-/

noncomputable section

public section

namespace Cslib.Circuits.Frontier.FastContraction.StoppingQuery.ProductRouting

open Boolean LocalValueGame FormulaExpansion Product
open Turing.MultiTapeTM ComputableInPolyTime

/-- Short mutable storage for one gate claim in a stopping product. -/
structure Position where
  /-- Circuit parameters retained by every routing move. -/
  parameters : Parameters
  /-- Current product macro address, without the assignment. -/
  data : NodeData
  /-- Remaining local Boolean formula at the macro address. -/
  formula : BoundedFormula 7 12
  /-- Proposed value of the current Boolean gate. -/
  claim : Bool
  deriving DecidableEq

/-- Framed binary parameters and macro address, then a framed fixed finite formula code,
followed by the claimed bit. The assignment is absent from this encoding. -/
enc_structure encPosition : Position where
  parameters : encParameters, data : encNodeData,
  formula : (encBoundedFormula 7 12), claim : encBool

/-- The same gate in the established stopping circuit, with assignment supplied by its entry
interpretation rather than by the mutable metadata. -/
@[expose] def address (p : Position) : Address := ⟨node p.data, p.formula.val⟩

/-- Start the bounded local formula for a specified product macro. -/
@[expose] def atNode (parameters : Parameters) (data : NodeData) (claim : Bool) : Position :=
  ⟨parameters, data, boundedTemplate parameters data, claim⟩

/-- The balanced product over all vertices, with multiplicative identity padding. -/
@[expose] def root (parameters : Parameters) (coefficient bit : ℕ) (claim : Bool) : Position :=
  atNode parameters (valueData 0 (Nat.clog 2 parameters.vertices) coefficient bit) claim

/-- Read the gate operation without querying an entry. Entry nodes are terminal placeholders. -/
@[expose] def operation (p : Position) : Op :=
  if p.data.kind = 4 then .const false else
    match BoundedFormula.operation p.formula with
    | .inl port => if (Product.source p.parameters p.data port).isSome then .or else .const false
    | .inr op => op

/-- A terminal has no owner; the claim selects universal versus existential at a binary gate. -/
@[expose] def player (p : Position) : Option Bool :=
  match operation p with
  | .const _ => none
  | .not => some false
  | .and => some p.claim
  | .or => some (!p.claim)

/-- Follow one local formula edge or a computed macro source, retaining the short parameters. -/
@[expose] def child (p : Position) (b : Bool) : Position :=
  match BoundedFormula.operation p.formula with
  | .inl port => (Product.source p.parameters p.data port).elim p
      (fun a => atNode p.parameters a p.claim)
  | .inr _ => { p with formula := BoundedFormula.child p.formula b }

/-- Negation chooses its sole child and flips the claim; other gates keep the selected bit. -/
@[expose] def next (p : Position) (b : Bool) : Position :=
  if operation p = .not then { child p false with claim := !p.claim } else child p b

/-- A native round emits the successor's header and short metadata. -/
@[expose] def step (x : Bool × Position) : Option Bool × Position :=
  let p := next x.2 x.1
  (player p, p)

private theorem inputLabel_address (p : Position) :
    inputLabel (address p) =
      if p.data.kind = 4 then some ⟨0, p.data.base, p.data.coefficient, p.data.bit⟩ else none := by
  rcases p with ⟨parameters, ⟨kind, base, level, coefficient, a, path, remaining, carry, bit, port⟩,
    formula, claim⟩
  fin_cases kind <;> simp [address, Product.node, inputLabel]

private theorem decoder_operation (p : Position) (input : Entry → Bool)
    (hentry : p.data.kind ≠ 4) :
    (decoder p.parameters.scale p.parameters.precision 0 p.parameters.vertices input).op
        (address p) = operation p := by
  change (StoppingQuery.operation p.parameters.scale p.parameters.precision 0
    p.parameters.vertices (address p)).elim (fun e => Op.const (input e)) id = operation p
  rw [StoppingQuery.operation, inputLabel_address, ite_eq_right hentry]
  simp only [Sum.elim_inr, id_eq, operation, ite_eq_right hentry]
  rcases p with ⟨parameters, data, ⟨f, hf⟩, claim⟩
  cases f with
  | gate op args => rfl
  | input i =>
    have hs := source_node parameters data i
    cases h : Product.source parameters data i with
    | none =>
      simp only [h, Option.map_none] at hs
      simp [address, FormulaExpansion.decoder, BoundedFormula.operation, h, ← hs]
    | some a =>
      simp only [h, Option.map_some] at hs
      simp [address, FormulaExpansion.decoder, BoundedFormula.operation, h, ← hs]

private theorem operation_not_iff (p : Position) (input : Entry → Bool) :
    operation p = .not ↔
      (decoder p.parameters.scale p.parameters.precision 0 p.parameters.vertices input).op
        (address p) = .not := by
  by_cases h : p.data.kind = 4
  · simp [operation, h, decoder, StoppingQuery.operation, inputLabel_address]
  · rw [decoder_operation p input h]

@[simp] theorem child_parameters (p : Position) (b : Bool) :
    (child p b).parameters = p.parameters := by
  cases hf : BoundedFormula.operation p.formula with
  | inl port =>
    cases hs : Product.source p.parameters p.data port <;> simp [child, hf, hs, atNode]
  | inr op => simp [child, hf]

@[simp] theorem child_claim (p : Position) (b : Bool) :
    (child p b).claim = p.claim := by
  cases hf : BoundedFormula.operation p.formula with
  | inl port =>
    cases hs : Product.source p.parameters p.data port <;> simp [child, hf, hs, atNode]
  | inr op => simp [child, hf]

/-- Every local move retains all circuit parameters. -/
@[simp] theorem next_parameters (p : Position) (b : Bool) :
    (next p b).parameters = p.parameters := by
  unfold next
  split <;> simp

/-- The encoded child is exactly the child in the existing stopping circuit. -/
theorem child_address (p : Position) (input : Entry → Bool) (b : Bool) :
    address (child p b) =
      (decoder p.parameters.scale p.parameters.precision 0 p.parameters.vertices input).child
        (address p) b := by
  rcases p with ⟨parameters, data, ⟨f, hf⟩, claim⟩
  cases f with
  | gate op args => cases op <;> rfl
  | input i =>
    have hs := source_node parameters data i
    cases h : Product.source parameters data i with
    | none =>
      simp only [h, Option.map_none] at hs
      simp [child, BoundedFormula.operation, h, address, decoder,
        FormulaExpansion.decoder, ← hs]
    | some a =>
      simp only [h, Option.map_some] at hs
      simp [child, BoundedFormula.operation, h, address, decoder,
        FormulaExpansion.decoder, atNode, FormulaExpansion.root, ← hs, boundedTemplate_val]

/-- Both the selected gate and the changed claim agree with the circuit's Boolean value game. -/
theorem next_claim (p : Position) (input : Entry → Bool) (b : Bool) :
    (⟨address (next p b), (next p b).claim⟩ : Claim Address) =
      LocalValueGame.next
        (decoder p.parameters.scale p.parameters.precision 0 p.parameters.vertices input)
        ⟨address p, p.claim⟩ b := by
  cases ho : (decoder p.parameters.scale p.parameters.precision 0 p.parameters.vertices input).op
      (address p) <;>
    simp only [LocalValueGame.next, ho, next, operation_not_iff p input, reduceCtorEq,
      ↓reduceIte, child_claim, child_parameters, Claim.mk.injEq, child_address p input, and_true]
  change address (child p false) = _
  exact child_address p input false

/-- A recorded owner means the circuit is at a nonconstant gate for every entry interpretation. -/
theorem nonterminal_of_player (p : Position) (input : Entry → Bool) {owner : Bool}
    (hp : player p = some owner) :
    ∀ b, (decoder p.parameters.scale p.parameters.precision 0 p.parameters.vertices input).op
      (address p) ≠ .const b := by
  have hentry : p.data.kind ≠ 4 := by
    intro h
    simp [player, operation, h] at hp
  rw [decoder_operation p input hentry]
  cases ho : operation p <;> simp_all [player]

private theorem player_eq (p : Position) (input : Entry → Bool) {owner : Bool}
    (hp : player p = some owner) :
    LocalValueGame.player
      (decoder p.parameters.scale p.parameters.precision 0 p.parameters.vertices input)
      ⟨address p, p.claim⟩ = owner := by
  have hentry : p.data.kind ≠ 4 := by
    intro h
    simp [player, operation, h] at hp
  simp only [LocalValueGame.player, decoder_operation p input hentry]
  cases ho : operation p <;> simp_all [player]

/-- A terminal reads either its labelled entry bit or its Boolean constant. The entry
interpretation is needed only in the first case. -/
@[expose] def terminalValue (input : Entry → Bool) (p : Position) : Bool :=
  if p.data.kind = 4 then input ⟨0, p.data.base, p.data.coefficient, p.data.bit⟩ else
    match operation p with
    | .const b => b
    | _ => false

/-- The terminal response agrees with the established circuit semantics. -/
theorem terminal_value (p : Position)
    (entry : ℕ → ℕ → GaloisRingArith.Ring p.parameters.precision (modulus p.parameters.scale))
    (hp : player p = none) :
    StoppingQuery.value p.parameters.scale p.parameters.precision 0 p.parameters.vertices entry
        (address p) =
      terminalValue (entryBit p.parameters.scale p.parameters.precision entry) p := by
  rw [value_eq_eval]
  by_cases hentry : p.data.kind = 4
  · simp [Decoder.eval, decoder, StoppingQuery.operation, inputLabel_address, hentry,
      terminalValue]
  · simp only [Decoder.eval, decoder_operation p _ hentry, terminalValue, ite_eq_right hentry]
    cases ho : operation p <;> simp_all [player]

/-- Every native update at a nonterminal lowers the established stopping-circuit rank. -/
theorem rank_next_lt (p : Position) {owner : Bool} (hp : player p = some owner) (b : Bool) :
    StoppingQuery.rank p.parameters.scale p.parameters.precision 0 p.parameters.vertices
        (address (next p b)) <
      StoppingQuery.rank p.parameters.scale p.parameters.precision 0 p.parameters.vertices
        (address p) := by
  have h := LocalValueGame.rank_next_lt
    (StoppingQuery.descends p.parameters.scale p.parameters.precision 0 p.parameters.vertices
      (fun _ => false)) ⟨address p, p.claim⟩
    (nonterminal_of_player p (fun _ => false) hp) b
  rw [← next_claim p (fun _ => false) b] at h
  exact h

/-- A native routing choice has exactly the Boolean game equation for the actual ring entries. -/
theorem value_iff_next (p : Position)
    (entry : ℕ → ℕ → GaloisRingArith.Ring p.parameters.precision (modulus p.parameters.scale))
    {owner : Bool} (hp : player p = some owner) :
    StoppingQuery.value p.parameters.scale p.parameters.precision 0 p.parameters.vertices entry
        (address p) = p.claim ↔
      if owner then
        ∀ b, StoppingQuery.value p.parameters.scale p.parameters.precision 0 p.parameters.vertices
          entry (address (next p b)) = (next p b).claim
      else
        ∃ b, StoppingQuery.value p.parameters.scale p.parameters.precision 0 p.parameters.vertices
          entry (address (next p b)) = (next p b).claim := by
  let input := entryBit p.parameters.scale p.parameters.precision entry
  have h := LocalValueGame.value_eq_iff_next
    (StoppingQuery.value p.parameters.scale p.parameters.precision 0 p.parameters.vertices entry)
    ⟨address p, p.claim⟩
    (value_eq_eval p.parameters.scale p.parameters.precision 0 p.parameters.vertices entry
      (address p)) (nonterminal_of_player p input hp)
  rw [player_eq p input hp] at h
  simpa only [← next_claim p (entryBit p.parameters.scale p.parameters.precision entry)] using h

/-- Root preparation denotes the existing balanced product block, including empty products. -/
theorem root_address (parameters : Parameters) (coefficient bit : ℕ) (claim : Bool) :
    address (root parameters coefficient bit claim) =
      FormulaExpansion.root (template parameters.scale parameters.precision 0 parameters.vertices)
        (.value 0 0 (Nat.clog 2 parameters.vertices) coefficient bit) := by
  simp [root, atNode, address, boundedTemplate_val, Product.node, valueData,
    FormulaExpansion.root]

end Cslib.Circuits.Frontier.FastContraction.StoppingQuery.ProductRouting
