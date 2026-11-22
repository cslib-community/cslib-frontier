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
CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.ProductTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-!
# Native computation of stopping-product gate moves

Every Boolean update is certified on its short position encoding. The computation includes
formula selection, local input routing and all arithmetic on macro addresses. No assignment
word or tensor value is read by these routines.
-/

noncomputable section

public section

namespace Cslib.Circuits.Frontier.FastContraction.StoppingQuery.ProductRouting

open Boolean LocalValueGame FormulaExpansion Product
open Turing.MultiTapeTM ComputableInPolyTime

private theorem formulaOperation_polyTime :
    ComputableInPolyTime (fun p : Position => BoundedFormula.operation p.formula) encPosition
      (encSum (encFinEnum (Fin 7)) encOp) :=
  (of_finite (encIn := encBoundedFormula 7 12)
    (encOut := encSum (encFinEnum (Fin 7)) encOp) BoundedFormula.operation).comp
      (by fun_prop)

/-- Classifying a gate uses only finite local control and the certified macro source router. -/
theorem operation_polyTime : ComputableInPolyTime operation encPosition encOp := by
  have hp := fst encPosition (encFinEnum (Fin 7))
  have hs : ComputableInPolyTime
      (fun x : Position × Fin 7 => Product.source x.1.parameters x.1.data x.2)
      (encPair encPosition (encFinEnum (Fin 7))) (encOption encNodeData) :=
    source_polyTime.comp ((encPosition_parameters_polyTime hp).prod
      ((encPosition_data_polyTime hp).prod (snd encPosition (encFinEnum (Fin 7)))))
  have hfinite : ComputableInPolyTime
      (fun b : Bool => if b then Op.or else .const false) encBool encOp := of_finite _
  have hport : ComputableInPolyTime
      (fun x : Position × Fin 7 => if (Product.source x.1.parameters x.1.data x.2).isSome
        then Op.or else .const false)
      (encPair encPosition (encFinEnum (Fin 7))) encOp :=
    hfinite.comp hs.optionIsSome
  have hlocal : ComputableInPolyTime (fun p : Position =>
      match BoundedFormula.operation p.formula with
      | .inl port => if (Product.source p.parameters p.data port).isSome
          then Op.or else .const false
      | .inr op => op) encPosition encOp := by
    apply ComputableInPolyTime.finite_cases (output := encOp)
      (branch := fun (op : Fin 7 ⊕ Op) (p : Position) => match op with
      | .inl port => if (Product.source p.parameters p.data port).isSome
          then Op.or else .const false
      | .inr op => op) formulaOperation_polyTime
    intro op
    cases op with
    | inl port => exact hport.comp (id'.pair (const (encOut := encFinEnum (Fin 7)) port))
    | inr op => exact const op
  exact ite_decide
    (decide_eq' (encNodeData_kind_polyTime (encPosition_data_polyTime id')) (const 4))
    (const (Op.const false)) hlocal

/-- Header preparation is native polynomial time in the short encoded position. -/
theorem player_polyTime :
    ComputableInPolyTime player encPosition (encOption encBool) := by
  have h := of_finite (encIn := encPair encOp encBool) (encOut := encOption encBool)
    (fun x : Op × Bool => match x.1 with
      | .const _ => none | .not => some false | .and => some x.2 | .or => some (!x.2))
  exact h.comp (operation_polyTime.pair (by fun_prop))

/-- Native construction of a local root computes its actual bounded template. -/
theorem atNode_polyTime {α : Type} {enc : α ↪ List Bool}
    {parameters : α → Parameters} {data : α → NodeData} {claim : α → Bool}
    (hp : ComputableInPolyTime parameters enc encParameters)
    (hd : ComputableInPolyTime data enc encNodeData)
    (hc : ComputableInPolyTime claim enc encBool) :
    ComputableInPolyTime (fun x => atNode (parameters x) (data x) (claim x))
      enc encPosition := by
  exact encPosition_mk_polyTime hp hd (boundedTemplate_polyTime.comp (hp.pair hd)) hc

/-- The finite formula move and native source lookup implement every selected child. -/
theorem child_polyTime :
    ComputableInPolyTime (fun x : Bool × Position => child x.2 x.1)
      (encPair encBool encPosition) encPosition := by
  have hf : ComputableInPolyTime
      (fun x : BoundedFormula 7 12 × Bool => BoundedFormula.child x.1 x.2)
      (encPair (encBoundedFormula 7 12) encBool) (encBoundedFormula 7 12) := of_finite _
  have htag := formulaOperation_polyTime.comp (snd encBool encPosition)
  unfold child
  apply ComputableInPolyTime.finite_cases (output := encPosition)
    (branch := fun (op : Fin 7 ⊕ Op) (x : Bool × Position) =>
    match op with
    | .inl port => (Product.source x.2.parameters x.2.data port).elim x.2
        (fun a => atNode x.2.parameters a x.2.claim)
    | .inr _ => { x.2 with formula := BoundedFormula.child x.2.formula x.1 }) htag
  intro op
  cases op with
  | inl port =>
    have hs : ComputableInPolyTime
        (fun x : Bool × Position => Product.source x.2.parameters x.2.data port)
        (encPair encBool encPosition) (encOption encNodeData) :=
      source_polyTime.comp ((encPosition_parameters_polyTime (snd encBool encPosition)).prod
        ((encPosition_data_polyTime (snd encBool encPosition)).prod (const port)))
    apply hs.optionElimWithInput (snd encBool encPosition)
    exact atNode_polyTime (by fun_prop) (by fun_prop) (by fun_prop)
  | inr op =>
    have hp := snd encBool encPosition
    exact encPosition_mk_polyTime (encPosition_parameters_polyTime hp)
      (encPosition_data_polyTime hp)
      (hf.comp ((encPosition_formula_polyTime hp).pair (fst encBool encPosition)))
      (encPosition_claim_polyTime hp)

/-- The complete Boolean update has a fixed native polynomial certificate. -/
theorem next_polyTime :
    ComputableInPolyTime (fun x : Bool × Position => next x.2 x.1)
      (encPair encBool encPosition) encPosition := by
  have hargs : ComputableInPolyTime (fun x : Bool × Position => (false, x.2))
      (encPair encBool encPosition) (encPair encBool encPosition) :=
    (const false).prod (snd encBool encPosition)
  have hconst := child_polyTime.comp hargs
  have ho := operation_polyTime.comp
    (snd encBool encPosition)
  have hflip := encPosition_mk_polyTime
    (encPosition_parameters_polyTime hconst) (encPosition_data_polyTime hconst)
    (encPosition_formula_polyTime hconst)
    (bool_not.comp (encPosition_claim_polyTime (snd encBool encPosition)))
  exact ite_decide (decide_eq' ho (const Op.not)) hflip child_polyTime

/-- The same finite native round handles every product level and every formula gate. -/
theorem step_polyTime :
    ComputableInPolyTime step (encPair encBool encPosition)
      (encPair (encOption encBool) encPosition) :=
  (player_polyTime.comp next_polyTime).pair next_polyTime

/-- Root preparation computes the logarithmic product height from the binary vertex count. -/
theorem root_polyTime {α : Type} {enc : α ↪ List Bool}
    {parameters : α → Parameters} {coefficient bit : α → ℕ} {claim : α → Bool}
    (hp : ComputableInPolyTime parameters enc encParameters)
    (hc : ComputableInPolyTime coefficient enc encNat)
    (hb : ComputableInPolyTime bit enc encNat)
    (hv : ComputableInPolyTime claim enc encBool) :
    ComputableInPolyTime (fun x => root (parameters x) (coefficient x) (bit x) (claim x))
      enc encPosition := by
  unfold root
  apply atNode_polyTime hp ?_ hv
  apply valueData_polyTime (const 0) ?_ hc hb
  exact binary_clog_two.comp (by fun_prop)

end Cslib.Circuits.Frontier.FastContraction.StoppingQuery.ProductRouting
