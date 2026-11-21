/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.LayeredCallback
public import CslibFrontier.Computability.Complexity.Problems.STCON.LayeredParameters
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision
public import Mathlib.Logic.Equiv.Fin.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Foundations.Data.Fin.Prod

/-!
# Original adjacency requests for subdivided STCON graphs

The subdivision callback receives flat labels of two original vertices and their chain
offsets. Only the labels matter for original adjacency. Dividing each label by the
retained graph width gives its layer, and the remainder gives its column. The original
adjacency callee reads the symbol directly from the input.

## Main results

* `Cslib.Complexity.STCON.subdivisionLayeredCall_eq`: agreement with requests built from
  the original bounded layered vertices.
* `Cslib.Complexity.STCON.subdivisionLayeredCall_inSpace`: native workspace linear in the
  subdivision request, given a native projection of the graph parameters.
-/

public section

namespace Cslib.Complexity.STCON

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace

/-- Prepare the pending call to the original adjacency machine using row-major vertex
labels. The scan may retain additional data alongside the layered graph parameters. -/
@[expose] def subdivisionLayeredCall {Context : Type} (graph : Context → LayeredParameters)
    (q : QueryMachine.Subdivision.Query Context) : LayeredQuery ⊕ Bool :=
  let p := graph q.context
  .inl ⟨p.radix, p.inputLength, q.fromLabel / p.width, q.fromLabel % p.width,
    q.toLabel / p.width, q.toLabel % p.width, none⟩

/-- The flat labels of bounded layered vertices yield the same pending call as their
original coordinates, regardless of the subdivision offsets. -/
theorem subdivisionLayeredCall_eq {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool)
    (a b : LayeredGraphVertex (configurationInstance ntm c w)) (fromOffset toOffset : ℕ)
    {Context : Type} (graph : Context → LayeredParameters) (ctx : Context)
    (hgraph : graph ctx = layeredParameters ntm c w.length) :
    subdivisionLayeredCall graph
      ⟨ctx,
        (finProdFinEquiv (layeredCoordinates _ a)).val,
        (finProdFinEquiv (layeredCoordinates _ b)).val, fromOffset, toOffset⟩ =
      .inl (layeredQueryRequest ntm c w a b) := by
  simp only [subdivisionLayeredCall, layeredQueryRequest, hgraph]
  congr 2
  · exact finProdFinEquiv_val_div _
  · exact finProdFinEquiv_val_mod _
  · exact finProdFinEquiv_val_div _
  · exact finProdFinEquiv_val_mod _

/-- Preparing the original adjacency call uses native workspace linear in the encoded
subdivision request when the graph parameters can be projected in linear workspace. -/
theorem subdivisionLayeredCall_inSpace {Context : Type} (encContext : Context ↪ List Bool)
    (graph : Context → LayeredParameters)
    (hgraph : ComputableInSpace graph encContext encLayeredParameters
      (fun ctx => (encContext ctx).length)) :
    ComputableInSpace (subdivisionLayeredCall graph) (QueryMachine.Subdivision.encQuery encContext)
      encLayeredCallback (fun q => (QueryMachine.Subdivision.encQuery encContext q).length) := by
  let encQ := QueryMachine.Subdivision.encQuery encContext
  have hid := budget_id (enc := encQ) (S := fun q => (encQ q).length) (.refl _)
  have hp := budget_comp_linear hgraph
    (QueryMachine.Subdivision.encQuery_context_budget encContext hid)
  have hw := encLayeredParameters_width_budget hp
  have hf := QueryMachine.Subdivision.encQuery_fromLabel_budget encContext hid
  have ht := QueryMachine.Subdivision.encQuery_toLabel_budget encContext hid
  have hq := encLayeredQuery_mk_budget (encLayeredParameters_radix_budget hp)
    (encLayeredParameters_inputLength_budget hp) (budget_natDiv hf hw) (budget_natMod hf hw)
    (budget_natDiv ht hw) (budget_natMod ht hw) (budget_const none (.refl _))
  have hinl := of_inO (ComputableInO.inl encLayeredQuery encBool)
  have hcall := budget_comp_linear hinl hq
  exact hcall

end Cslib.Complexity.STCON
