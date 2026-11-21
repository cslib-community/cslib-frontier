/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Mathlib.Logic.Equiv.Fin.Basic
import CslibFrontier.Foundations.Data.Fin.Prod

/-!
# Flat IDs for subdivision edge requests

An original vertex label and a chain position are packed in row-major order, with
`bound + 1` slots per label. A scan can start each source at offset zero and use the
same numbering for all of its edge requests, including requests at unused slots.

`decodeFlatQuery` reconstructs the existing adjacency callback request from two binary
IDs and the chain bound. It retains the supplied context. Its agreement theorem applies
to IDs in the rectangular carrier, which the caller supplies through `Fin` coordinates.
The native certificates cover request preparation and entry to the existing same-input
subdivision callback.
-/

public section

namespace Turing.QueryMachine.Subdivision

open Cslib.LayeredDigraph.Subdivision
open MultiTapeTM ComputableInSpace

/-- Row-major numbering of all subdivision slots, including unused positions. -/
abbrev flatIndex (n bound : ℕ) : Vertex (Fin n) bound ≃ Fin (n * (bound + 1)) :=
  (equivProd (Fin n) bound).trans finProdFinEquiv

/-- Flat ID of the offset-zero root for a binary original label and chain bound. -/
@[expose] def rootID (label bound : ℕ) : ℕ := (bound + 1) * label

/-- The scalar root ID agrees with the root in the subdivision's row-major numbering. -/
theorem rootID_eq_flatIndex {n : ℕ} (label : Fin n) (bound : ℕ) :
    rootID label.val bound = (flatIndex n bound (root bound label)).val := by
  simp [rootID, flatIndex]

/-- Computing a root ID takes linear space in the binary label and chain bound. -/
theorem rootID_inSpace :
    ComputableInSpace (fun p : ℕ × ℕ => rootID p.1 p.2) (encPair encNat encNat) encNat
      (fun p => (encPair encNat encNat p).length) :=
  (budget_natMul (budget_natSucc (snd encNat encNat)) (fst encNat encNat)).of_enc_eq
    (fun _ => rfl)

/-- An edge request carrying two flat scan IDs and the subdivision chain bound. -/
structure FlatQuery (Context : Type) where
  /-- Parameters passed through to the edge callback. -/
  context : Context
  /-- Uniform upper bound on chain length. -/
  bound : ℕ
  /-- Row-major source ID. -/
  fromID : ℕ
  /-- Row-major target ID. -/
  toID : ℕ

variable {Context : Type}

/-- Frame the callback context, binary chain bound and binary source ID in that order,
then append the binary target ID. -/
enc_structure encFlatQuery (encContext : Context ↪ List Bool) : FlatQuery Context where
  context : encContext, bound : encNat, fromID : encNat, toID : encNat

/-- Decode the original labels and chain offsets for an ordinary subdivision edge request. -/
@[expose] def decodeFlatQuery (q : FlatQuery Context) : Query Context :=
  let slots := q.bound + 1
  ⟨q.context, q.fromID / slots, q.toID / slots, q.fromID % slots, q.toID % slots⟩

/-- Decoding indexed vertices recovers their exact original labels and offsets. -/
theorem decodeFlatQuery_flatIndex {n : ℕ} (ctx : Context) (bound : ℕ)
    (a b : Vertex (Fin n) bound) :
    decodeFlatQuery ⟨ctx, bound, (flatIndex n bound a).val, (flatIndex n bound b).val⟩ =
      ⟨ctx, a.vertex.val, b.vertex.val, a.offset.val, b.offset.val⟩ := by
  simp only [decodeFlatQuery, flatIndex, Equiv.trans_apply, finProdFinEquiv_val_div,
    finProdFinEquiv_val_mod, equivProd_apply]

/-- Decoding fits in linear space in the retained context and binary request. -/
theorem decodeFlatQuery_inSpace (encContext : Context ↪ List Bool) :
    ComputableInSpace decodeFlatQuery (encFlatQuery encContext) (encQuery encContext)
      (fun q => (encFlatQuery encContext q).length) := by
  have hid := of_inO (ComputableInDegree.id' (enc := encFlatQuery encContext)).inO_one
  have hslots := budget_natSucc (encFlatQuery_bound_budget encContext hid)
  have ha := encFlatQuery_fromID_budget encContext hid
  have hb := encFlatQuery_toID_budget encContext hid
  exact (encQuery_mk_budget encContext (encFlatQuery_context_budget encContext hid)
    (budget_natDiv ha hslots) (budget_natDiv hb hslots) (budget_natMod ha hslots)
    (budget_natMod hb hslots)).of_enc_eq (fun _ => rfl)

/-- Decode the flat request and enter the subdivision callback in its pending caller state. -/
@[expose] def flatCallbackStart {τ : Type} (q : FlatQuery Context) :
    (Query Context ⊕ Bool) ⊕ ((Query Context ⊕ Bool) × τ) :=
  .inl (.inl (decodeFlatQuery q))

/-- Entering the callback takes linear workspace in the encoded flat request. -/
theorem flatCallbackStart_inSpace {τ : Type} (encContext : Context ↪ List Bool)
    (encT : τ ↪ List Bool) :
    ComputableInSpace flatCallbackStart (encFlatQuery encContext) (encCallback encContext encT)
      (fun q => (encFlatQuery encContext q).length) := by
  let encC := encCaller encContext
  have hcaller := of_inO (ComputableInO.inl (encQuery encContext) encBool)
  have hcall := of_inO (ComputableInO.inl encC (encPair encC encT))
  have h := budget_comp_linear hcall
    (budget_comp_linear hcaller (decodeFlatQuery_inSpace encContext))
  exact h

end Turing.QueryMachine.Subdivision
